package pair

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"strings"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/bsv-blockchain/go-sdk/chainhash"
	ec "github.com/bsv-blockchain/go-sdk/primitives/ec"
	"github.com/bsv-blockchain/go-sdk/script"
	"github.com/bsv-blockchain/go-sdk/script/interpreter"
	"github.com/bsv-blockchain/go-sdk/transaction"
	sighash "github.com/bsv-blockchain/go-sdk/transaction/sighash"
	"github.com/icellan/runar/compilers/go/compiler"
	runar "github.com/icellan/runar/packages/runar-go"
)

// Adversarial tests for the pair pool and its vault. Everything runs through
// the go-sdk interpreter on a real transaction, both contract inputs executed
// with their real BIP-143 preimages. advRun is a more flexible sibling of
// fixture.run (pair_test.go): other sighash types for the pool's preimage and
// for its signer's signature, a signature made over another transaction, raw
// signature / selector / change / vaultCode pushes, extra pushes, another
// _codePart,
// plain P2PKH inputs signed and executed, version and locktime.
//
// Every run through advRun (and so every run in pair_property_test.go)
// enforces the stranding invariant: an accepted pool input always has its
// vault, output 1 of its own transaction, as input 1.

// --- runner ---

type advOpts struct {
	preFlag   sighash.Flag // the pool's txPreimage type; 0 = ALL|FORKID
	preBIP143 bool         // a non-FORKID preFlag still laid out as BIP-143 (default: the legacy serialisation)
	sigFlag   sighash.Flag // the pool signer's signature type; 0 = ALL|FORKID
	sigSpend  *spend       // the signature is made over the transaction this spend describes
	rawSig    []byte       // a raw push in place of the signature
	sigTweak  func([]byte) []byte
	method    []byte   // a raw push in place of the method index
	leading   [][]byte // pushes below _codePart
	trailing  [][]byte // pushes after the method index
	codePart  []byte   // replaces _codePart (nil: f.code)
	chPkh     []byte   // a raw push in place of _changePKH
	chAmt     []byte   // a raw push in place of _changeAmount
	rawPrev   []byte   // a raw push in place of the pool's allPrevouts push
	rawCode   []byte   // a raw push in place of the _codePart push
	rawVault  []byte   // a raw push in place of the vaultCode push (Swap, Rescind)
	noVault   bool     // omit the vaultCode push (Swap, Rescind)
	noPre     bool     // omit the pool's preimage push

	noChronicle bool                   // run the interpreter without the Chronicle upgrade
	p2pkh       map[int]*ec.PrivateKey // plain P2PKH inputs: signed (ALL|FORKID) and executed
	version     uint32
	lockTime    uint32
}

func advFlag(f sighash.Flag) sighash.Flag {
	if f == 0 {
		return sighash.AllForkID
	}
	return f
}

func advTx(s spend, o advOpts) *transaction.Transaction {
	tx := transaction.NewTransaction()
	if o.version != 0 {
		tx.Version = o.version
	}
	tx.LockTime = o.lockTime
	for _, i := range s.ins {
		h, _ := chainhash.NewHash(bytes.Repeat([]byte{i.txid}, 32))
		tx.AddInput(&transaction.TransactionInput{SourceTXID: h, SourceTxOutIndex: i.vout, SequenceNumber: 0xffffffff})
	}
	for _, x := range s.outs {
		tx.AddOutput(&transaction.TransactionOutput{Satoshis: uint64(x.sats), LockingScript: script.NewFromBytes(x.script)})
	}
	return tx
}

// advPreimage is input idx's sighash preimage under flag, scriptCode sc.
func advPreimage(t testing.TB, tx *transaction.Transaction, idx int, sats int64, sc []byte, flag sighash.Flag, bip143 bool) []byte {
	t.Helper()
	cp := tx.ShallowClone()
	cp.Inputs[idx].SetSourceTxOutput(&transaction.TransactionOutput{Satoshis: uint64(sats), LockingScript: script.NewFromBytes(sc)})
	var pre []byte
	var err error
	if flag&sighash.ForkID != 0 || bip143 {
		pre, err = cp.CalcInputPreimage(uint32(idx), flag)
	} else {
		pre, err = cp.CalcInputPreimageLegacy(uint32(idx), flag)
	}
	if err != nil {
		t.Fatal(err)
	}
	return pre
}

func advHash(pre []byte) []byte {
	h := sha256.Sum256(pre)
	d := sha256.Sum256(h[:])
	return d[:]
}

func advExec(tx *transaction.Transaction, idx int, i in, chronicle bool) error {
	opts := []interpreter.ExecutionOptionFunc{
		interpreter.WithTx(tx, idx, &transaction.TransactionOutput{Satoshis: uint64(i.sats), LockingScript: script.NewFromBytes(i.lock)}),
		interpreter.WithForkID(),
		interpreter.WithAfterGenesis(),
	}
	if chronicle {
		opts = append(opts, interpreter.WithAfterChronicle())
	}
	return interpreter.NewEngine().Execute(opts...)
}

// advAccepted counts accepted pool inputs the stranding invariant was checked on.
var advAccepted atomic.Int64

// advRunTx runs s like fixture.run, with o's deviations, and returns the
// transaction too.
func advRunTx(t testing.TB, f *fixture, s spend, o advOpts) (result, *transaction.Transaction) {
	t.Helper()
	tx := advTx(s, o)
	var real []byte
	for _, i := range s.ins {
		real = append(real, outpoint(i)...)
	}
	chron := !o.noChronicle
	for idx, k := range o.p2pkh {
		i := s.ins[idx]
		sig, err := k.Sign(advHash(advPreimage(t, tx, idx, i.sats, i.lock, sighash.AllForkID, false)))
		if err != nil {
			t.Fatal(err)
		}
		u := append(pushData(append(sig.Serialize(), 0x41)), pushData(k.PubKey().Compressed())...)
		tx.Inputs[idx].UnlockingScript = script.NewFromBytes(u)
	}

	var r result
	if s.poolIdx >= 0 {
		pi := s.poolIdx
		pin := s.ins[pi]
		pre := advPreimage(t, tx, pi, pin.sats, afterSeparator(pin.lock), advFlag(o.preFlag), o.preBIP143)
		sigPush := o.rawSig
		if sigPush == nil {
			sigTx, sigIn := tx, pin
			if o.sigSpend != nil {
				sigTx, sigIn = advTx(*o.sigSpend, o), o.sigSpend.ins[pi]
			}
			sf := advFlag(o.sigFlag)
			if o.sigFlag == 0 && s.sigFlag != 0 {
				sf = s.sigFlag
			}
			sig, err := s.signer.Sign(advHash(advPreimage(t, sigTx, pi, sigIn.sats, afterSeparator(sigIn.lock), sf, false)))
			if err != nil {
				t.Fatal(err)
			}
			b := append(sig.Serialize(), byte(sf))
			if o.sigTweak != nil {
				b = o.sigTweak(b)
			}
			sigPush = pushData(b)
		}
		var u []byte
		for _, l := range o.leading {
			u = append(u, l...)
		}
		code := f.code
		if o.codePart != nil {
			code = o.codePart
		}
		if o.rawCode != nil {
			u = append(u, o.rawCode...)
		} else {
			u = append(u, pushData(code)...)
		}
		u = append(u, sigPush...)
		for _, a := range s.args {
			u = append(u, a...)
		}
		switch {
		case o.rawPrev != nil:
			u = append(u, o.rawPrev...)
		case s.prevouts != nil:
			u = append(u, pushData(s.prevouts)...)
		default:
			u = append(u, pushData(real)...)
		}
		if s.method != methodClose {
			switch {
			case o.noVault:
			case o.rawVault != nil:
				u = append(u, o.rawVault...)
			case s.vaultArg != nil:
				u = append(u, pushData(s.vaultArg)...)
			default:
				u = append(u, pushData(f.vault)...)
			}
			cp, ca := make([]byte, 20), int64(0)
			if s.change != nil {
				cp, ca = s.change.script, s.change.sats
			}
			if o.chPkh != nil {
				u = append(u, o.chPkh...)
			} else {
				u = append(u, pushData(cp)...)
			}
			if o.chAmt != nil {
				u = append(u, o.chAmt...)
			} else {
				u = append(u, pushNum(ca)...)
			}
		}
		if !o.noPre {
			u = append(u, pushData(pre)...)
		}
		if o.method != nil {
			u = append(u, o.method...)
		} else {
			u = append(u, pushNum(int64(s.method))...)
		}
		for _, tr := range o.trailing {
			u = append(u, tr...)
		}
		tx.Inputs[pi].UnlockingScript = script.NewFromBytes(u)
	}
	if s.vaultIdx >= 0 {
		vin := s.ins[s.vaultIdx]
		flag := s.vaultSighash
		if flag == 0 {
			flag = sighash.AllForkID
		}
		prevouts := s.vaultPrevouts
		if prevouts == nil {
			prevouts = real
		}
		vpre := advPreimage(t, tx, s.vaultIdx, vin.sats, afterSeparator(vin.lock), flag, false)
		if s.forgeVaultPre != nil {
			vpre = s.forgeVaultPre(vpre)
		}
		u := pushData(prevouts)
		u = append(u, pushData(vpre)...)
		tx.Inputs[s.vaultIdx].UnlockingScript = script.NewFromBytes(u)
	}
	for idx := range o.p2pkh {
		if err := advExec(tx, idx, s.ins[idx], chron); err != nil {
			t.Fatalf("harness: plain P2PKH input %d rejected: %v", idx, err)
		}
	}
	if s.poolIdx >= 0 {
		r.pool = advExec(tx, s.poolIdx, s.ins[s.poolIdx], chron)
	}
	if s.vaultIdx >= 0 {
		r.vault = advExec(tx, s.vaultIdx, s.ins[s.vaultIdx], chron)
	}
	advStrandingCheck(t, s, r)
	return r, tx
}

func advRun(t testing.TB, f *fixture, s spend, o advOpts) result {
	t.Helper()
	r, _ := advRunTx(t, f, s, o)
	return r
}

// advH is fixture.run's honest path through advRun (the stranding check included).
func advH(t testing.TB, f *fixture, s spend) result {
	t.Helper()
	return advRun(t, f, s, advOpts{})
}

// advStrandingCheck: an accepted pool input is input 0, output 0 of its
// transaction, and input 1 is output 1 of that same transaction; an accepted
// vault input is input 1 with input 0 at vout 0 of its own transaction.
func advStrandingCheck(t testing.TB, s spend, r result) {
	t.Helper()
	if s.poolIdx >= 0 && r.pool == nil {
		advAccepted.Add(1)
		p := s.ins[s.poolIdx]
		if s.poolIdx != 0 || len(s.ins) < 2 || p.vout != 0 || s.ins[1].txid != p.txid || s.ins[1].vout != 1 {
			t.Errorf("STRANDING: pool input %d (%x:%d) accepted without its vault as input 1 (inputs %+v)", s.poolIdx, p.txid, p.vout, s.ins)
		}
	}
	if s.vaultIdx >= 0 && r.vault == nil {
		v := s.ins[s.vaultIdx]
		if s.vaultIdx != 1 || v.vout != 1 || s.ins[0].txid != v.txid || s.ins[0].vout != 0 {
			t.Errorf("VAULT RULE: vault input %d (%x:%d) accepted outside its rule (inputs %+v)", s.vaultIdx, v.txid, v.vout, s.ins)
		}
	}
}

func advTxHex(tx *transaction.Transaction) string { return hex.EncodeToString(tx.Bytes()) }

// --- toolchain ---

type advSlot struct {
	ParamIndex   int `json:"paramIndex"`
	ByteOffset   int `json:"byteOffset"`
	CodeSepIndex int `json:"codeSepIndex"`
}

type advArtifact struct {
	Script            string    `json:"script"`
	ASM               string    `json:"asm"`
	ConstructorSlots  []advSlot `json:"constructorSlots"`
	CodeSepIndexSlots []advSlot `json:"codeSepIndexSlots"`
	CodePartLenSlots  []advSlot `json:"codePartLenSlots"`

	head     bool // the PairPool artifact JSON has a codePartLenSlots key
	template []byte
	sa       runar.RunarArtifact
}

var (
	advArtOnce sync.Once
	advArtVal  *advArtifact
	advArtErr  error
)

// advArt is the PairPool artifact as JSON. HEAD is detected from this
// artifact only (the Vault artifact has no codePartLenSlots key on either).
func advArt(t testing.TB) *advArtifact {
	t.Helper()
	advArtOnce.Do(func() {
		art, err := compiler.CompileFromSource("PairPool.runar.go")
		if err != nil {
			advArtErr = err
			return
		}
		js, err := compiler.ArtifactToJSON(art)
		if err != nil {
			advArtErr = err
			return
		}
		a := &advArtifact{}
		if advArtErr = json.Unmarshal(js, a); advArtErr != nil {
			return
		}
		var keys map[string]json.RawMessage
		if advArtErr = json.Unmarshal(js, &keys); advArtErr != nil {
			return
		}
		_, a.head = keys["codePartLenSlots"]
		if a.template, advArtErr = hex.DecodeString(a.Script); advArtErr != nil {
			return
		}
		advArtErr = json.Unmarshal(js, &a.sa)
		advArtVal = a
	})
	if advArtErr != nil {
		t.Fatal(advArtErr)
	}
	return advArtVal
}

func advIsHead(t testing.TB) bool { return advArt(t).head }

func advToolchain(t testing.TB) string {
	if advIsHead(t) {
		return "HEAD"
	}
	return "pinned"
}

type advWant int

const (
	advPass   advWant = iota // must pass
	advFail                  // must fail
	advRecord                // log only
)

// advCheck asserts ok against head's or pinned's expectation and logs an
// ADV-RECORD line either way (`go test -v ./pool/pair/ | grep ADV-RECORD`).
func advCheck(t *testing.T, name string, r result, head, pinned advWant) {
	t.Helper()
	want := pinned
	if advIsHead(t) {
		want = head
	}
	t.Logf("ADV-RECORD %s | %s | pool=%v vault=%v", advToolchain(t), name, advErrS(r.pool), advErrS(r.vault))
	switch want {
	case advPass:
		mustPass(t, r)
	case advFail:
		mustFailPool(t, r)
	}
}

func advErrS(err error) string {
	if err == nil {
		return "pass"
	}
	s := err.Error()
	if len(s) > 120 {
		s = s[:120] + "..."
	}
	return "fail (" + s + ")"
}

// --- fixtures ---

var advCfgs = [][3]int64{{30, 5, 10}, {0, 0, 0}}

var (
	advFixMu    sync.Mutex
	advFixCache = map[[3]int64]*fixture{}
)

func advFix(t testing.TB, bps [3]int64) *fixture {
	t.Helper()
	advFixMu.Lock()
	defer advFixMu.Unlock()
	if f, ok := advFixCache[bps]; ok {
		return f
	}
	f := newFixture(t, bps[0], bps[1], bps[2])
	advFixCache[bps] = f
	return f
}

var advMethodNames = []string{"Swap", "Close", "Rescind"}

func advDir(aIn bool) string {
	if aIn {
		return "A in"
	}
	return "B in"
}

// advEach runs fn per fee config and direction.
func advEach(t *testing.T, fn func(t *testing.T, f *fixture, p pair, aIn bool)) {
	for _, bps := range advCfgs {
		for _, aIn := range []bool{true, false} {
			bps, aIn := bps, aIn
			t.Run(fmt.Sprintf("bps %d-%d-%d/%s", bps[0], bps[1], bps[2], advDir(aIn)), func(t *testing.T) {
				fn(t, advFix(t, bps), fresh(), aIn)
			})
		}
	}
}

// advNext is the next validator key fixture.swap names.
func advNext(k *ec.PrivateKey) *ec.PrivateKey { return key(k.Serialize()[0] + 1) }

func advValid(f *fixture, p pair, method int, aIn bool) spend {
	switch method {
	case methodSwap:
		s, _ := f.swap(p, 40_000, aIn)
		return s
	case methodClose:
		return f.close(p)
	default:
		s, _ := f.rescind(p)
		return s
	}
}

func advWithSigner(s spend, k *ec.PrivateKey) spend {
	s.signer = k
	return s
}

func advCopy(s spend) spend {
	s.outs = clone(s.outs)
	s.ins = append([]in{}, s.ins...)
	s.args = append([][]byte{}, s.args...)
	return s
}

// State offsets (pair.state): ReserveA 0, ReserveB 8, LpPubKey 16,
// ValidatorPubKey 49, ValidatorIdentity 82, Nonce 115, LpFeeAPkh 147,
// LpFeeBPkh 167, Affirmation length byte 187, Affirmation 188.
const (
	advOffA      = 0
	advOffB      = 8
	advOffLp     = 16
	advOffVal    = 49
	advOffId     = 82
	advOffNonce  = 115
	advOffFeeA   = 147
	advOffFeeB   = 167
	advOffAffLen = 187
	advOffAff    = 188
)

// advLockState is a pool output script with the given raw state.
func (f *fixture) advLockState(a int64, state []byte) []byte {
	s := append(append([]byte{}, tokenPrefix(assetA, a)...), f.code...)
	s = append(s, 0x6a)
	return append(s, state...)
}

// advStateVal is p's state with the ValidatorPubKey field replaced by raw bytes.
func advStateVal(p pair, val []byte) []byte {
	s := p.state()
	return append(append(append([]byte{}, s[:advOffVal]...), val...), s[advOffVal+33:]...)
}

// advSwap describes a Swap fully; the zero values take fixture.swap's defaults.
type advSwap struct {
	amountIn int64
	aIn      bool
	next     *ec.PrivateKey // nil: advNext(p.validator)
	nextRaw  []byte         // raw nextValidatorPubKey bytes (overrides next in the state and the arg)
	user     []byte
	com      []byte
	tcPkh    []byte
	tc       int64
	change   *out // Rúnar's change: script = the pkh
}

func advBuildSwap(f *fixture, p pair, a advSwap) (spend, swapResult) {
	next := a.next
	if next == nil {
		next = advNext(p.validator)
	}
	user, com, tcPkh := userPkh, commissionPkh, changePkh
	if a.user != nil {
		user = a.user
	}
	if a.com != nil {
		com = a.com
	}
	if a.tcPkh != nil {
		tcPkh = a.tcPkh
	}
	r := f.model(p, a.amountIn, a.aIn, next)
	inAsset, outAsset, lpPkh := assetA, assetB, lpFeeAPkh
	if !a.aIn {
		inAsset, outAsset, lpPkh = assetB, assetA, lpFeeBPkh
	}
	nextBytes := next.PubKey().Compressed()
	poolOut := f.poolLock(r.after)
	if a.nextRaw != nil {
		nextBytes = a.nextRaw
		poolOut = f.advLockState(r.after.a, advStateVal(r.after, a.nextRaw))
	}
	outs := []out{{p.sats, poolOut}, {1, f.vaultLock(r.after)}, {1, tokenP2pkh(outAsset, r.out, user)}}
	if r.lpFee > 0 {
		outs = append(outs, out{1, tokenP2pkh(inAsset, r.lpFee, lpPkh)})
	}
	if r.valFee > 0 {
		outs = append(outs, out{1, tokenP2pkh(inAsset, r.valFee, pkh(p.validator))})
	}
	if r.com > 0 {
		outs = append(outs, out{1, tokenP2pkh(inAsset, r.com, com)})
	}
	if a.tc > 0 {
		outs = append(outs, out{1, tokenP2pkh(inAsset, a.tc, tcPkh)})
	}
	var change *out
	if a.change != nil {
		change = &out{a.change.sats, a.change.script}
		if a.change.sats > 0 {
			outs = append(outs, out{a.change.sats, p2pkh(a.change.script)})
		}
	}
	return spend{
		ins: f.ins(p), outs: outs, poolIdx: 0, vaultIdx: 1,
		method: methodSwap, signer: p.validator, change: change,
		args: [][]byte{
			pushData(nextBytes),
			pushNum(a.amountIn),
			pushBool(a.aIn),
			pushData(user),
			pushData(com),
			pushData(tcPkh),
			pushNum(a.tc),
		},
	}, r
}

// advKeyWithByte is a deterministic private key whose compressed public key
// has byte v at index i.
func advKeyWithByte(t testing.TB, i int, v byte) *ec.PrivateKey {
	t.Helper()
	for n := 0; n < 1<<16; n++ {
		seed := sha256.Sum256([]byte(fmt.Sprintf("adv-key-%d", n)))
		k, _ := ec.PrivateKeyFromBytes(seed[:])
		if k.PubKey().Compressed()[i] == v {
			return k
		}
	}
	t.Fatalf("no key with %#x at %d", v, i)
	return nil
}

var advFlags = []struct {
	name string
	flag sighash.Flag
}{
	{"NONE|FORKID", sighash.NoneForkID},
	{"SINGLE|FORKID", sighash.SingleForkID},
	{"ALL|ANYONECANPAY|FORKID", sighash.AllForkID | sighash.AnyOneCanPay},
	{"NONE|ANYONECANPAY|FORKID", sighash.NoneForkID | sighash.AnyOneCanPay},
	{"SINGLE|ANYONECANPAY|FORKID", sighash.SingleForkID | sighash.AnyOneCanPay},
	{"ALL without FORKID", sighash.All},
}

// The harness's own swap and advBuildSwap agree.
func TestAdvHarnessAgreement(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	for _, aIn := range []bool{true, false} {
		a, _ := f.swap(fresh(), 40_000, aIn)
		b, _ := advBuildSwap(f, fresh(), advSwap{amountIn: 40_000, aIn: aIn})
		if fmt.Sprint(a.outs) != fmt.Sprint(b.outs) || fmt.Sprint(a.args) != fmt.Sprint(b.args) {
			t.Fatalf("%s: advBuildSwap differs from fixture.swap", advDir(aIn))
		}
		mustPass(t, advH(t, f, b))
		mustPass(t, f.run(t, a))
	}
}

// --- who can spend ---

func TestAdv_WhoCanSpend(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		_, r := f.swap(p, 40_000, aIn)
		rotated := r.after // validator advNext(p.validator)
		random := key(0x31)
		for method := 0; method < 3; method++ {
			method := method
			mn := advMethodNames[method]
			for _, pp := range []struct {
				name string
				p    pair
				prev *ec.PrivateKey // the key before the last rotation
			}{{"fresh", p, nil}, {"after one rotation", rotated, p.validator}} {
				pp := pp
				base := advValid(f, pp.p, method, aIn)
				right := pp.p.validator
				if method == methodClose {
					right = pp.p.lp
				}
				t.Run(mn+"/"+pp.name+": the right signer passes", func(t *testing.T) { mustPass(t, advH(t, f, base)) })
				wrong := map[string]*ec.PrivateKey{
					"the identity key":       validatorIdentity,
					"a random key":           random,
					"the next validator key": advNext(pp.p.validator),
				}
				if method == methodClose {
					wrong["the validator"] = pp.p.validator
				} else {
					wrong["the LP"] = pp.p.lp
				}
				if pp.prev != nil {
					wrong["the previous validator key"] = pp.prev
				}
				for name, k := range wrong {
					k := k
					t.Run(mn+"/"+pp.name+": signed by "+name, func(t *testing.T) {
						mustFailPool(t, advH(t, f, advWithSigner(base, k)))
					})
				}
				t.Run(mn+"/"+pp.name+": empty signature", func(t *testing.T) {
					mustFailPool(t, advRun(t, f, base, advOpts{rawSig: []byte{0x00}}))
				})
				t.Run(mn+"/"+pp.name+": a public key as the signature", func(t *testing.T) {
					mustFailPool(t, advRun(t, f, base, advOpts{rawSig: pushData(right.PubKey().Compressed())}))
				})
				t.Run(mn+"/"+pp.name+": the right signer's signature over a different transaction", func(t *testing.T) {
					other := advCopy(base)
					other.outs = append(other.outs, out{1, p2pkh(pkh(random))})
					mustFailPool(t, advRun(t, f, base, advOpts{sigSpend: &other}))
					// and the other way round: the honest outputs signed, a thief's outputs sent
					steal := advCopy(base)
					steal.outs[len(steal.outs)-1].script = p2pkh(pkh(random))
					mustFailPool(t, advRun(t, f, steal, advOpts{sigSpend: &base}))
				})
				t.Run(mn+"/"+pp.name+": the right signer's signature over a different pool outpoint", func(t *testing.T) {
					other := advCopy(base)
					other.ins[0].txid, other.ins[1].txid = 0x12, 0x12
					mustFailPool(t, advRun(t, f, base, advOpts{sigSpend: &other}))
				})
			}
		}
	})
}

// --- sighash types ---

// The pool's txPreimage under any type but ALL|FORKID: every method rejects.
func TestAdv_PreimageSighashType(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		for method := 0; method < 3; method++ {
			for _, fl := range advFlags {
				method, fl := method, fl
				t.Run(advMethodNames[method]+": preimage "+fl.name, func(t *testing.T) {
					s := advValid(f, p, method, aIn)
					mustFailPool(t, advRun(t, f, s, advOpts{preFlag: fl.flag}))
					if fl.flag&sighash.ForkID == 0 {
						mustFailPool(t, advRun(t, f, s, advOpts{preFlag: fl.flag, preBIP143: true}))
					}
				})
			}
		}
	})
}

// The signer's own signature must be ALL|FORKID (requireSighashAll). Every
// signature here is a valid signature of its type, made over the digest the
// interpreter computes for that type (the legacy digest without FORKID).
// Swap and Rescind run CHECKSIG first: a wrong signer fails there, the right
// signer gets past it and fails the type check, a different error. Close runs
// the type check first. The same transaction signed ALL|FORKID passes, so the
// signature's type is the only difference.
func TestAdv_SignatureSighashType(t *testing.T) {
	flags := append(append([]struct {
		name string
		flag sighash.Flag
	}{}, advFlags...), struct {
		name string
		flag sighash.Flag
	}{"ALL|FORKID with an undefined bit (0x61)", 0x61})
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		for method := 0; method < 3; method++ {
			method := method
			mn := advMethodNames[method]
			base := advValid(f, p, method, aIn)
			wrong := p.lp
			if method == methodClose {
				wrong = p.validator
			}
			t.Run(mn+": ALL|FORKID (control)", func(t *testing.T) { mustPass(t, advH(t, f, base)) })
			for _, fl := range flags {
				fl := fl
				t.Run(mn+": signature "+fl.name, func(t *testing.T) {
					r := advRun(t, f, base, advOpts{sigFlag: fl.flag})
					w := advRun(t, f, advWithSigner(base, wrong), advOpts{sigFlag: fl.flag})
					t.Logf("right signer: pool %v; wrong signer: pool %v", advErrS(r.pool), advErrS(w.pool))
					mustFailPool(t, r)
					mustFailPool(t, w)
					if method != methodClose && fl.flag != 0x61 && r.pool.Error() == w.pool.Error() {
						t.Fatalf("the right signer's %s signature failed where a wrong signer's does (%v): not the type check", fl.name, r.pool)
					}
					if fl.flag&sighash.ForkID == 0 {
						mustFailPool(t, advRun(t, f, base, advOpts{sigFlag: fl.flag, noChronicle: true}))
					}
				})
			}
		}
	})
}

// Attempts around the type check: a last byte of 0x41 on a signature made
// over another type's digest (CHECKSIG hashes by the last byte, so it is the
// ALL|FORKID digest that must verify), an empty signature, a 1-byte "41",
// bytes after the type byte. Every one is refused; the reason is logged.
func TestAdv_SignatureSighashTypeBypass(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	set41 := func(b []byte) []byte { b[len(b)-1] = 0x41; return b }
	for method := 0; method < 3; method++ {
		method := method
		mn := advMethodNames[method]
		base := advValid(f, p, method, true)
		cases := []struct {
			name string
			o    advOpts
		}{
			{"NONE|FORKID digest, last byte rewritten to 41", advOpts{sigFlag: sighash.NoneForkID, sigTweak: set41}},
			{"SINGLE|FORKID digest, last byte rewritten to 41", advOpts{sigFlag: sighash.SingleForkID, sigTweak: set41}},
			{"ALL|ANYONECANPAY|FORKID digest, last byte rewritten to 41", advOpts{sigFlag: 0xc1, sigTweak: set41}},
			{"legacy ALL digest, last byte rewritten to 41", advOpts{sigFlag: sighash.All, sigTweak: set41}},
			{"empty signature", advOpts{rawSig: []byte{0x00}}},
			{"the single byte 41", advOpts{rawSig: []byte{0x01, 0x41}}},
			{"the bytes 41 41", advOpts{rawSig: []byte{0x02, 0x41, 0x41}}},
			{"a valid ALL|FORKID signature with 41 appended", advOpts{sigTweak: func(b []byte) []byte { return append(b, 0x41) }}},
			{"a valid NONE|FORKID signature with 41 appended", advOpts{sigFlag: sighash.NoneForkID, sigTweak: func(b []byte) []byte { return append(b, 0x41) }}},
			{"a valid ALL|FORKID signature with 00 inserted before its type byte", advOpts{sigTweak: func(b []byte) []byte {
				return append(append(append([]byte{}, b[:len(b)-1]...), 0x00), 0x41)
			}}},
		}
		for _, c := range cases {
			c := c
			t.Run(mn+": "+c.name, func(t *testing.T) {
				r := advRun(t, f, base, c.o)
				t.Logf("pool %v", advErrS(r.pool))
				mustFailPool(t, r)
			})
		}
	}
}

// What the type check prevents: a signature that leaves outputs or inputs
// out, reused by a third party over a transaction of its own. Each rebuild
// below was accepted before requireSighashAll; now the signer's partial
// signature is refused outright, the untouched transaction included, and
// the same rebuild under the signer's ALL|FORKID signature fails CHECKSIG.
func TestAdv_PartialSighashSignatureCannotBeReused(t *testing.T) {
	thief := pkh(key(0x66))
	thiefKey := key(0x67)
	for _, bps := range advCfgs {
		f := advFix(t, bps)
		p := fresh()
		addIn := func(s spend) spend {
			s = advCopy(s)
			s.ins = append(s.ins, in{txid: 0x2a, vout: 0, sats: 5_000})
			return s
		}
		swapFunding := func(s spend) spend {
			s = advCopy(s)
			s.ins[2] = in{txid: 0x2b, vout: 3, sats: 7_000}
			return s
		}
		withOuts := func(s spend, o []out) spend {
			s = advCopy(s)
			s.outs = o
			return s
		}
		type rebuild struct {
			name   string
			flag   sighash.Flag
			signed spend // what the signer signed
			s      spend // what the third party sends
		}
		var cases []rebuild

		cl := f.close(p)
		steal := []out{{1, tokenP2pkh(assetA, p.a, thief)}, {1, tokenP2pkh(assetB, p.b, thief)}}
		cases = append(cases,
			rebuild{"Close, LP NONE: all outputs to the thief", 0x42, cl, withOuts(cl, steal)},
			rebuild{"Close, LP SINGLE: outputs other than 0 to the thief", 0x43, cl, withOuts(cl, []out{cl.outs[0], steal[1]})},
			rebuild{"Close, LP ALL|ANYONECANPAY: an input added", 0xc1, cl, addIn(cl)},
			rebuild{"Close, LP NONE|ANYONECANPAY: outputs to the thief, funding replaced", 0xc2, cl, swapFunding(withOuts(cl, steal))},
			rebuild{"Close, LP SINGLE|ANYONECANPAY: output 1 to the thief, an input added", 0xc3, cl, addIn(withOuts(cl, []out{cl.outs[0], steal[1]}))},
		)
		for _, aIn := range []bool{true, false} {
			base := advSwap{amountIn: 40_000, aIn: aIn, tc: 777, change: &out{4_321, changePkh}}
			signed, _ := advBuildSwap(f, p, base)
			mod := func(edit func(a *advSwap)) spend {
				a := base
				ch := *base.change
				a.change = &ch
				edit(&a)
				s, _ := advBuildSwap(f, p, a)
				return s
			}
			d := advDir(aIn)
			cases = append(cases,
				rebuild{"Swap " + d + ", validator NONE: payout to the thief", 0x42, signed, mod(func(a *advSwap) { a.user = thief })},
				rebuild{"Swap " + d + ", validator NONE: the thief as next validator", 0x42, signed, mod(func(a *advSwap) { a.next = thiefKey })},
				rebuild{"Swap " + d + ", validator NONE: amountIn doubled", 0x42, signed, mod(func(a *advSwap) { a.amountIn = 80_000 })},
				rebuild{"Swap " + d + ", validator NONE: direction flipped", 0x42, signed, mod(func(a *advSwap) { a.aIn = !aIn })},
				rebuild{"Swap " + d + ", validator SINGLE: payout to the thief", 0x43, signed, mod(func(a *advSwap) { a.user = thief })},
				rebuild{"Swap " + d + ", validator SINGLE: token change to the thief", 0x43, signed, mod(func(a *advSwap) { a.tcPkh = thief })},
				rebuild{"Swap " + d + ", validator SINGLE: sats change to the thief", 0x43, signed, mod(func(a *advSwap) { a.change.script = thief })},
				rebuild{"Swap " + d + ", validator ALL|ANYONECANPAY: funding replaced, an input added", 0xc1, signed, addIn(swapFunding(signed))},
			)
		}
		rs, _ := f.rescind(p)
		rs.outs = append(rs.outs, out{900, p2pkh(changePkh)})
		rs.change = &out{900, changePkh}
		red := advCopy(rs)
		red.outs[2].script = p2pkh(thief)
		red.change = &out{900, thief}
		cases = append(cases, rebuild{"Rescind, validator NONE: sats change to the thief", 0x42, rs, red})

		for _, c := range cases {
			c := c
			t.Run(fmt.Sprintf("bps %v: %s", bps, c.name), func(t *testing.T) {
				mustPass(t, advH(t, f, c.signed))
				orig := advRun(t, f, c.signed, advOpts{sigFlag: c.flag})
				reb := advRun(t, f, c.s, advOpts{sigFlag: c.flag, sigSpend: &c.signed})
				all := advRun(t, f, c.s, advOpts{sigSpend: &c.signed})
				t.Logf("signed tx under %#x: %v; rebuilt: %v; rebuilt under the ALL|FORKID signature: %v", byte(c.flag), advErrS(orig.pool), advErrS(reb.pool), advErrS(all.pool))
				mustFailPool(t, orig)
				mustFailPool(t, reb)
				mustFailPool(t, all)
			})
		}
	}
}

// --- pairing ---

func TestAdv_Pairing(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		other := fresh()
		other.lp = key(11)
		for method := 0; method < 3; method++ {
			method := method
			mn := advMethodNames[method]
			base := advValid(f, p, method, aIn)
			pool, vault, fund := base.ins[0], base.ins[1], base.ins[2]
			fund2 := in{txid: 0x23, vout: 0, sats: 50_000}
			type layout struct {
				name      string
				ins       []in
				pi, vi    int
				wantVault bool // the vault input, if run, must fail too
			}
			layouts := []layout{
				{"vault missing (funding at 1)", []in{pool, fund}, 0, -1, false},
				{"the pool alone", []in{pool}, 0, -1, false},
				{"a foreign vault at 1", []in{pool, {txid: 0x33, vout: 1, sats: 1, lock: f.vaultLock(other)}, fund}, 0, 1, true},
				{"a vault script at vout 2 of the pool's transaction", []in{pool, {txid: 0x11, vout: 2, sats: 1, lock: vault.lock}, fund}, 0, 1, true},
				{"the pool at input 1", []in{fund, pool, vault}, 1, 2, true},
				{"the pool at input 2", []in{fund, fund2, pool, vault}, 2, 3, true},
				{"the pool at vout 3 (its vault at vout 1)", []in{{txid: 0x11, vout: 3, sats: pool.sats, lock: pool.lock}, vault, fund}, 0, 1, true},
				{"the pool at vout 1, the vault at vout 2", []in{{txid: 0x11, vout: 1, sats: pool.sats, lock: pool.lock}, {txid: 0x11, vout: 2, sats: 1, lock: vault.lock}, fund}, 0, 1, true},
				{"an input before the pool", []in{fund2, pool, vault, fund}, 1, 2, true},
				{"an input between the pool and its vault", []in{pool, fund2, vault, fund}, 0, 2, true},
			}
			for _, l := range layouts {
				l := l
				t.Run(mn+": "+l.name, func(t *testing.T) {
					s := advCopy(base)
					s.ins, s.poolIdx, s.vaultIdx = l.ins, l.pi, l.vi
					r := advH(t, f, s)
					mustFailPool(t, r)
					if l.vi >= 0 && l.wantVault {
						mustFailVault(t, r)
					}
				})
			}
			t.Run(mn+": inputs after the vault (control)", func(t *testing.T) {
				s := advCopy(base)
				s.ins = []in{pool, vault, fund, fund2, {txid: 0x24, vout: 7, sats: 3}}
				mustPass(t, advH(t, f, s))
			})

			real := append(append(outpoint(pool), outpoint(vault)...), outpoint(fund)...)
			wrongTail := append(append(outpoint(pool), outpoint(vault)...), outpoint(fund2)...)
			flipped := append([]byte{}, real...)
			flipped[80] ^= 1
			prevs := []struct {
				name string
				b    []byte
			}{
				{"36 bytes (the pool's outpoint)", real[:36]},
				{"71 bytes", real[:71]},
				{"72 bytes (pool and vault, no funding)", real[:72]},
				{"trailing bytes", append(append([]byte{}, real...), 0x00)},
				{"the right first 72 bytes, a wrong tail", wrongTail},
				{"one byte flipped in the tail", flipped},
				{"empty", []byte{}},
			}
			for _, pv := range prevs {
				pv := pv
				t.Run(mn+": pool allPrevouts "+pv.name, func(t *testing.T) {
					s := advCopy(base)
					s.prevouts = pv.b
					mustFailPool(t, advH(t, f, s))
				})
				t.Run(mn+": vault allPrevouts "+pv.name, func(t *testing.T) {
					s := advCopy(base)
					s.vaultPrevouts = pv.b
					mustFailVault(t, advH(t, f, s))
				})
			}
			t.Run(mn+": a one-input transaction told its true 36-byte prevouts", func(t *testing.T) {
				// hashPrevouts matches; Substr(allPrevouts, 36, 36) runs off the end.
				s := advCopy(base)
				s.ins, s.vaultIdx = []in{pool}, -1
				s.prevouts = outpoint(pool)
				mustFailPool(t, advH(t, f, s))
			})
		}
	})
}

// The vault moves only with its pool: every way to spend it without one.
func TestAdv_VaultWithoutItsPool(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	base := f.close(p)
	pool, vault, fund := base.ins[0], base.ins[1], base.ins[2]
	steal := []out{{1, tokenP2pkh(assetB, p.b, userPkh)}}
	foreignPool := in{txid: 0x33, vout: 0, sats: 1, lock: f.poolLock(p)}
	cases := []struct {
		name string
		ins  []in
		vi   int
	}{
		{"alone", []in{vault}, 0},
		{"at input 0, funding at 1", []in{vault, fund}, 0},
		{"at input 0, its pool at 1", []in{vault, pool}, 0},
		{"at input 1 after funding", []in{fund, vault}, 1},
		{"at input 1 after another transaction's vout 0", []in{{txid: 0x33, vout: 0, sats: 1}, vault}, 1},
		{"at input 1 after another pool (vout 0 of another tx)", []in{foreignPool, vault}, 1},
		{"at input 1 after its own transaction's vout 2", []in{{txid: 0x11, vout: 2, sats: 1}, vault}, 1},
		{"at input 2 after its pool and funding", []in{pool, fund, vault}, 2},
		{"at input 2 after funding and its pool", []in{fund, pool, vault}, 2},
		{"a vault script at vout 0 spent at input 1 after vout 0", []in{{txid: 0x11, vout: 0, sats: 1}, {txid: 0x11, vout: 0, sats: 1, lock: vault.lock}}, 1},
		{"a vault script at vout 2, input 0 is vout 0", []in{{txid: 0x11, vout: 0, sats: 1}, {txid: 0x11, vout: 2, sats: 1, lock: vault.lock}}, 1},
		{"a vault script at vout 0, at input 0", []in{{txid: 0x11, vout: 0, sats: 1, lock: vault.lock}, fund}, 0},
	}
	for _, c := range cases {
		c := c
		t.Run(c.name, func(t *testing.T) {
			mustFailVault(t, advH(t, f, spend{ins: c.ins, outs: steal, poolIdx: -1, vaultIdx: c.vi}))
		})
	}
	t.Run("told the honest prevouts in a transaction without the pool", func(t *testing.T) {
		s := spend{ins: []in{fund, vault}, outs: steal, poolIdx: -1, vaultIdx: 1}
		s.vaultPrevouts = append(outpoint(pool), outpoint(vault)...)
		mustFailVault(t, advH(t, f, s))
	})
	for _, fl := range advFlags {
		fl := fl
		t.Run("with its pool, vault preimage "+fl.name, func(t *testing.T) {
			s := base
			s.vaultSighash = fl.flag
			mustFailVault(t, advH(t, f, s))
		})
		t.Run("without its pool, vault preimage "+fl.name+", prevouts empty and real", func(t *testing.T) {
			s := spend{ins: []in{fund, vault}, outs: steal, poolIdx: -1, vaultIdx: 1, vaultSighash: fl.flag}
			mustFailVault(t, advH(t, f, s))
			s.vaultPrevouts = []byte{}
			mustFailVault(t, advH(t, f, s))
		})
	}
}

// TRUST MODEL. The vault checks only outpoints: input 0 is vout 0 of the
// vault's own transaction and the vault is input 1 at vout 1. It never sees
// input 0's script. A vault output created at vout 1 of a transaction whose
// vout 0 is NOT a pool (a P2PKH, or a pool of other code) is released by
// whoever can spend that vout 0. Off-chain check carrying the weight: the
// lookup accepts a pool only after checking the pair at deploy (vout 0 the
// canonical pool code with the canonical VaultCodeHash, vout 1 the canonical
// vault code, same transaction).
func TestTrustModel_VaultChecksOnlyTheOutpoint(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	thief := key(0x5a)
	vault := in{txid: 0x11, vout: 1, sats: 1, lock: f.vaultLock(p)}
	steal := []out{{1, tokenP2pkh(assetB, p.b, pkh(thief))}}

	t.Run("vout 0 is the thief's P2PKH: the vault is released, outputs free", func(t *testing.T) {
		s := spend{ins: []in{{txid: 0x11, vout: 0, sats: 1_000, lock: p2pkh(pkh(thief))}, vault}, outs: steal, poolIdx: -1, vaultIdx: 1}
		mustPass(t, advRun(t, f, s, advOpts{p2pkh: map[int]*ec.PrivateKey{0: thief}}))
	})
	// The thief's own pair of other readonly args (a legitimate {0,0,0}
	// pair, the canonical vault beside it): the vault releases with whatever
	// pool code sits at vout 0, so the lookup must check the pool's code too.
	t.Run("vout 0 is a pool of other code whose LP is the thief: its Close releases the vault", func(t *testing.T) {
		g := advFix(t, [3]int64{0, 0, 0}) // other readonly args: another pool's code
		q := fresh()
		q.lp = thief
		s := g.close(q)
		s.ins[1] = vault
		s.outs = append(s.outs, steal...)
		mustPass(t, advH(t, g, s))
	})
	t.Run("control: with the canonical pool at vout 0 only the LP's Close releases it", func(t *testing.T) {
		s := f.close(p)
		mustPass(t, advH(t, f, s))
		mustFailPool(t, advH(t, f, advWithSigner(s, thief)))
	})
}

// --- the vault code witness ---

// Swap and Rescind take the vault's script as the argument vaultCode and
// build output 1 from it, after checking Sha256(vaultCode) == VaultCodeHash.
// Every other script is refused, whether output 1 is built from it or is the
// real vault. A different script with the vault's hash cannot be tried: that
// would be a SHA-256 second preimage; the nearest attempt, the hash itself as
// the argument, is refused.
func TestAdv_VaultCodeWitness(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		sw, r := f.swap(p, 40_000, aIn)
		rs, after := f.rescind(p)
		tail := tokenP2pkh(assetB, 1, pkh(p.validator))[len(tokenPrefix(assetB, 1)):]
		codes := []struct {
			name string
			code []byte
		}{
			{"a P2PKH to the validator", tail},
			{"empty", []byte{}},
			{"OP_TRUE", []byte{0x51}},
			{"the vault's code without its last byte (a prefix)", f.vault[:len(f.vault)-1]},
			{"the vault's code without its first byte", f.vault[1:]},
			{"the vault's code with 61 appended (an extension)", append(append([]byte{}, f.vault...), 0x61)},
			{"the vault's code with a P2PKH appended", append(append([]byte{}, f.vault...), tail...)},
			{"the vault's code with its middle byte flipped", advFlip(f.vault, len(f.vault)/2)},
			{"the vault's code twice", append(append([]byte{}, f.vault...), f.vault...)},
			{"the pool's code", f.code},
			{"VaultCodeHash itself (claiming the hash)", f.advVaultHash()},
		}
		for _, m := range []struct {
			name  string
			s     spend
			after pair
		}{{"Swap", sw, r.after}, {"Rescind", rs, after}} {
			m := m
			t.Run(m.name+": the vault's code (control)", func(t *testing.T) { mustPass(t, advH(t, f, m.s)) })
			for _, c := range codes {
				c := c
				t.Run(m.name+": vaultCode "+c.name+", output 1 built from it", func(t *testing.T) {
					s := advCopy(m.s)
					s.vaultArg = c.code
					s.outs[1].script = append(tokenPrefix(assetB, m.after.b), c.code...)
					mustFailPool(t, advH(t, f, s))
				})
				t.Run(m.name+": vaultCode "+c.name+", output 1 the real vault", func(t *testing.T) {
					s := advCopy(m.s)
					s.vaultArg = c.code
					mustFailPool(t, advH(t, f, s))
				})
			}
			t.Run(m.name+": vaultCode omitted", func(t *testing.T) {
				mustFailPool(t, advRun(t, f, m.s, advOpts{noVault: true}))
			})
			t.Run(m.name+": the vault's code pushed twice", func(t *testing.T) {
				mustFailPool(t, advRun(t, f, m.s, advOpts{rawVault: append(pushData(f.vault), pushData(f.vault)...)}))
			})
		}
		t.Run("Close: a vaultCode pushed after allPrevouts (Close takes none)", func(t *testing.T) {
			s := f.close(p)
			real := append(append(outpoint(s.ins[0]), outpoint(s.ins[1])...), outpoint(s.ins[2])...)
			mustFailPool(t, advRun(t, f, s, advOpts{rawPrev: append(pushData(real), pushData(f.vault)...)}))
		})
	})
}

// TRUST MODEL. The script accepts whatever VaultCodeHash the pool was
// deployed with: a pool whose hash is that of OP_TRUE writes its token B
// reserve, at the first Swap or Rescind, to an output anyone can spend. The
// canonical vault's code is then the one refused. Off-chain check carrying
// the weight: the lookup admits a pool only if VaultCodeHash is sha256 of the
// canonical Vault script.
func TestTrustModel_VaultCodeHashIsWhateverWasDeployed(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	opTrue := []byte{0x51}
	g := *f
	g.code = advCodeFor(t, assetA, assetB, advSha(opTrue), f.bps)
	p := fresh()
	sw, r := g.swap(p, 40_000, true)
	sw.vaultArg = opTrue
	sw.outs[1].script = append(tokenPrefix(assetB, r.after.b), opTrue...)
	rs, after := g.rescind(p)
	rs.vaultArg = opTrue
	rs.outs[1].script = append(tokenPrefix(assetB, after.b), opTrue...)
	for name, s := range map[string]spend{"Swap": sw, "Rescind": rs} {
		s := s
		t.Run(name+": token B written to an OP_TRUE output", func(t *testing.T) {
			mustPass(t, advH(t, &g, s))
			canon := advCopy(s)
			canon.vaultArg = nil
			mustFailPool(t, advH(t, &g, canon))
			// the output it wrote: spendable with an empty unlocking script
			free := spend{ins: []in{{txid: 0x44, vout: 1, sats: 1, lock: s.outs[1].script}}, outs: []out{{1, tokenP2pkh(assetB, 1, userPkh)}}, poolIdx: -1, vaultIdx: -1}
			tx := advTx(free, advOpts{})
			tx.Inputs[0].UnlockingScript = script.NewFromBytes([]byte{})
			if err := advExec(tx, 0, free.ins[0], true); err != nil {
				t.Fatalf("the OP_TRUE vault output is not freely spendable: %v", err)
			}
		})
	}
}

// --- stranding ---

// No accepted spend of a pool leaves its vault behind. Every advRun in both
// files asserts it (advStrandingCheck); here every arrangement of up to four
// inputs drawn from {pool, its vault, funding, a foreign vault} is run for
// each method, and the pool input passes exactly when the arrangement starts
// pool, vault.
func TestAdv_NoStranding(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	other := fresh()
	other.lp = key(11)
	for method := 0; method < 3; method++ {
		base := advValid(f, p, method, true)
		items := map[byte]in{
			'P': base.ins[0],
			'V': base.ins[1],
			'F': base.ins[2],
			'X': {txid: 0x33, vout: 1, sats: 1, lock: f.vaultLock(other)},
		}
		var perms []string
		var gen func(prefix string, left string)
		gen = func(prefix, left string) {
			if strings.Contains(prefix, "P") {
				perms = append(perms, prefix)
			}
			for i := range left {
				gen(prefix+string(left[i]), left[:i]+left[i+1:])
			}
		}
		gen("", "PVFX")
		accepted := 0
		for _, perm := range perms {
			s := advCopy(base)
			s.ins = nil
			s.poolIdx, s.vaultIdx = -1, -1
			for i := range perm {
				s.ins = append(s.ins, items[perm[i]])
				switch perm[i] {
				case 'P':
					s.poolIdx = i
				case 'V':
					s.vaultIdx = i
				}
			}
			r := advH(t, f, s)
			want := strings.HasPrefix(perm, "PV")
			if (r.pool == nil) != want {
				t.Errorf("%s inputs %s: pool accepted=%v, want %v (%v)", advMethodNames[method], perm, r.pool == nil, want, r.pool)
			}
			if r.pool == nil {
				accepted++
				if r.vault != nil {
					t.Errorf("%s inputs %s: pool accepted but its vault rejected: %v", advMethodNames[method], perm, r.vault)
				}
			}
		}
		t.Logf("%s: %d input arrangements, %d accepted (all starting pool, vault)", advMethodNames[method], len(perms), accepted)
	}
	t.Run("Close without the vault is rejected, not a stranded token B reserve", func(t *testing.T) {
		s := f.close(p)
		for _, ins := range [][]in{{s.ins[0]}, {s.ins[0], s.ins[2]}, {s.ins[0], s.ins[2], s.ins[1]}} {
			c := advCopy(s)
			c.ins, c.vaultIdx = ins, -1
			mustFailPool(t, advH(t, f, c))
		}
	})
	t.Logf("accepted pool inputs checked against the stranding invariant so far in this run: %d", advAccepted.Load())
}

// --- output-set attacks on Swap ---

func advSha(b []byte) []byte {
	h := sha256.Sum256(b)
	return h[:]
}

// advVaultHash is VaultCodeHash for f's vault: sha256 of the vault script.
func (f *fixture) advVaultHash() []byte { return advSha(f.vault) }

// advCodeFor is the pool code (no prefix, no state) for other readonly args.
func advCodeFor(t testing.TB, a, b, vaultHash []byte, bps [3]int64) []byte {
	t.Helper()
	sa := advArt(t).sa
	p := pair{sats: 1, a: 1000, b: 1000, lp: key(1), validator: key(2)}
	h := hex.EncodeToString
	c := runar.NewRunarContract(&sa, []interface{}{
		p.a, p.b,
		h(p.lp.PubKey().Compressed()), h(p.validator.PubKey().Compressed()), h(validatorIdentity.PubKey().Compressed()),
		h(nonce), h(lpFeeAPkh), h(lpFeeBPkh), h(affirmation),
		h(a), h(b), h(vaultHash), bps[0], bps[1], bps[2],
	})
	full, _ := hex.DecodeString(c.GetLockingScript())
	tail := append([]byte{0x6a}, p.state()...)
	if !bytes.HasSuffix(full, tail) {
		t.Fatal("SDK tail is not OP_RETURN || state")
	}
	return full[:len(full)-len(tail)]
}

func TestAdv_SwapOutputSet(t *testing.T) {
	otherAsset := bytes.Repeat([]byte{0xc7}, 32)
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		s, r := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: aIn, tc: 777, change: &out{4_321, changePkh}})
		mustPass(t, advH(t, f, s))
		inAsset, outAsset := assetA, assetB
		if !aIn {
			inAsset, outAsset = assetB, assetA
		}
		n := len(s.outs)
		fees := []struct {
			name string
			amt  int64
			pkh  []byte
		}{}
		lpPkh := lpFeeAPkh
		if !aIn {
			lpPkh = lpFeeBPkh
		}
		if r.lpFee > 0 {
			fees = append(fees, struct {
				name string
				amt  int64
				pkh  []byte
			}{"LP fee", r.lpFee, lpPkh})
		}
		if r.valFee > 0 {
			fees = append(fees, struct {
				name string
				amt  int64
				pkh  []byte
			}{"validator fee", r.valFee, pkh(p.validator)})
		}
		if r.com > 0 {
			fees = append(fees, struct {
				name string
				amt  int64
				pkh  []byte
			}{"commission", r.com, commissionPkh})
		}
		tcIdx := 3 + len(fees)
		mut := func(name string, edit func(c *spend)) {
			t.Run(name, func(t *testing.T) {
				c := advCopy(s)
				edit(&c)
				mustFailPool(t, advH(t, f, c))
			})
		}
		mut("an extra output at the end", func(c *spend) { c.outs = append(c.outs, out{1, p2pkh(userPkh)}) })
		mut("an extra output in the middle (after the payout)", func(c *spend) {
			c.outs = append(c.outs[:3], append([]out{{1, tokenP2pkh(outAsset, 1, userPkh)}}, c.outs[3:]...)...)
		})
		mut("the payout twice", func(c *spend) { c.outs = append(c.outs, c.outs[2]) })
		for i := 0; i < n; i++ {
			i := i
			mut(fmt.Sprintf("output %d removed", i), func(c *spend) { c.outs = append(c.outs[:i], c.outs[i+1:]...) })
		}
		for i := 0; i+1 < n; i++ {
			i := i
			mut(fmt.Sprintf("outputs %d and %d swapped", i, i+1), func(c *spend) { c.outs[i], c.outs[i+1] = c.outs[i+1], c.outs[i] })
		}
		mut("the payout split in two", func(c *spend) {
			h := r.out / 2
			c.outs = append(c.outs[:2], append([]out{{1, tokenP2pkh(outAsset, h, userPkh)}, {1, tokenP2pkh(outAsset, r.out-h, userPkh)}}, c.outs[3:]...)...)
		})
		mut("the payout in the input token", func(c *spend) { c.outs[2].script = tokenP2pkh(inAsset, r.out, userPkh) })
		mut("the payout in a third token", func(c *spend) { c.outs[2].script = tokenP2pkh(otherAsset, r.out, userPkh) })
		mut("the payout of 2 sats", func(c *spend) { c.outs[2].sats = 2 })
		mut("the payout of 0 sats", func(c *spend) { c.outs[2].sats = 0 })
		for i, fe := range fees {
			i, fe := i, fe
			mut(fe.name+" in the output token", func(c *spend) { c.outs[3+i].script = tokenP2pkh(outAsset, fe.amt, fe.pkh) })
			mut(fe.name+" of 2 sats", func(c *spend) { c.outs[3+i].sats = 2 })
			mut(fe.name+" one more", func(c *spend) { c.outs[3+i].script = tokenP2pkh(inAsset, fe.amt+1, fe.pkh) })
		}
		mut("token change in the output token", func(c *spend) { c.outs[tcIdx].script = tokenP2pkh(outAsset, 777, changePkh) })
		mut("token change of 2 sats", func(c *spend) { c.outs[tcIdx].sats = 2 })
		mut("pool and vault swapped", func(c *spend) { c.outs[0], c.outs[1] = c.outs[1], c.outs[0] })
		mut("pool continuation with one more sat", func(c *spend) { c.outs[0].sats++ })
		mut("vault of 2 sats", func(c *spend) { c.outs[1].sats = 2 })
		mut("vault of 0 sats", func(c *spend) { c.outs[1].sats = 0 })
		mut("vault replaced by a token P2PKH of the same amount", func(c *spend) { c.outs[1].script = tokenP2pkh(assetB, r.after.b, userPkh) })
		mut("vault replaced by a plain P2PKH", func(c *spend) { c.outs[1].script = p2pkh(userPkh) })
		mut("vault with the pool's code", func(c *spend) { c.outs[1].script = append(tokenPrefix(assetB, r.after.b), f.code...) })
		mut("vault with OP_TRUE as code", func(c *spend) { c.outs[1].script = append(tokenPrefix(assetB, r.after.b), 0x51) })
		mut("vault code with a byte appended", func(c *spend) { c.outs[1].script = append(f.vaultLock(r.after), 0x61) })
		mut("vault code with its first byte changed", func(c *spend) {
			v := f.vaultLock(r.after)
			v[len(tokenPrefix(assetB, r.after.b))] ^= 1
			c.outs[1].script = v
		})
		mut("vault in token A", func(c *spend) { c.outs[1].script = append(tokenPrefix(assetA, r.after.b), f.vault...) })
		mut("vault in a third token", func(c *spend) { c.outs[1].script = append(tokenPrefix(otherAsset, r.after.b), f.vault...) })

		// another pool's code for the continuation
		state := r.after.state()
		for _, oc := range []struct {
			name string
			code func() []byte
		}{
			{"other AssetIdA", func() []byte { return advCodeFor(t, otherAsset, assetB, f.advVaultHash(), f.bps) }},
			{"other AssetIdB", func() []byte { return advCodeFor(t, assetA, otherAsset, f.advVaultHash(), f.bps) }},
			{"AssetIdA and AssetIdB swapped", func() []byte { return advCodeFor(t, assetB, assetA, f.advVaultHash(), f.bps) }},
			{"other fees", func() []byte {
				return advCodeFor(t, assetA, assetB, f.advVaultHash(), [3]int64{f.bps[0] + 1, f.bps[1], f.bps[2]})
			}},
			{"other VaultCodeHash", func() []byte {
				return advCodeFor(t, assetA, assetB, advSha(append(append([]byte{}, f.vault...), 0x61)), f.bps)
			}},
		} {
			oc := oc
			mut("pool continuation with "+oc.name+" (another pool's code)", func(c *spend) {
				code := oc.code()
				if bytes.Equal(code, f.code) {
					t.Fatal("other readonly args gave the same code")
				}
				lock := append(append(tokenPrefix(assetA, r.after.a), code...), 0x6a)
				c.outs[0].script = append(lock, state...)
			})
		}
		fields := []struct {
			name     string
			off, len int
		}{
			{"ReserveA", advOffA, 8}, {"ReserveB", advOffB, 8}, {"LpPubKey", advOffLp, 33},
			{"ValidatorPubKey", advOffVal, 33}, {"ValidatorIdentity", advOffId, 33}, {"Nonce", advOffNonce, 32},
			{"LpFeeAPkh", advOffFeeA, 20}, {"LpFeeBPkh", advOffFeeB, 20}, {"Affirmation length", advOffAffLen, 1},
			{"Affirmation", advOffAff, len(affirmation)},
		}
		for _, fd := range fields {
			for _, at := range []int{0, fd.len - 1} {
				fd, at := fd, at
				mut(fmt.Sprintf("state %s byte %d flipped", fd.name, at), func(c *spend) {
					st := append([]byte{}, state...)
					st[fd.off+at] ^= 0x01
					c.outs[0].script = f.advLockState(r.after.a, st)
				})
			}
		}
		mut("ReserveA and ReserveB swapped in state", func(c *spend) {
			st := append([]byte{}, state...)
			copy(st[0:8], state[8:16])
			copy(st[8:16], state[0:8])
			c.outs[0].script = f.advLockState(r.after.a, st)
		})
		mut("ReserveA and ReserveB swapped everywhere (prefixes and state)", func(c *spend) {
			sw := r.after
			sw.a, sw.b = sw.b, sw.a
			c.outs[0].script, c.outs[1].script = f.poolLock(sw), f.vaultLock(sw)
		})
		for _, d := range []int64{-1, 1} {
			d := d
			mut(fmt.Sprintf("pool prefix (A) %+d, state right", d), func(c *spend) {
				c.outs[0].script = f.advLockState(r.after.a+d, state)
			})
			mut(fmt.Sprintf("vault prefix (B) %+d, state right", d), func(c *spend) {
				a := r.after
				a.b += d
				c.outs[1].script = f.vaultLock(a)
			})
			mut(fmt.Sprintf("state ReserveB %+d, vault prefix right", d), func(c *spend) {
				a := r.after
				a.b += d
				c.outs[0].script = f.poolLock(a)
			})
			mut(fmt.Sprintf("state ReserveA %+d, pool prefix right", d), func(c *spend) {
				a := r.after
				a.a += d
				c.outs[0].script = f.advLockState(r.after.a, a.state())
			})
		}
	})
}

// --- trust model ---

// TRUST MODEL. The script sees no token input in either direction. With its
// key alone the validator signs a Swap of any amountIn and takes nearly all
// of the other reserve: token B with a fake A-in Swap, token A with a fake
// B-in Swap. Off-chain check carrying the weight: the validator confirms the
// token inputs of both assets cover the token outputs before signing (and the
// BRC-162 overlay refuses outputs its inputs do not cover).
func TestTrustModel_ValidatorDrainsWithFakeTokenInput(t *testing.T) {
	for _, bps := range advCfgs {
		f := advFix(t, bps)
		p := fresh()
		for _, aIn := range []bool{true, false} {
			rin, rout, outName := p.a, p.b, "B"
			if !aIn {
				rin, rout, outName = p.b, p.a, "A"
			}
			for _, mult := range []int64{10, 1000, 1_000_000_000} {
				name := fmt.Sprintf("bps %v: %s, amountIn %d x the input reserve, no token input", bps, advDir(aIn), mult)
				t.Run(name, func(t *testing.T) {
					s, r := f.swap(p, rin*mult, aIn)
					if !r.ok {
						t.Fatal("model rejects")
					}
					mustPass(t, advH(t, f, s))
					t.Logf("drained %d of %d token %s (%.9f of the reserve)", r.out, rout, outName, float64(r.out)/float64(rout))
				})
			}
		}
	}
}

// TRUST MODEL. nextValidatorPubKey is any 33 bytes: a validator naming bytes
// no one holds ends Swap and Rescind for good, and the LP still closes.
// Off-chain check: the lookup and the LP watch for a rotation to a key the
// validator cannot sign with (the pool is then only closable).
func TestTrustModel_ValidatorNamesUnusableNextKey(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	for _, nk := range []struct {
		name string
		b    []byte
	}{
		{"33 zero bytes", make([]byte, 33)},
		{"02 || ff*32 (x not on the curve)", append([]byte{0x02}, bytes.Repeat([]byte{0xff}, 32)...)},
		{"07 || a real x (bad prefix)", append([]byte{0x07}, key(50).PubKey().Compressed()[1:]...)},
	} {
		nk := nk
		t.Run(nk.name, func(t *testing.T) {
			s, r := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: true, nextRaw: nk.b})
			mustPass(t, advH(t, f, s))
			after := r.after
			lock := f.advLockState(after.a, advStateVal(after, nk.b))
			for _, k := range []*ec.PrivateKey{p.validator, advNext(p.validator), p.lp, validatorIdentity} {
				for _, m := range []int{methodSwap, methodRescind} {
					c := advCopy(advValid(f, after, m, false))
					c.ins[0].lock = lock
					mustFailPool(t, advH(t, f, advWithSigner(c, k)))
				}
			}
			c := advCopy(f.close(after))
			c.ins[0].lock = lock
			mustPass(t, advH(t, f, c))
		})
	}
}

// TRUST MODEL. The validator rescinds whenever it likes; the LP closes after.
// Off-chain check: none needed for safety (the LP keeps its funds); the
// lookup stops quoting a rescinded pool.
func TestTrustModel_ValidatorRescindsAnytime(t *testing.T) {
	for _, bps := range advCfgs {
		f := advFix(t, bps)
		p := fresh()
		for i, q := range []pair{p, func() pair { _, r := f.swap(p, 40_000, true); return r.after }()} {
			rs, after := f.rescind(q)
			mustPass(t, advH(t, f, rs))
			mustPass(t, advH(t, f, f.close(after)))
			t.Logf("bps %v pool %d: rescinded, then closed by the LP", bps, i)
		}
	}
}

// TRUST MODEL. The relay names any commissionPkh (and the taker any payout
// and change address). Off-chain check: the validator's signature covers the
// arguments it vetted; who receives the commission is the relay's business.
func TestTrustModel_RelayNamesAnyCommissionPkh(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	for name, com := range map[string][]byte{
		"the validator's own pkh": pkh(p.validator), "the LP's pkh": pkh(p.lp), "the user's pkh": userPkh,
		"20 zero bytes": make([]byte, 20), "LpFeeAPkh": lpFeeAPkh,
	} {
		com := com
		t.Run(name, func(t *testing.T) {
			for _, aIn := range []bool{true, false} {
				s, _ := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: aIn, com: com})
				mustPass(t, advH(t, f, s))
			}
		})
	}
}

// TRUST MODEL. The continuation vault is always 1 sat: a vault holding more
// is not carried, the excess goes wherever the transaction sends it (here
// Rúnar's change). Off-chain check: the lookup's rule that a pair is deployed
// with a 1-sat vault.
func TestTrustModel_VaultSatsAreNotCarried(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	s, _ := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: true, change: &out{999, changePkh}})
	s.ins[1].sats = 1_000
	mustPass(t, advH(t, f, s))
	t.Log("a 1000-sat vault: continuation vault 1 sat, 999 sats left to the change output")
}

// --- two pools in one transaction ---

// The second pool input of a transaction can never verify: a pool must be
// input 0. A transaction spending two pools is invalid whatever its outputs.
func TestAdv_TwoPoolsInOneTransaction(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	g := advFix(t, [3]int64{0, 0, 0})
	p := fresh()
	for _, tw := range []struct {
		name string
		g    *fixture
		q    pair
	}{
		{"identical twin", f, p},
		{"distinct pool (other fees, other LP)", g, func() pair { q := fresh(); q.lp = key(12); return q }()},
	} {
		tw := tw
		for method := 0; method < 3; method++ {
			method := method
			t.Run(tw.name+": "+advMethodNames[method], func(t *testing.T) {
				first := advValid(f, p, method, true)
				second := advValid(tw.g, tw.q, method, true)
				ins := []in{
					first.ins[0], first.ins[1],
					{txid: 0x33, vout: 0, sats: tw.q.sats, lock: second.ins[0].lock},
					{txid: 0x33, vout: 1, sats: 1, lock: second.ins[1].lock},
					first.ins[2],
				}
				outs := append(clone(first.outs), second.outs...)
				a := advCopy(first)
				a.ins, a.outs = ins, outs
				ra := advH(t, f, a)
				t.Logf("first pool (input 0) with both pools' outputs: pool %v, vault %v", advErrS(ra.pool), advErrS(ra.vault))
				b := advCopy(second)
				b.ins, b.outs, b.poolIdx, b.vaultIdx = ins, outs, 2, 3
				rb := advH(t, tw.g, b)
				mustFailPool(t, rb)
				mustFailVault(t, rb)
				// the second pool's own outputs first: still not input 0
				b.outs = append(clone(second.outs), first.outs...)
				rb = advH(t, tw.g, b)
				mustFailPool(t, rb)
				mustFailVault(t, rb)
			})
		}
	}
}

// --- method selector and layout confusion ---

func TestAdv_MethodSelector(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		t.Run("layout x selector: only the matching selector runs", func(t *testing.T) {
			sel := []struct {
				name string
				push []byte
				v    int64
			}{{"0", []byte{0x00}, 0}, {"1", []byte{0x51}, 1}, {"2", []byte{0x52}, 2}, {"3", []byte{0x53}, 3}, {"-1", []byte{0x4f}, -1}, {"16", []byte{0x60}, 16}, {"100", []byte{0x01, 0x64}, 100}}
			for m := 0; m < 3; m++ {
				for _, v := range sel {
					r := advRun(t, f, advValid(f, p, m, aIn), advOpts{method: v.push})
					if int64(m) == v.v && !r.ok() {
						t.Errorf("%s layout, selector %s: %v", advMethodNames[m], v.name, r.pool)
					}
					if int64(m) != v.v && r.pool == nil {
						t.Errorf("%s layout dispatched by selector %s", advMethodNames[m], v.name)
					}
				}
			}
		})
		t.Run("encodings of a selector dispatch by numeric value (recorded)", func(t *testing.T) {
			for m := 0; m < 3; m++ {
				v := byte(m)
				for _, e := range []struct {
					name string
					push []byte
					val  int64
				}{
					{"OP_PUSHBYTES_1 v", []byte{0x01, v}, int64(m)},
					{"two bytes v 00", []byte{0x02, v, 0x00}, int64(m)},
					{"PUSHDATA1 v", []byte{0x4c, 0x01, v}, int64(m)},
					{"PUSHDATA2 v", []byte{0x4d, 0x01, 0x00, v}, int64(m)},
					{"PUSHDATA4 v", []byte{0x4e, 0x01, 0x00, 0x00, 0x00, v}, int64(m)},
					{"negative zero 80", []byte{0x01, 0x80}, 0},
					{"negative zero 00 80", []byte{0x02, 0x00, 0x80}, 0},
					{"v with the sign bit (-v)", []byte{0x02, v, 0x80}, -int64(m)},
					{"v + 256", []byte{0x02, v, 0x01}, int64(m) + 256},
				} {
					r := advRun(t, f, advValid(f, p, m, aIn), advOpts{method: e.push})
					want := e.val == int64(m)
					t.Logf("%s layout, selector %s (%x): pool %v", advMethodNames[m], e.name, e.push, advErrS(r.pool))
					if want != (r.pool == nil) {
						t.Errorf("%s layout, selector %s (%x, value %d): accepted=%v, want %v", advMethodNames[m], e.name, e.push, e.val, r.pool == nil, want)
					}
				}
			}
		})
		t.Run("a push after the selector", func(t *testing.T) {
			for m := 0; m < 3; m++ {
				for v := int64(0); v < 3; v++ {
					if advRun(t, f, advValid(f, p, m, aIn), advOpts{trailing: [][]byte{pushNum(v)}}).pool == nil {
						t.Errorf("%s layout accepted with a trailing push of %d", advMethodNames[m], v)
					}
				}
			}
		})
		t.Run("no preimage", func(t *testing.T) {
			for m := 0; m < 3; m++ {
				mustFailPool(t, advRun(t, f, advValid(f, p, m, aIn), advOpts{noPre: true}))
			}
		})
		t.Run("one method's layout under another's selector, either signer", func(t *testing.T) {
			for m := 0; m < 3; m++ {
				for sel := 0; sel < 3; sel++ {
					if sel == m {
						continue
					}
					for _, k := range []*ec.PrivateKey{p.validator, p.lp} {
						r := advRun(t, f, advWithSigner(advValid(f, p, m, aIn), k), advOpts{method: pushNum(int64(sel))})
						if r.pool == nil {
							t.Errorf("%s layout under the %s selector accepted", advMethodNames[m], advMethodNames[sel])
						}
					}
				}
			}
		})
	})
}

// Extra pushes below the arguments, and signatures in the wrong layout.
func TestAdv_LeadingPushesAndLayouts(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		junk := [][]byte{pushData(bytes.Repeat([]byte{0xee}, 33)), pushNum(1), pushNum(0)}
		for method := 0; method < 3; method++ {
			method := method
			mn := advMethodNames[method]
			base := advValid(f, p, method, aIn)
			tx := advTx(base, advOpts{})
			dig := advHash(advPreimage(t, tx, 0, base.ins[0].sats, afterSeparator(base.ins[0].lock), sighash.AllForkID, false))
			sigOf := func(k *ec.PrivateKey) []byte {
				s, _ := k.Sign(dig)
				return pushData(append(s.Serialize(), 0x41))
			}
			right, wrong := p.validator, p.lp
			if method == methodClose {
				right, wrong = p.lp, p.validator
			}
			for n := 1; n <= 3; n++ {
				n := n
				t.Run(fmt.Sprintf("%s: right signer, %d junk pushes below (recorded)", mn, n), func(t *testing.T) {
					r := advRun(t, f, base, advOpts{leading: junk[:n]})
					t.Logf("%s with %d leading pushes: pool %v", mn, n, advErrS(r.pool))
				})
				t.Run(fmt.Sprintf("%s: wrong signer, %d junk pushes below", mn, n), func(t *testing.T) {
					mustFailPool(t, advRun(t, f, advWithSigner(base, wrong), advOpts{leading: junk[:n]}))
				})
			}
			t.Run(mn+": the right signature pushed below, a wrong one in the slot", func(t *testing.T) {
				c := advWithSigner(base, wrong)
				mustFailPool(t, advRun(t, f, c, advOpts{leading: [][]byte{sigOf(right)}}))
				mustFailPool(t, advRun(t, f, c, advOpts{leading: [][]byte{sigOf(right), sigOf(wrong)}}))
				mustFailPool(t, advRun(t, f, c, advOpts{leading: [][]byte{sigOf(wrong), sigOf(right)}}))
			})
			t.Run(mn+": the right signature after the selector", func(t *testing.T) {
				mustFailPool(t, advRun(t, f, advWithSigner(base, wrong), advOpts{trailing: [][]byte{sigOf(right)}}))
			})
		}
		t.Run("the validator's signature in the Close layout, padded", func(t *testing.T) {
			for _, pad := range [][][]byte{nil, {pushNum(0)}, {pushNum(0), pushNum(0)}, {pushData(make([]byte, 20)), pushNum(0)}} {
				mustFailPool(t, advRun(t, f, advWithSigner(f.close(p), p.validator), advOpts{leading: pad}))
				mustFailPool(t, advRun(t, f, advValid(f, p, methodRescind, aIn), advOpts{method: pushNum(methodClose), leading: pad}))
			}
		})
		t.Run("the LP's signature in the Swap and Rescind layouts, padded", func(t *testing.T) {
			for _, pad := range [][][]byte{nil, {pushNum(0)}, {pushNum(0), pushNum(0)}} {
				for _, m := range []int{methodSwap, methodRescind} {
					mustFailPool(t, advRun(t, f, advWithSigner(advValid(f, p, m, aIn), p.lp), advOpts{leading: pad}))
				}
			}
		})
	})
}

// --- unlocking malleability ---

// With a validator-signed Swap in hand a third party may edit the unlocking
// script (it is not signed). Every accepted variant must leave the outputs
// exactly as signed (they are fixed here by construction and checked by the
// contract's hashOutputs); the expected acceptances are bytes that build no
// output (commissionPkh at a zero commission, tokenChangePkh at tokenChange 0,
// _changePKH at _changeAmount 0) and other encodings of the same values.
func TestAdv_UnlockingMalleability(t *testing.T) {
	advEach(t, func(t *testing.T, f *fixture, p pair, aIn bool) {
		base, r := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: aIn})
		_, baseTx := advRunTx(t, f, base, advOpts{})
		other20 := pushData(bytes.Repeat([]byte{0xcd}, 20))
		noCom := r.com == 0
		amt := scriptNum(40_000)
		real := append(append(outpoint(base.ins[0]), outpoint(base.ins[1])...), outpoint(base.ins[2])...)
		type mut struct {
			name string
			pass bool
			edit func(s *spend, o *advOpts)
		}
		arg := func(i int, v []byte) func(s *spend, o *advOpts) {
			return func(s *spend, o *advOpts) { s.args[i] = v }
		}
		muts := []mut{
			{"nextValidatorPubKey: another key", false, arg(0, pushData(key(0x31).PubKey().Compressed()))},
			{"nextValidatorPubKey as PUSHDATA1 (same bytes)", true, arg(0, append([]byte{0x4c, 33}, advNext(p.validator).PubKey().Compressed()...))},
			{"amountIn + 1", false, arg(1, pushNum(40_001))},
			{"amountIn - 1", false, arg(1, pushNum(39_999))},
			{"amountIn with a padding zero byte (same value)", true, arg(1, pushData(append(append([]byte{}, amt...), 0x00)))},
			{"amountIn as PUSHDATA1 (same value)", true, arg(1, append([]byte{0x4c, byte(len(amt))}, amt...))},
			{"aIn flipped", false, arg(2, pushBool(!aIn))},
			{"aIn as 01 01", aIn, arg(2, []byte{0x01, 0x01})},
			{"aIn as 01 00 (not the empty false)", false, arg(2, []byte{0x01, 0x00})},
			{"aIn as 01 02", false, arg(2, []byte{0x01, 0x02})},
			{"aIn as PUSHDATA1 of the same byte string", true, arg(2, map[bool][]byte{true: {0x4c, 0x01, 0x01}, false: {0x4c, 0x00}}[aIn])},
			{"userPkh changed", false, arg(3, other20)},
			{"commissionPkh changed", noCom, arg(4, other20)},
			{"tokenChangePkh changed (tokenChange 0)", true, arg(5, other20)},
			{"tokenChange 0 -> 1", false, arg(6, pushNum(1))},
			{"tokenChange 0 as 01 00", true, arg(6, []byte{0x01, 0x00})},
			{"tokenChange 0 as negative zero", true, arg(6, []byte{0x01, 0x80})},
			{"tokenChange -1", false, arg(6, []byte{0x01, 0x81})},
			{"_changePKH changed (_changeAmount 0)", true, func(s *spend, o *advOpts) { o.chPkh = other20 }},
			{"_changeAmount 0 -> 1", false, func(s *spend, o *advOpts) { o.chAmt = pushNum(1) }},
			{"_changeAmount 0 as 01 00", true, func(s *spend, o *advOpts) { o.chAmt = []byte{0x01, 0x00} }},
			{"allPrevouts as PUSHDATA2 (same bytes)", true, func(s *spend, o *advOpts) {
				o.rawPrev = append([]byte{0x4d, byte(len(real)), byte(len(real) >> 8)}, real...)
			}},
			{"allPrevouts one byte changed", false, func(s *spend, o *advOpts) {
				b := append([]byte{}, real...)
				b[100] ^= 1
				o.rawPrev = pushData(b)
			}},
			{"vaultCode as PUSHDATA4 (same bytes)", true, func(s *spend, o *advOpts) {
				n := len(f.vault)
				o.rawVault = append([]byte{0x4e, byte(n), byte(n >> 8), 0, 0}, f.vault...)
			}},
			{"vaultCode one byte changed", false, func(s *spend, o *advOpts) { s.vaultArg = advFlip(f.vault, len(f.vault)/2) }},
			{"vaultCode with a byte appended", false, func(s *spend, o *advOpts) { s.vaultArg = append(append([]byte{}, f.vault...), 0x61) }},
			{"vaultCode omitted", false, func(s *spend, o *advOpts) { o.noVault = true }},
			{"_codePart as PUSHDATA4 (same bytes)", true, func(s *spend, o *advOpts) {
				n := len(f.code)
				o.rawCode = append([]byte{0x4e, byte(n), byte(n >> 8), 0, 0}, f.code...)
			}},
			{"_codePart one byte changed", false, func(s *spend, o *advOpts) {
				cp := append([]byte{}, f.code...)
				cp[len(cp)/2] ^= 1
				o.codePart = cp
			}},
			{"_codePart empty", false, func(s *spend, o *advOpts) { o.codePart = []byte{} }},
			{"signature with S replaced by n-S (high S; accepted by the go-sdk interpreter, node policy not tested)", true, func(s *spend, o *advOpts) {
				o.sigTweak = func(b []byte) []byte {
					sig, err := ec.ParseDERSignature(b[:len(b)-1])
					if err != nil {
						t.Fatal(err)
					}
					sig.S = new(big.Int).Sub(ec.S256().N, sig.S)
					return append(sig.Serialize(), b[len(b)-1])
				}
			}},
			{"signature hashtype byte 41 -> 42", false, func(s *spend, o *advOpts) {
				o.sigTweak = func(b []byte) []byte { b[len(b)-1] = 0x42; return b }
			}},
			{"signature hashtype byte 41 -> c1", false, func(s *spend, o *advOpts) {
				o.sigTweak = func(b []byte) []byte { b[len(b)-1] = 0xc1; return b }
			}},
		}
		for _, m := range muts {
			m := m
			t.Run(m.name, func(t *testing.T) {
				s := advCopy(base)
				o := advOpts{}
				m.edit(&s, &o)
				res, tx := advRunTx(t, f, s, o)
				t.Logf("pool %v", advErrS(res.pool))
				if m.pass {
					mustPass(t, res)
				} else {
					mustFailPool(t, res)
				}
				if res.ok() {
					for i := range baseTx.Outputs {
						if !bytes.Equal(baseTx.Outputs[i].Bytes(), tx.Outputs[i].Bytes()) || len(baseTx.Outputs) != len(tx.Outputs) {
							t.Fatalf("an accepted unlocking variant moved output %d", i)
						}
					}
				}
			})
		}
	})
}

// --- Close always works for the LP, and only for the LP ---

func TestAdv_CloseAlwaysWorks(t *testing.T) {
	for _, bps := range advCfgs {
		f := advFix(t, bps)
		p := fresh()
		swapped := p
		for i := 0; i < 5; i++ {
			s, r := f.swap(swapped, int64(30_000+1000*i), i%2 == 0)
			mustPass(t, advH(t, f, s))
			swapped = r.after
		}
		_, rescinded := f.rescind(p)
		tiny := pair{sats: 1, a: 1, b: 1, lp: key(10), validator: key(20)}
		rich := fresh()
		rich.sats = 5_000
		huge := pair{sats: 1, a: 1<<63 - 1, b: 1<<63 - 1, lp: key(10), validator: key(20)}
		var many []out
		for i := 0; i < 20; i++ {
			many = append(many, out{int64(i), p2pkh(bytes.Repeat([]byte{byte(i)}, 20))})
		}
		for _, c := range []struct {
			name string
			q    pair
			outs []out
		}{
			{"fresh", p, nil},
			{"after five swaps", swapped, nil},
			{"after Rescind", rescinded, nil},
			{"reserves of 1 and 1", tiny, nil},
			{"reserves of 2^63-1", huge, nil},
			{"a pool output of 5000 sats", rich, nil},
			{"twenty unrelated outputs", p, many},
			{"a single OP_FALSE OP_RETURN of 0 sats", p, []out{{0, []byte{0x00, 0x6a}}}},
			{"a single OP_RETURN of 1 sat", p, []out{{1, []byte{0x6a}}}},
			{"everything to a third party", p, []out{{1, tokenP2pkh(assetA, p.a, userPkh)}, {1, tokenP2pkh(assetB, p.b, userPkh)}}},
		} {
			c := c
			t.Run(fmt.Sprintf("bps %v: %s", bps, c.name), func(t *testing.T) {
				s := f.close(c.q)
				if c.outs != nil {
					s.outs = c.outs
				}
				mustPass(t, advH(t, f, s))
				for _, k := range []*ec.PrivateKey{c.q.validator, validatorIdentity, key(0x31), advNext(c.q.validator)} {
					mustFailPool(t, advH(t, f, advWithSigner(s, k)))
				}
			})
		}
	}
}

// --- Rúnar main (HEAD) vs the Rúnar pinned in go.mod ---
//
// HEAD is Rúnar v1 main, the compiler the contract requires (go.work points
// at it); the pinned compiler is the one go.mod names (GOWORK=off). Every
// test here passes on both: where they differ the test asserts HEAD's
// behaviour and records the pinned one on an ADV-RECORD line
// (`go test -v -run TestAdvHead ./pool/pair/ | grep ADV-RECORD`).

type advState struct {
	a, b                                int64
	lp, val, id, nonce, feeA, feeB, aff []byte
}

func advStateOf(p pair, aff []byte) advState {
	val := make([]byte, 33)
	if !p.rescinded {
		val = p.validator.PubKey().Compressed()
	}
	return advState{a: p.a, b: p.b, lp: p.lp.PubKey().Compressed(), val: val,
		id: validatorIdentity.PubKey().Compressed(), nonce: nonce, feeA: lpFeeAPkh, feeB: lpFeeBPkh, aff: aff}
}

// advSDKScript is the SDK's locking script (code || OP_RETURN || state) for
// this state and f's readonly args; an SDK panic comes back as an error.
func (f *fixture) advSDKScript(t testing.TB, s advState) (full []byte, err error) {
	t.Helper()
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("SDK panic: %v", r)
		}
	}()
	sa := advArt(t).sa
	h := hex.EncodeToString
	c := runar.NewRunarContract(&sa, []interface{}{
		s.a, s.b, h(s.lp), h(s.val), h(s.id), h(s.nonce), h(s.feeA), h(s.feeB), h(s.aff),
		h(assetA), h(assetB), h(f.advVaultHash()), f.bps[0], f.bps[1], f.bps[2],
	})
	return hex.DecodeString(c.GetLockingScript())
}

// advSDKTail is OP_RETURN || state as the SDK frames it.
func (f *fixture) advSDKTail(t testing.TB, s advState) []byte {
	t.Helper()
	full, err := f.advSDKScript(t, s)
	if err != nil {
		t.Fatal(err)
	}
	code := advCodeFor(t, assetA, assetB, f.advVaultHash(), f.bps)
	if !bytes.HasPrefix(full, code) || full[len(code)] != 0x6a {
		t.Fatal("SDK script does not start with its own code part")
	}
	return full[len(code):]
}

// advSDKLock is the pool output for s: A's prefix, f.code, the SDK's tail.
func (f *fixture) advSDKLock(t testing.TB, s advState) []byte {
	t.Helper()
	return append(append(tokenPrefix(assetA, s.a), f.code...), f.advSDKTail(t, s)...)
}

// advHandSplice instantiates the template as an off-chain builder that knows
// constructorSlots and codeSepIndexSlots but not codePartLenSlots would; it
// returns the code and the built-code offsets of the template's length fields.
func advHandSplice(t testing.TB, f *fixture) (code []byte, pins []int) {
	t.Helper()
	a := advArt(t)
	type sub struct {
		off int
		enc []byte
	}
	var subs []sub
	for _, cs := range a.CodeSepIndexSlots {
		if cs.CodeSepIndex != 1 || a.template[cs.ByteOffset] != 0x00 {
			t.Fatalf("codeSepIndex slot %+v", cs)
		}
		subs = append(subs, sub{cs.ByteOffset, []byte{0x51}})
	}
	for _, s := range a.ConstructorSlots {
		if a.template[s.ByteOffset] != 0x00 {
			t.Fatalf("constructor slot %+v is not an OP_0 placeholder", s)
		}
		var enc []byte
		switch s.ParamIndex {
		case 9:
			enc = pushData(assetA)
		case 10:
			enc = pushData(assetB)
		case 11:
			enc = pushData(f.advVaultHash())
		case 12, 13, 14:
			enc = pushNum(f.bps[s.ParamIndex-12])
		default:
			t.Fatalf("unexpected constructor slot param %d", s.ParamIndex)
		}
		subs = append(subs, sub{s.ByteOffset, enc})
	}
	for _, pin := range a.CodePartLenSlots {
		shift := 0
		for _, s := range subs {
			if s.off < pin.ByteOffset {
				shift += len(s.enc) - 1
			}
		}
		pins = append(pins, pin.ByteOffset+shift)
	}
	for i := 1; i < len(subs); i++ { // descending by offset
		for j := i; j > 0 && subs[j].off > subs[j-1].off; j-- {
			subs[j], subs[j-1] = subs[j-1], subs[j]
		}
	}
	code = append([]byte{}, a.template...)
	for _, s := range subs {
		code = append(append(append([]byte{}, code[:s.off]...), s.enc...), code[s.off+1:]...)
	}
	return code, pins
}

// advPins finds the template's code-part length checks: 04 <LE len>
// OP_BIN2NUM then OP_NUMEQUAL OP_VERIFY (an exact pin, eq) or
// OP_GREATERTHANOREQUAL OP_VERIFY (a lower bound). It returns the offsets of
// the length fields and the value they hold.
func advPins(tpl []byte) (eq, ge []int, value int) {
	for i := 0; i+8 <= len(tpl); i++ {
		if tpl[i] != 0x04 || tpl[i+5] != 0x81 || tpl[i+7] != 0x69 || (tpl[i+6] != 0x9c && tpl[i+6] != 0xa2) {
			continue
		}
		v := int(tpl[i+1]) | int(tpl[i+2])<<8 | int(tpl[i+3])<<16 | int(tpl[i+4])<<24
		if v < len(tpl)/2 || v > 2*len(tpl) {
			continue // not a code-part length
		}
		if tpl[i+6] == 0x9c {
			eq = append(eq, i+1)
		} else {
			ge = append(ge, i+1)
		}
		value = v
	}
	return eq, ge, value
}

// advBound is the length the compiled template's check holds (the pinned
// lower bound; at HEAD the value a deployer that does not patch leaves).
func advBound(t testing.TB) int {
	_, _, v := advPins(advArt(t).template)
	if v == 0 {
		t.Fatal("no code-part length check in the template")
	}
	return v
}

func TestAdvHead_ToolchainShape(t *testing.T) {
	a := advArt(t)
	f := advFix(t, [3]int64{30, 5, 10})
	eq, ge, v := advPins(a.template)
	t.Logf("ADV-RECORD %s | template %d bytes, compiled length check holds %d, SDK code %d bytes, codePartLenSlots %v, exact pins at %v, lower bounds at %v",
		advToolchain(t), len(a.template), v, len(f.code), a.CodePartLenSlots, eq, ge)
	if !bytes.HasPrefix(a.template, []byte{0x61, 0xab}) {
		t.Fatalf("template starts %x", a.template[:2])
	}
	if a.head {
		if len(eq) != 3 || len(ge) != 0 || len(a.CodePartLenSlots) != 3 {
			t.Fatalf("HEAD: %d exact pins, %d lower bounds, %d slots", len(eq), len(ge), len(a.CodePartLenSlots))
		}
		for i, s := range a.CodePartLenSlots {
			if s.ByteOffset != eq[i] {
				t.Fatalf("slot %d is not at an exact pin (%v)", s.ByteOffset, eq)
			}
		}
	} else {
		if len(ge) != 3 || len(eq) != 0 {
			t.Fatalf("pinned: %d lower bounds, %d exact pins", len(ge), len(eq))
		}
		// The bound is below the deployed code's length (the AssetIds are
		// spliced in at a width the compiler does not know): _codePart cuts
		// inside the code above the bound clear the length check.
		t.Logf("ADV-RECORD pinned | lower bound %d < code %d: in-code cuts in [%d, %d) clear the length check", v, len(f.code), v, len(f.code))
	}
}

// At HEAD the SDK patches each length field to the deployed code's length.
func TestAdvHead_SDKPoolPinsItsCodeLength(t *testing.T) {
	for _, bps := range [][3]int64{{0, 0, 0}, {30, 5, 10}, {16, 17, 1}, {10000, 0, 0}} {
		f := advFix(t, bps)
		_, pins := advHandSplice(t, f)
		if advIsHead(t) {
			if len(pins) != 3 {
				t.Fatalf("%d pins", len(pins))
			}
			for _, off := range pins {
				got := int(f.code[off]) | int(f.code[off+1])<<8 | int(f.code[off+2])<<16 | int(f.code[off+3])<<24
				if f.code[off-1] != 0x04 || got != len(f.code) {
					t.Fatalf("bps %v pin at %d: %x (value %d, code %d bytes)", bps, off, f.code[off-1:off+7], got, len(f.code))
				}
			}
		}
		p := fresh()
		mustPass(t, advH(t, f, f.close(p)))
		rs, _ := f.rescind(p)
		mustPass(t, advH(t, f, rs))
		if bps[0] < 10000 {
			s, _ := f.swap(p, 40_000, true)
			mustPass(t, advH(t, f, s))
		}
	}
}

// An off-chain builder that splices constructor args at constructorSlots and
// resolves codeSepIndexSlots, knowing nothing of codePartLenSlots, leaves the
// template's length in every pin at HEAD: every method fails, Close included,
// and token A and token B sent to such a pair are locked for good. Patching
// the three length fields gives the SDK's bytes.
func TestAdvHead_HandSplicedCodeLocksBothReserves(t *testing.T) {
	a := advArt(t)
	for _, bps := range [][3]int64{{0, 0, 0}, {30, 5, 10}, {16, 17, 1}} {
		bps := bps
		t.Run(fmt.Sprintf("bps %v", bps), func(t *testing.T) {
			f := advFix(t, bps)
			hand, pins := advHandSplice(t, f)
			if len(hand) != len(f.code) {
				t.Fatalf("hand-spliced %d bytes, SDK %d", len(hand), len(f.code))
			}
			patched := append([]byte{}, hand...)
			for _, off := range pins {
				n := len(patched)
				patched[off], patched[off+1], patched[off+2], patched[off+3] = byte(n), byte(n>>8), byte(n>>16), byte(n>>24)
			}
			if !a.head {
				if !bytes.Equal(hand, f.code) {
					t.Fatal("pinned: the hand splice differs from the SDK code")
				}
			} else {
				if bytes.Equal(hand, f.code) {
					t.Fatal("HEAD: the hand splice equals the SDK code")
				}
				for i := range hand {
					if hand[i] == f.code[i] {
						continue
					}
					inPin := false
					for _, off := range pins {
						inPin = inPin || (i >= off && i < off+4)
					}
					if !inPin {
						t.Fatalf("hand splice differs outside the length fields at %d", i)
					}
				}
				for _, off := range pins {
					if v := int(hand[off]) | int(hand[off+1])<<8; v != advBound(t) {
						t.Fatalf("hand-spliced pin at %d holds %d, want the template's %d", off, v, advBound(t))
					}
				}
			}
			if !bytes.Equal(patched, f.code) {
				t.Fatal("patching the length fields does not give the SDK's code")
			}
			g := *f
			g.code = hand
			p := fresh()
			sw, _ := g.swap(p, 40_000, true)
			rs, _ := g.rescind(p)
			for i, s := range []spend{sw, g.close(p), rs} {
				advCheck(t, fmt.Sprintf("bps %v hand-spliced pair: %s", bps, advMethodNames[i]), advH(t, &g, s), advFail, advPass)
			}
			h := *f
			h.code = patched
			mustPass(t, advH(t, &h, h.close(p)))
		})
	}
}

func advFlip(b []byte, i int) []byte {
	c := append([]byte{}, b...)
	c[i] ^= 0x01
	return c
}

// _codePart tampering on an SDK-built pair, every method.
func TestAdvHead_CodePartTampering(t *testing.T) {
	a := advArt(t)
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	sw, _ := f.swap(p, 40_000, true)
	rs, _ := f.rescind(p)
	calls := []spend{sw, f.close(p), rs}
	for _, s := range calls {
		mustPass(t, advRun(t, f, s, advOpts{codePart: f.code}))
	}
	other := advCodeFor(t, bytes.Repeat([]byte{0xc7}, 32), assetB, f.advVaultHash(), f.bps)
	for _, tc := range []struct {
		name string
		cp   []byte
	}{
		{"truncated by 1", f.code[:len(f.code)-1]},
		{"extended by 00", append(append([]byte{}, f.code...), 0x00)},
		{"extended by 6a", append(append([]byte{}, f.code...), 0x6a)},
		{"first byte flipped", advFlip(f.code, 0)},
		{"middle byte flipped", advFlip(f.code, len(f.code)/2)},
		{"last byte flipped", advFlip(f.code, len(f.code)-1)},
		{"empty", []byte{}},
		{"the template", a.template},
		{"another pool's code (other AssetIdA)", other},
	} {
		for i, s := range calls {
			tc, s := tc, s
			t.Run(tc.name+": "+advMethodNames[i], func(t *testing.T) {
				advCheck(t, "codePart "+tc.name+" "+advMethodNames[i], advRun(t, f, s, advOpts{codePart: tc.cp}), advFail, advRecord)
			})
		}
	}
	// Extended by one byte where the byte after it is 0x6a too: ReserveA's
	// low byte 0x6a.
	t.Run("extended by 6a with ReserveA's low byte 0x6a", func(t *testing.T) {
		q := fresh()
		q.a = 0x4c4b6a
		sw, _ := f.swap(q, 40_000, true)
		rs, _ := f.rescind(q)
		for i, s := range []spend{sw, f.close(q), rs} {
			mustPass(t, advH(t, f, s))
			advCheck(t, "codePart code||6a, ReserveA low byte 6a: "+advMethodNames[i], advRun(t, f, s, advOpts{codePart: append(append([]byte{}, f.code...), 0x6a)}), advFail, advRecord)
		}
	})
}

// advCutRecord collects pinned code-part-cut acceptances for the summary log.
type advCutRecord struct {
	mu   sync.Mutex
	hits []string
}

func (c *advCutRecord) add(s string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.hits = append(c.hits, s)
}

// advCutClose runs the LP's Close of the pool whose lock is lock, with
// _codePart cut at k (the script after its prefix, body[:k]) and signed by k.
func advCutClose(t *testing.T, f *fixture, p pair, lock []byte, k int, signer *ec.PrivateKey) result {
	t.Helper()
	s := advCopy(f.close(p))
	s.ins[0].lock = lock
	s.signer = signer
	thief := pkh(signer)
	s.outs = []out{{1, tokenP2pkh(assetA, p.a, thief)}, {1, tokenP2pkh(assetB, p.b, thief)}}
	body := lock[len(tokenPrefix(assetA, p.a)):]
	return advRun(t, f, s, advOpts{codePart: body[:k]})
}

// On pinned, _codePart may run past the code into the state (any cut k >= the
// template length with script[k] == 0x6a clears the lower bound), and the
// state is then read from script[k+1:], every field moved by j+1 bytes for a
// cut at state byte j. Here LpPubKey is at state byte 16, so a key with 0x6a
// at byte 16 moves the next key onto LpPubKey: LpPubKey[16] = 0x6a lets the
// ValidatorPubKey holder Close the LP's pair, ValidatorPubKey[16] = 0x6a lets
// the ValidatorIdentity holder Close it. Byte 24 (Pool's aligning
// byte) moves the fields 41 bytes here: a window no one holds.
// Every 0x6a state byte of each pool below is cut, for key bytes 1..32 of
// both keys; Close is the oracle (no continuation), signed by the LP, the
// validator, the identity key, and whoever holds the moved LpPubKey window.
// HEAD's equality pin must reject every cut.
func TestAdvHead_CodePartRunIntoState(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	known := map[string]*ec.PrivateKey{}
	names := map[string]string{}
	addKnown := func(name string, k *ec.PrivateKey) {
		known[string(k.PubKey().Compressed())] = k
		names[string(k.PubKey().Compressed())] = name
	}
	var rec advCutRecord
	type pl struct {
		name string
		p    pair
	}
	var pools []pl
	pools = append(pools, pl{"the fresh pool", fresh()})
	for b := 1; b < 33; b++ {
		kb := advKeyWithByte(t, b, 0x6a)
		q := fresh()
		q.lp = kb
		pools = append(pools, pl{fmt.Sprintf("LpPubKey byte %d = 6a", b), q})
		q = fresh()
		q.validator = kb
		pools = append(pools, pl{fmt.Sprintf("ValidatorPubKey byte %d = 6a", b), q})
	}
	cuts, runs := 0, 0
	for _, x := range pools {
		p := x.p
		addKnown("LP", p.lp)
		addKnown("validator", p.validator)
		addKnown("identity", validatorIdentity)
		lock := f.poolLock(p)
		state := p.state()
		for j := range state {
			if state[j] != 0x6a {
				continue
			}
			cuts++
			k := len(f.code) + 1 + j
			signers := []*ec.PrivateKey{p.lp, p.validator, validatorIdentity}
			holder := ""
			if s := j + 1; s+advOffLp+33 <= len(state) {
				if hk, ok := known[string(state[s+advOffLp:s+advOffLp+33])]; ok {
					holder = names[string(hk.PubKey().Compressed())]
					dup := false
					for _, sg := range signers {
						dup = dup || sg == hk
					}
					if !dup {
						signers = append(signers, hk)
					}
				}
			}
			for _, sg := range signers {
				runs++
				r := advCutClose(t, f, p, lock, k, sg)
				who := names[string(sg.PubKey().Compressed())]
				name := fmt.Sprintf("%s: Close with _codePart cut at state byte %d (fields moved %d bytes; moved LpPubKey held by %q), signed by %s", x.name, j, j+1, holder, who)
				if r.pool == nil {
					rec.add(name)
				}
				if advIsHead(t) && r.pool == nil {
					t.Errorf("HEAD accepted: %s", name)
				}
				named := x.name == "the fresh pool" || strings.Contains(x.name, "byte 16 ") || strings.Contains(x.name, "byte 24 ")
				if r.pool == nil || holder != "" || named {
					t.Logf("ADV-RECORD %s | %s | pool=%v", advToolchain(t), name, advErrS(r.pool))
				}
			}
			// Swap and Rescind under the same cut, with the honest
			// continuation (not what a shifted state would write: recorded
			// on pinned, rejected at HEAD).
			if x.name != "the fresh pool" && !strings.Contains(x.name, "byte 16 ") && !strings.Contains(x.name, "byte 24 ") {
				continue
			}
			sw, _ := f.swap(p, 40_000, true)
			rs, _ := f.rescind(p)
			body := lock[len(tokenPrefix(assetA, p.a)):]
			for mi, m := range []spend{sw, rs} {
				for _, sg := range []*ec.PrivateKey{p.validator, validatorIdentity} {
					runs++
					r := advRun(t, f, advWithSigner(m, sg), advOpts{codePart: body[:k]})
					name := fmt.Sprintf("%s: %s with _codePart cut at state byte %d, honest continuation, signed by %s", x.name, []string{"Swap", "Rescind"}[mi], j, names[string(sg.PubKey().Compressed())])
					if r.pool == nil {
						rec.add(name)
						if advIsHead(t) {
							t.Errorf("HEAD accepted: %s", name)
						}
					}
					t.Logf("ADV-RECORD %s | %s | pool=%v", advToolchain(t), name, advErrS(r.pool))
				}
			}
		}
	}
	t.Logf("ADV-RECORD %s | %d pools, %d state cuts, %d runs (Close for all; Swap and Rescind for the fresh, byte-16 and byte-24 pools), %d accepted", advToolchain(t), len(pools), cuts, runs, len(rec.hits))
	for _, h := range rec.hits {
		t.Logf("ADV-RECORD %s | ACCEPTED: %s", advToolchain(t), h)
	}
}

// The validator rotates to a next key whose byte 16 is 0x6a with one ordinary
// Swap (the contract never checks the bytes; raw bytes need no grinding, a
// real key ~256 tries), then the identity key Closes with a cut at state byte
// 65. The Swap is honest on both toolchains; the theft must fail at HEAD.
func TestAdvHead_ValidatorRotatesThenIdentityClosesViaCut(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	raw := append([]byte{0x02}, bytes.Repeat([]byte{0x11}, 32)...)
	raw[16] = 0x6a
	for _, nk := range []struct {
		name string
		b    []byte
	}{{"a ground real key", advKeyWithByte(t, 16, 0x6a).PubKey().Compressed()}, {"raw bytes", raw}} {
		nk := nk
		t.Run(nk.name, func(t *testing.T) {
			s, r := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: true, nextRaw: nk.b})
			mustPass(t, advH(t, f, s))
			after := r.after
			lock := f.advLockState(after.a, advStateVal(after, nk.b))
			k := len(f.code) + 1 + advOffVal + 16
			body := lock[len(tokenPrefix(assetA, after.a)):]
			if body[k] != 0x6a {
				t.Fatalf("byte %d is %#x", k, body[k])
			}
			ctl := advCopy(f.close(after))
			ctl.ins[0].lock = lock
			mustPass(t, advH(t, f, ctl))
			mustFailPool(t, advH(t, f, advWithSigner(ctl, validatorIdentity)))
			advCheck(t, "theft: Swap to a next key with byte 16 = 6a, then identity Close via a cut at state byte 65 ("+nk.name+")",
				advCutClose(t, f, after, lock, k, validatorIdentity), advFail, advRecord)
		})
	}
}

// On pinned the lower bound lies inside this contract's code: every 0x6a
// byte of the code at or above it is a cut the length check accepts, the
// "state" then read from the code's own bytes. AssetIdA and AssetIdB of 32
// 0x6a bytes multiply the candidates. Close by the LP, the validator and the
// identity key; recorded on pinned, rejected at HEAD.
func TestAdvHead_CodePartCutInsideCodeAboveTheBound(t *testing.T) {
	base := advFix(t, [3]int64{30, 5, 10})
	six := bytes.Repeat([]byte{0x6a}, 32)
	for _, v := range []struct {
		name string
		a, b []byte
	}{{"SDK asset ids", assetA, assetB}, {"AssetIdA = AssetIdB = 32 x 6a", six, six}} {
		v := v
		t.Run(v.name, func(t *testing.T) {
			g := *base
			g.code = advCodeFor(t, v.a, v.b, base.advVaultHash(), base.bps)
			p := fresh()
			lock := append(append(tokenPrefix(v.a, p.a), g.code...), 0x6a)
			lock = append(lock, p.state()...)
			ctl := advCopy(g.close(p))
			ctl.ins[0].lock = lock
			mustPass(t, advH(t, &g, ctl))
			n, acc := 0, 0
			for k := advBound(t); k < len(g.code); k++ {
				if g.code[k] != 0x6a {
					continue
				}
				n++
				for _, sg := range []*ec.PrivateKey{p.lp, p.validator, validatorIdentity} {
					s := advCopy(ctl)
					s.signer = sg
					body := lock[len(tokenPrefix(v.a, p.a)):]
					r := advRun(t, &g, s, advOpts{codePart: body[:k]})
					if r.pool == nil {
						acc++
						t.Logf("ADV-RECORD %s | ACCEPTED: in-code cut at %d (%s)", advToolchain(t), k, v.name)
						if advIsHead(t) {
							t.Errorf("HEAD accepted an in-code cut at %d", k)
						}
					}
				}
			}
			t.Logf("ADV-RECORD %s | %s: %d in-code 0x6a cuts in [%d, %d), %d accepted", advToolchain(t), v.name, n, advBound(t), len(g.code), acc)
		})
	}
}

// A fake state hidden in the Affirmation: 0x6a || a complete state whose
// LpPubKey is the thief's. On pinned a cut at that 0x6a reads the fake state
// (trailing bytes dropped), so whoever chose the Affirmation Closes the pair.
// Off-chain check carrying the weight on pinned: the lookup bounds and
// validates the Affirmation (a DER signature cannot carry this). HEAD's
// equality pin rejects it. The Affirmation is >= 256 bytes so the honest LP
// Close works on both toolchains (128..255 misparse on pinned, see below).
func TestAdvHead_FakeStateInsideTheAffirmation(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	thief := key(0x5b)
	fake := advStateOf(p, nil)
	fake.lp = thief.PubKey().Compressed()
	var fs []byte
	fs = append(fs, p.state()[:16]...)
	for _, b := range [][]byte{fake.lp, fake.val, fake.id, fake.nonce, fake.feeA, fake.feeB} {
		fs = append(fs, b...)
	}
	fs = append(fs, 0x00) // an empty Affirmation
	aff := append(bytes.Repeat([]byte{0x30}, 8), 0x6a)
	aff = append(aff, fs...)
	for len(aff) < 300 {
		aff = append(aff, 0x31)
	}
	st := advStateOf(p, aff)
	lock := f.advSDKLock(t, st)
	ctl := advCopy(f.close(p))
	ctl.ins[0].lock = lock
	mustPass(t, advH(t, f, ctl))
	mustFailPool(t, advH(t, f, advWithSigner(ctl, thief)))
	body := lock[len(tokenPrefix(assetA, p.a)):]
	k := bytes.Index(body[len(f.code)+1+advOffAffLen:], append([]byte{0x6a}, fs[:8]...)) + len(f.code) + 1 + advOffAffLen
	if body[k] != 0x6a || !bytes.Equal(body[k+1:k+1+len(fs)], fs) {
		t.Fatal("fake state not found where expected")
	}
	advCheck(t, "theft: Close by the Affirmation's chooser via a cut at a fake state inside the Affirmation",
		advCutClose(t, f, p, lock, k, thief), advFail, advRecord)
}

// Swap with a nextValidatorPubKey that is not 33 bytes. HEAD's state writer
// asserts the width. Pinned writes it raw, poolScript taking the
// continuation's code as scriptCode minus the NEW state's length, so a width
// w moves 33-w bytes between the code region and the state.
func TestAdvHead_SwapNextValidatorKeyWidth(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 0})
	p := fresh()
	lock := f.poolLock(p)
	body := lock[len(tokenPrefix(assetA, p.a)):]
	nk := advNext(p.validator)
	for _, w := range []int{0, 1, 32, 34, 65} {
		w := w
		t.Run(fmt.Sprintf("%d bytes", w), func(t *testing.T) {
			var b []byte
			switch w {
			case 65:
				b = nk.PubKey().Uncompressed()
			case 34:
				b = append(nk.PubKey().Compressed(), 0x00)
			default:
				b = nk.PubKey().Compressed()[:w]
			}
			s, r := advBuildSwap(f, p, advSwap{amountIn: 40_000, aIn: true, nextRaw: b})
			newState := advStateVal(r.after, b)
			keep := len(f.code) + 1 + 33 - w
			written := append(append(tokenPrefix(assetA, r.after.a), body[:keep]...), newState...)
			naive := f.advLockState(r.after.a, newState)
			var wroteOK bool
			for _, sh := range []struct {
				name string
				s    []byte
			}{{"continuation as poolScript builds it", written}, {"continuation code || 6a || state", naive}} {
				c := advCopy(s)
				c.outs[0].script = sh.s
				res := advH(t, f, c)
				advCheck(t, fmt.Sprintf("Swap nextValidatorPubKey %d bytes, %s", w, sh.name), res, advFail, advRecord)
				if sh.name == "continuation as poolScript builds it" {
					wroteOK = res.ok()
				}
			}
			if advIsHead(t) || !wroteOK {
				return
			}
			// Pinned wrote it: can the LP still Close it?
			next := r.after
			ctl := advCopy(f.close(next))
			ctl.ins[0].lock = written
			advCheck(t, fmt.Sprintf("pinned: LP Close of the pair a %d-byte nextValidatorPubKey Swap wrote", w), advH(t, f, ctl), advFail, advRecord)
			nb := written[len(tokenPrefix(assetA, next.a)):]
			found := false
			for k := advBound(t); k < len(nb); k++ {
				if nb[k] == 0x6a && advRun(t, f, ctl, advOpts{codePart: nb[:k]}).pool == nil {
					found = true
					t.Logf("ADV-RECORD pinned | LP Close of the %d-byte-key pair passes with a %d-byte code part", w, k)
				}
			}
			if !found {
				t.Logf("ADV-RECORD pinned | LP Close of the %d-byte-key pair: no code part works", w)
			}
		})
	}
}

// Rescind writes ValidatorPubKey as exactly 33 zero bytes.
func TestAdvHead_RescindWritesThirtyThreeZeroBytes(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	for _, w := range []int{33, 32, 34} {
		rs, after := f.rescind(p)
		rs.outs[0].script = f.advLockState(after.a, advStateVal(p, make([]byte, w)))
		want := advFail
		if w == 33 {
			want = advPass
		}
		advCheck(t, fmt.Sprintf("Rescind writing %d zero bytes", w), advH(t, f, rs), want, want)
	}
}

// Bytes after the state on the spent pool. HEAD's reader asserts the state is
// consumed: every method rejects. Pinned's reader drops the rest.
func TestAdvHead_TrailingBytesAfterState(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	p := fresh()
	for _, ex := range []struct {
		name  string
		extra []byte
	}{{"one 00 byte", []byte{0x00}}, {"an extra push", []byte{0x02, 0xbe, 0xef}}} {
		ex := ex
		t.Run(ex.name, func(t *testing.T) {
			lock := append(f.poolLock(p), ex.extra...)
			body := lock[len(tokenPrefix(assetA, p.a)):]
			sw, r := f.swap(p, 40_000, true)
			rs, after := f.rescind(p)
			for _, m := range []struct {
				name     string
				s        spend
				newA     int64
				newState []byte
			}{{"Swap", sw, r.after.a, r.after.state()}, {"Close", f.close(p), 0, nil}, {"Rescind", rs, after.a, after.state()}} {
				c := advCopy(m.s)
				c.ins[0].lock = lock
				if m.newState == nil {
					advCheck(t, "trailing "+ex.name+": Close", advH(t, f, c), advFail, advRecord)
					continue
				}
				advCheck(t, "trailing "+ex.name+": "+m.name+", the honest continuation", advH(t, f, c), advFail, advRecord)
				c.outs[0].script = append(append(tokenPrefix(assetA, m.newA), body[:len(f.code)+1+len(ex.extra)]...), m.newState...)
				advCheck(t, "trailing "+ex.name+": "+m.name+", continuation as poolScript builds it", advH(t, f, c), advFail, advRecord)
			}
		})
	}
}

func advAff(n int) []byte {
	b := make([]byte, n)
	for i := range b {
		b[i] = byte(0x30 + i%7) // no 0x6a
	}
	return b
}

var advAffSizes = []int{0, 1, 71, 72, 73, 75, 76, 127, 128, 129, 255, 256}

// The SDK's Affirmation framing: OP_0 when empty, a direct push below 76,
// PUSHDATA1 to 255, PUSHDATA2 above.
func TestAdvHead_AffirmationSDKFraming(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	for _, n := range advAffSizes {
		tail := f.advSDKTail(t, advStateOf(fresh(), advAff(n)))
		frame := tail[1+advOffAffLen : len(tail)-n]
		var want []byte
		switch {
		case n == 0:
			want = []byte{0x00}
		case n < 0x4c:
			want = []byte{byte(n)}
		case n <= 0xff:
			want = []byte{0x4c, byte(n)}
		default:
			want = []byte{0x4d, byte(n), byte(n >> 8)}
		}
		if !bytes.Equal(frame, want) || !bytes.HasSuffix(tail, advAff(n)) {
			t.Errorf("%d bytes: framing %x, want %x", n, frame, want)
		}
	}
}

// Swap (both directions) -> second Swap -> Rescind -> Close, and Close
// directly, per Affirmation size, every continuation framed by the SDK.
// HEAD: everything passes. Pinned: recorded.
func TestAdvHead_AffirmationSizesLifecycle(t *testing.T) {
	f := advFix(t, [3]int64{30, 5, 10})
	for _, n := range advAffSizes {
		n := n
		aff := advAff(n)
		lockOf := func(p pair) []byte { return f.advSDKLock(t, advStateOf(p, aff)) }
		at := func(s spend, p pair) spend {
			s = advCopy(s)
			s.ins[0].lock = lockOf(p)
			return s
		}
		t.Run(fmt.Sprintf("%d bytes", n), func(t *testing.T) {
			p := fresh()
			advCheck(t, fmt.Sprintf("Affirmation %d: Close", n), advH(t, f, at(f.close(p), p)), advPass, advRecord)
			for _, aIn := range []bool{true, false} {
				s1, r1 := f.swap(p, 40_000, aIn)
				s1 = at(s1, p)
				s1.outs[0].script = lockOf(r1.after)
				res := advH(t, f, s1)
				advCheck(t, fmt.Sprintf("Affirmation %d: Swap %s", n, advDir(aIn)), res, advPass, advRecord)
				if !res.ok() {
					continue
				}
				p2 := r1.after
				s2, r2 := f.swap(p2, 7_000, !aIn)
				s2 = at(s2, p2)
				s2.outs[0].script = lockOf(r2.after)
				advCheck(t, fmt.Sprintf("Affirmation %d: Swap %s, Swap", n, advDir(aIn)), advH(t, f, s2), advPass, advRecord)
				p3 := r2.after
				s3, p4 := f.rescind(p3)
				s3 = at(s3, p3)
				s3.outs[0].script = lockOf(p4)
				advCheck(t, fmt.Sprintf("Affirmation %d: Swap %s, Swap, Rescind", n, advDir(aIn)), advH(t, f, s3), advPass, advRecord)
				advCheck(t, fmt.Sprintf("Affirmation %d: Swap %s, Swap, Rescind, Close", n, advDir(aIn)), advH(t, f, at(f.close(p4), p4)), advPass, advRecord)
			}
		})
	}
}
