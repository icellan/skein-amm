//go:build integration

package regtest

import (
	"testing"

	ec "github.com/bsv-blockchain/go-sdk/primitives/ec"
	sighash "github.com/bsv-blockchain/go-sdk/transaction/sighash"
)

// Spends the NODE must refuse. Each is an honest spend with one
// defect (fully funded and value-balanced, every coin input signed), so the
// node's reason is a script's, not bad-txns-in-belowout. Before each
// broadcast the go-sdk interpreter must name exactly the contract inputs the
// case expects to fail (reject's failing indices). After each rejection the
// pool and vault UTXOs of every pair involved are checked unspent, and the
// honest spend of that same pair is broadcast and must be accepted: the
// harness is not the cause.

// Swap defects. Each fails the pool (input 0) alone; the vault
// (input 1) has nothing to object to, its pool being input 0.
func TestSwapRejected(t *testing.T) {
	t.Parallel()
	e := newEnv(t)
	pr := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))

	cases := []struct {
		name   string
		aIn    bool
		mutate func(t *testing.T, s *spend, r *swapPlan)
	}{
		{"payout +1 token", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs[2].script = tokenP2pkh(pr.p.assetB, r.out+1, pkh(r.user))
		}},
		{"payout +1 token (B-in)", false, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs[2].script = tokenP2pkh(pr.p.assetA, r.out+1, pkh(r.user))
		}},
		{"vault one token short", true, func(t *testing.T, s *spend, r *swapPlan) {
			a := r.after
			a.b--
			s.outs[1].script = vaultScript(pr.p, pr.vault, a)
		}},
		{"vault replaced by a token-B P2PKH", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs[1].script = tokenP2pkh(pr.p.assetB, r.after.b, pkh(newKey(t)))
		}},
		{"vault output missing", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs = append(s.outs[:1], s.outs[2:]...)
		}},
		{"pool and vault outputs swapped", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs[0], s.outs[1] = s.outs[1], s.outs[0]
		}},
		{"signed by a key that is not the validator's", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.ins[0].signer = newKey(t)
		}},
		{"validator fee output missing", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs = append(s.outs[:4], s.outs[5:]...)
		}},
		{"an extra output after the contract's", true, func(t *testing.T, s *spend, r *swapPlan) {
			s.outs = append(s.outs, out{1_000, p2pkhScript(pkh(newKey(t)))})
		}},
		{"ReserveB in state one more than the vault's prefix", true, func(t *testing.T, s *spend, r *swapPlan) {
			a := r.after
			a.b++
			s.outs[0].script = poolScript(pr.p, pr.code, a)
		}},
		// The continuation carries the 32-byte key in state (one byte
		// shorter). That is not necessarily the script's own continuation
		// (poolScript cuts the code by Len(state)), so this shows the node
		// refuses this spend, not that no continuation could pass.
		{"nextValidatorPubKey of 32 bytes", true, func(t *testing.T, s *spend, r *swapPlan) {
			short := r.next.PubKey().Compressed()[:32]
			s.ins[0].args[0] = pushData(short)
			a := r.after
			a.validatorRaw = short
			s.outs[0].script = poolScript(pr.p, pr.code, a)
		}},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			e := e.sub(t)
			r := planSwap(t, pr, 20_000, c.aIn)
			s := swapSpend(pr, r)
			s.label = "BAD swap: " + c.name
			c.mutate(t, s, r)
			e.reject(s, consensusReject, 0)
			e.swap(pr, planSwap(t, pr, 20_000, c.aIn)) // the honest spend of the same pair
		})
	}
	e.close(pr)
}

// a pool deployed with 5,000 sats; the continuation one
// sat short, that sat routed to Rúnar's change (with a matching
// _changeAmount), so the transaction balances and only the pool's rule
// refuses it.
func TestSwapRejected_PoolSatSkimmed(t *testing.T) {
	t.Parallel()
	e := newEnv(t)
	st := newPairState(t)
	st.sats = 5_000
	pr := e.deploySDK(newParams(t, 30, 5, 10, 71), st)
	plan := func() (*swapPlan, *spend) {
		r := planSwap(t, pr, 20_000, true)
		r.satsChangePkh, r.satsChange = pkh(newKey(t)), 1_000
		return r, swapSpend(pr, r)
	}
	_, s := plan()
	s.label = "BAD swap: continuation 1 sat fewer (to Rúnar change)"
	s.outs[0].sats--
	last := len(s.outs) - 1
	s.outs[last].sats++
	s.ins[0].changeSats++
	e.reject(s, consensusReject, 0)
	r, honest := plan()
	e.swapWith(pr, r, honest)
	e.close(pr)
}

// pairingCases are the four ways of parting a pool from its vault, applied to
// an honest spend of pr (pool at 0, vault at 1, coins after): the contract
// inputs each is expected to fail, by index.
func pairingCases(foreign *pair) []struct {
	name    string
	edit    func(s *spend)
	failing []int
} {
	return []struct {
		name    string
		edit    func(s *spend)
		failing []int
	}{
		{"without the vault input (a coin at input 1)", func(s *spend) {
			s.ins = append(s.ins[:1], s.ins[2:]...)
		}, []int{0}},
		{"a foreign vault (another deployed pair's) at input 1", func(s *spend) {
			s.ins[1] = vaultIn(foreign)
		}, []int{0, 1}},
		{"its vault at input 2", func(s *spend) {
			s.ins = append([]*input{s.ins[0], s.ins[2], s.ins[1]}, s.ins[3:]...)
		}, []int{0, 2}},
		{"the pool at input 1 (its vault at 0)", func(s *spend) {
			s.ins[0], s.ins[1] = s.ins[1], s.ins[0]
		}, []int{0, 1}},
	}
}

// each of Swap, Rescind and Close with the pool and its vault
// parted, on its own pair; a second deployed pair supplies the foreign vault.
func TestPairingRejected(t *testing.T) {
	t.Parallel()
	e := newEnv(t)
	foreign := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))
	methods := []struct {
		name   string
		honest func(t *testing.T, pr *pair) *spend
		after  func(e *env, pr *pair)
	}{
		{"Swap", func(t *testing.T, pr *pair) *spend { return swapSpend(pr, planSwap(t, pr, 20_000, true)) },
			func(e *env, pr *pair) { e.swap(pr, planSwap(e.t, pr, 20_000, true)); e.close(pr) }},
		{"Rescind", func(t *testing.T, pr *pair) *spend { return rescindSpend(t, pr, 0) },
			func(e *env, pr *pair) { e.rescind(pr, 0); e.close(pr) }},
		{"Close", func(t *testing.T, pr *pair) *spend { return closeSpend(t, pr) },
			func(e *env, pr *pair) { e.close(pr) }},
	}
	for _, m := range methods {
		t.Run(m.name, func(t *testing.T) {
			e := e.sub(t)
			pr := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))
			for _, c := range pairingCases(foreign) {
				t.Run(c.name, func(t *testing.T) {
					s := m.honest(t, pr)
					s.label = "BAD " + m.name + ": " + c.name
					s.watch = []*pair{pr, foreign}
					c.edit(s)
					e.sub(t).reject(s, consensusReject, c.failing...)
				})
			}
			t.Run("the honest "+m.name+" of the same pair", func(t *testing.T) {
				m.after(e.sub(t), pr)
			})
		})
	}
	e.close(foreign)
}

// attempts to take a vault (token B) without its own pool. The victim
// pair V and the attacker's pair X are both deployed here.
func TestVaultTheftRejected(t *testing.T) {
	t.Parallel()
	e := newEnv(t)
	v := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))
	x := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))
	thief := newKey(t)
	steal := out{1, tokenP2pkh(v.p.assetB, v.st.b, pkh(thief))}

	t.Run("the vault spent alone", func(t *testing.T) {
		// Its only sat is the fee; token B burned to a data output. The
		// outputs do not matter to the vault's script, only its inputs.
		s := &spend{
			label: "BAD theft: the vault alone",
			ins:   []*input{vaultIn(v)},
			outs:  []out{{0, []byte{0x00, 0x6a}}},
			watch: []*pair{v},
		}
		e.sub(t).reject(s, consensusReject, 0)
	})
	t.Run("the vault at input 1 after a plain funding input", func(t *testing.T) {
		payer := &coin{lock: p2pkhScript(pkh(thief)), key: thief}
		s := &spend{
			label: "BAD theft: funding input at 0, the vault at 1",
			ins:   []*input{coinIn(payer), vaultIn(v)},
			outs:  []out{steal},
			payer: payer,
			watch: []*pair{v},
		}
		e.sub(t).reject(s, consensusReject, 1)
	})
	t.Run("another pair's pool honestly Closed at input 0, its vault at 1, the victim vault at 2", func(t *testing.T) {
		s := closeSpend(t, x)
		s.label = "BAD theft: X closed + victim vault at 2"
		s.ins = []*input{s.ins[0], s.ins[1], vaultIn(v), s.ins[2]}
		s.outs = append(s.outs, steal)
		s.watch = []*pair{v}
		e.sub(t).reject(s, consensusReject, 2)
	})
	t.Run("another pair's pool Closed at input 0 with the victim vault at 1 in place of its own", func(t *testing.T) {
		s := closeSpend(t, x)
		s.label = "BAD theft: X closed with the victim vault at 1"
		s.ins[1] = vaultIn(v)
		s.outs[1] = steal
		s.watch = []*pair{v, x}
		e.sub(t).reject(s, consensusReject, 0, 1)
	})
	t.Run("the victim's honest Close but the vault's preimage ALL|ANYONECANPAY", func(t *testing.T) {
		s := closeSpend(t, v)
		s.label = "BAD close: vault preimage ALL|ANYONECANPAY|FORKID"
		s.ins[1].flag = sighash.AllForkID | sighash.AnyOneCanPay
		e.sub(t).reject(s, consensusReject, 1)
	})
	t.Run("the attacker's honest Close of its own pair", func(t *testing.T) {
		e.sub(t).close(x)
	})
	t.Run("the victim's honest Close", func(t *testing.T) {
		e.sub(t).close(v)
	})
}

// Close by anyone but the LP; Rescind by the LP; a second Rescind and
// a Swap after Rescind (both by the old validator key).
func TestCloseRejected(t *testing.T) {
	t.Parallel()
	e := newEnv(t)
	pr := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))
	for name, k := range map[string]func() *ec.PrivateKey{
		"signed by the validator": func() *ec.PrivateKey { return pr.st.validator },
		"signed by a random key":  func() *ec.PrivateKey { return newKey(t) },
	} {
		t.Run(name, func(t *testing.T) {
			s := closeSpend(t, pr)
			s.label = "BAD close: " + name
			s.ins[0].signer = k()
			e.sub(t).reject(s, consensusReject, 0)
		})
	}
	t.Run("the LP's Close of the same pair", func(t *testing.T) {
		e.sub(t).close(pr)
	})
}

func TestRescindRejected(t *testing.T) {
	t.Parallel()
	e := newEnv(t)
	pr := e.deploySDK(newParams(t, 30, 5, 10, 71), newPairState(t))
	t.Run("signed by the LP", func(t *testing.T) {
		s := rescindSpend(t, pr, 0)
		s.label = "BAD rescind: LP-signed"
		s.ins[0].signer = pr.st.lp
		e.sub(t).reject(s, consensusReject, 0)
	})
	t.Run("the honest Rescind of the same pair", func(t *testing.T) {
		e.sub(t).rescind(pr, 0)
	})
	t.Run("a second Rescind (old validator key)", func(t *testing.T) {
		s := rescindSpend(t, pr, 0) // signed by pr.st.validator: the key before Rescind
		s.label = "BAD rescind: second rescind"
		e.sub(t).reject(s, consensusReject, 0)
	})
	t.Run("a Swap after Rescind (old validator key)", func(t *testing.T) {
		// swapSpend signs with the old key and pays the validator fee where the
		// script would: Hash160 of the cleared key. The signature is the only
		// defect.
		s := swapSpend(pr, planSwap(t, pr, 20_000, true))
		s.label = "BAD swap after rescind"
		e.sub(t).reject(s, consensusReject, 0)
	})
	t.Run("the LP's Close of the rescinded pair", func(t *testing.T) {
		e.sub(t).close(pr)
	})
}
