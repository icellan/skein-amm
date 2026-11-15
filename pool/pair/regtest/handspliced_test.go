//go:build integration

package regtest

import (
	"bytes"
	"fmt"
	"sort"
	"testing"
)

// a pair whose pool code was built WITHOUT the SDK, from the
// artifact template with the constructor slots spliced (assetIdA, assetIdB,
// VaultCodeHash, the three fee rates) and the codeSepIndex slots set to OP_1, the
// way a non-SDK builder that predates Rúnar's codePartLenSlots would.
// The template's verify_code_part_len fields hold a compile-time lower bound,
// and only the SDK writes the deployed code length into them. A pool deployed
// from such code pins SIZE(_codePart) to a length its real code part does not
// have.
//
// Each method gets its own freshly deployed hand-spliced pair, so one result
// cannot confound another, under two fee sets (the fee pushes' widths move
// the code's bytes). For each, two spends are tried:
//
//   - the honest spend (_codePart = the deployed code), and
//   - the recovery probe: _codePart = the deployed code truncated to the pinned
//     length. Rúnar authenticates _codePart as 61ab || scriptCode[0:SIZE-2], so
//     at the pinned SIZE this genuine prefix is the ONLY _codePart that can
//     pass; if the node refuses it too, no _codePart unlocks the method.
//
// Only the pool input is expected to fail (the vault's rule is about input
// positions, not the pool's code). The vault can move only with its pool, so
// when both spends are refused for Swap, Rescind and Close, BOTH reserves (A
// in the pool, B in the vault) are unrecoverable; the test then passes and
// logs FUNDS LOCKED.
func TestHandSplicedTemplate_FundLock(t *testing.T) {
	t.Parallel()
	c := compiled(t)
	if len(c.tmpl.CodePartLenSlots) == 0 {
		// A Rúnar without codePartLenSlots: the template has no deploy-time length field,
		// so the hand splice must be the SDK's code, and it spends.
		t.Logf("this Rúnar's artifact has no codePartLenSlots: the hand splice should equal the SDK")
		e := newEnv(t)
		pp, st := newParams(t, 30, 5, 10, 71), newPairState(t)
		code := handCode(t, c, pp, false)
		if sdk := sdkCode(t, c, pp, st); !bytes.Equal(code, sdk) {
			t.Fatalf("hand-spliced code differs from the SDK's although there are no codePartLenSlots")
		}
		pr := e.deployCode(pp, st, code, "deploy hand-spliced")
		e.swap(pr, planSwap(t, pr, 20_000, true))
		e.swap(pr, planSwap(t, pr, 20_000, false))
		e.rescind(pr, 0)
		e.close(pr)
		return
	}
	t.Logf("artifact template %d bytes; codePartLenSlots (template offsets): %+v", len(c.raw), c.tmpl.CodePartLenSlots)

	for _, fees := range [][3]int64{{30, 5, 10}, {0, 0, 0}} {
		feeName := fmt.Sprintf("fees %d-%d-%d", fees[0], fees[1], fees[2])
		locked := map[string]bool{}
		for _, method := range []string{"swap", "rescind", "close"} {
			t.Run("unpatched/"+feeName+"/"+method, func(t *testing.T) {
				e := newEnv(t)
				pp, st := newParams(t, fees[0], fees[1], fees[2], 71), newPairState(t)
				code := handCode(t, c, pp, false)
				sdk := sdkCode(t, c, pp, st)
				offs, pins := templateLenPins(t, c, pp)
				if len(code) != len(sdk) || bytes.Equal(code, sdk) {
					t.Fatalf("expected the hand splice to differ from the SDK's code only in the length fields (%d vs %d bytes)", len(code), len(sdk))
				}
				for i := range code {
					if code[i] != sdk[i] && !inField(i, offs) {
						t.Fatalf("hand splice differs from the SDK's code at byte %d, outside the length fields %v", i, offs)
					}
				}
				t.Logf("deployed code is %d bytes; the template's %d verify_code_part_len fields (at %v) pin %v", len(code), len(offs), offs, pins)

				pr := e.deployCode(pp, st, code, "deploy hand-spliced (unpatched)")
				honest := handSplicedSpend(t, pr, method)
				honest.label = fmt.Sprintf("hand-spliced %s, honest _codePart (%d bytes)", method, len(code))
				reason := e.reject(honest, consensusReject, 0)
				t.Logf("HAND-SPLICED %s: honest spend REJECTED: %s", method, reason)

				for _, pin := range distinct(pins) {
					if pin >= len(code) {
						t.Logf("pin %d >= the code's %d bytes: no genuine prefix of that length exists", pin, len(code))
						continue
					}
					sc := scriptCodeAfter(t, pr.poolLock, 0x61)
					probe := handSplicedSpend(t, pr, method)
					probe.ins[0].codePart = append([]byte{}, code[:pin]...)
					probe.label = fmt.Sprintf("hand-spliced %s, recovery probe _codePart = code[:%d]", method, pin)
					t.Logf("probe: scriptCode byte after the claimed code part is %#x (0x6a would satisfy the split check)", sc[pin-2])
					reason := e.reject(probe, consensusReject, 0)
					t.Logf("HAND-SPLICED %s: recovery probe (_codePart truncated to the pinned %d bytes) REJECTED: %s", method, pin, reason)
				}
				if !t.Failed() {
					locked[method] = true
				}
			})
		}
		if locked["swap"] && locked["rescind"] && locked["close"] {
			t.Logf("FUNDS LOCKED (%s): a pair whose pool was deployed from the hand-spliced template (codePartLenSlots left as the template has them) "+
				"cannot be spent by Swap, Rescind or Close, with the honest _codePart or the only other _codePart the pin admits; "+
				"both tokens are unrecoverable: A in the pool, and B in the vault, which moves only with its pool", feeName)
		} else {
			t.Errorf("hand-spliced pair (%s): not every method was refused (locked: %v); see the subtests", feeName, locked)
		}
	}

	t.Run("patched with the deployed length: the SDK's bytes, and it spends", func(t *testing.T) {
		e := newEnv(t)
		pp, st := newParams(t, 30, 5, 10, 71), newPairState(t)
		code := handCode(t, c, pp, true)
		if sdk := sdkCode(t, c, pp, st); !bytes.Equal(code, sdk) {
			t.Fatalf("hand splice + length patch (%d bytes) is not the SDK's code (%d bytes)", len(code), len(sdk))
		}
		pr := e.deployCode(pp, st, code, "deploy hand-spliced + patched")
		e.swap(pr, planSwap(t, pr, 20_000, true))
		e.swap(pr, planSwap(t, pr, 20_000, false))
		e.rescind(pr, 0)
		e.close(pr)
	})
}

// handSplicedSpend is the honest spend of a pair by method name.
func handSplicedSpend(t *testing.T, pr *pair, method string) *spend {
	switch method {
	case "swap":
		return swapSpend(pr, planSwap(t, pr, 20_000, true))
	case "rescind":
		return rescindSpend(t, pr, 0)
	default:
		return closeSpend(t, pr)
	}
}

func inField(i int, offs []int) bool {
	for _, o := range offs {
		if i >= o && i < o+4 {
			return true
		}
	}
	return false
}

func distinct(xs []int) []int {
	m := map[int]bool{}
	var out []int
	for _, x := range xs {
		if !m[x] {
			m[x] = true
			out = append(out, x)
		}
	}
	sort.Ints(out)
	return out
}
