# pool/pair/regtest: the PairPool contract on a real node

On-node tests of `pool/pair/PairPool.runar.go` and `pool/pair/Vault.runar.go`
against a bitcoin-sv regtest node. The suite compiles both contracts from
source with Rúnar, deploys pairs with real transactions, spends them through
Swap, Rescind and Close, mines, and reads the chain back to check the
result. `pool/pair/pair_test.go` covers the same scripts in the go-sdk
interpreter. This suite checks them under the node's consensus rules and
mempool policy.

This is a separate Go module, and every test file has the `integration` build
tag, so the root module's `go test ./...` never builds it.

A pair is two outputs of one transaction, always spent and rewritten
together: output 0 the stateful pool (token A's prefix, the code, the
state), output 1 the keyless vault (token B's prefix, the vault code). A
deploy is one funder transaction with the pool at output 0 and the vault at
output 1. Every spend here has the pool at input 0 and the vault at input 1,
unless a negative case moves them.

## What it proves

- Script validity of both contract inputs, the pool and the vault, under the
  node's consensus rules and standardness policy. The node is configured by
  Rúnar's `integration/regtest.sh`; see the policy list below.
- Every accepted spend's outputs are mined exactly as an independent
  expectation says (value and script, byte for byte). That covers the pool
  continuation (token-A prefix, code, state with both reserves), the vault
  continuation (token-B prefix, vault code), the payout, the fee outputs,
  token change and Rúnar sats change. Each spend consumes the previous pair:
  input 0 spends the previous `txid:0`, input 1 the previous `txid:1`, and
  both UTXOs are gone afterwards.
- Value flow. The pool continuation holds exactly the spent pool's sats, also
  for a pool deployed with 5,000 sats. The vault stays at 1 sat. A funding
  input pays the miner: the contract inputs' sats all go to the contract
  outputs (or, on Close, to the LP's outputs), and the funding input carries
  exactly the fee plus the 1-sat outputs nothing else covers.
- Each negative case is refused by the node with a consensus-level script
  failure (`mandatory-script-verify-flag-failed`). Before the broadcast, the
  go-sdk interpreter has to fail exactly the contract inputs the case names
  (for example, only the vault at input 2), so a harness defect cannot pass
  as a rejection. After the rejection, the pool and vault UTXOs of every pair
  involved are still unspent, and the honest spend of that pair is then
  accepted.
- Every SDK-deployed pool's code equals a build from the artifact template
  done without the SDK: constructor slots spliced (assetIdA, assetIdB,
  vaultCode, the three fee rates), codeSepIndex slots set to `OP_1`, and the
  `codePartLenSlots` fields set to the deployed length. The SDK's vault
  script equals the vault artifact's script (it has no slots).

## What it does not prove

- **Token conservation.** The node knows nothing about BRC-162. A token
  output is just a script with a `0x20 <assetId> <amount> OP_2DROP` prefix,
  and the "token inputs" here are ordinary 1-sat outputs carrying a
  token-prefixed P2PKH script, made by a plain wallet transaction. No token
  amount is checked on chain, in either direction: the pair's script sees no
  token input at all. The validator, which signs every Swap, and the overlays
  check them.
- Mainnet policy. `regtest.sh` overrides the node's defaults:
  `acceptnonstdtxn=0` (standard script flags are enforced at mempool entry),
  `minminingtxfee=0.00000001` (1 sat/kB), `maxscriptsizepolicy=0`,
  `maxtxsizepolicy=0`, `maxscriptnumlengthpolicy=0`,
  `maxstackmemoryusagepolicy`/`consensus=100000000`, and Genesis and
  Chronicle active from height 1. A miner or ARC with stricter size, fee or
  validation-time limits could refuse transactions this node takes. The
  suite pays 100 sat/kB by default (`FEE_RATE_SAT_PER_KB`).
- The validator's and the overlays' rules: affirmation checks, key
  derivation, prefix == state on admission, the canonical VaultCode.
- The 32-byte `nextValidatorPubKey` case builds its continuation with the
  short key in state. That shows the node refuses this spend, not that no
  continuation could pass.

## Running

You need Docker and a Rúnar checkout. By default the checkout is the sibling
`../../../../runar` (next to the main skein-amm checkout); otherwise set
`RUNAR_DIR`.

```sh
cd pool/pair/regtest
./run.sh -v                       # starts the skein-pair node if needed, runs everything, leaves it running
./run.sh -run HandSpliced -v
./run.sh --pinned -v              # compile with the Rúnar the root go.mod pins instead of the checkout
FEE_RATE_SAT_PER_KB=1 ./run.sh -v # the node's floor
./run.sh --stop                   # run everything, then stop the node
```

Or by hand:

```sh
<runar>/integration/regtest.sh start skein-pair   # container runar-integration-regtest-skein-pair, RPC 19741
RPC_URL=http://localhost:19741 GOWORK=off go test -tags integration -count=1 -v .
<runar>/integration/regtest.sh stop skein-pair
<runar>/integration/regtest.sh clean skein-pair   # removes <runar>/integration/regtest-data/skein-pair
```

`go.mod` replaces Rúnar with the relative path `../../../../runar/...`, which
only resolves from the main checkout. `run.sh` writes `go.local.mod` with the
replaces pointing at `RUNAR_DIR` and runs with `-modfile=go.local.mod`, so it
also works from a worktree. `go.local.*` and `go.pinned.*` are generated and
ignored by git.

Environment:

| var | default | |
|---|---|---|
| `RUNAR_DIR` | `../../../../runar` | Rúnar checkout (`regtest.sh`, compiler, SDK) |
| `INSTANCE` | `skein-pair` | regtest.sh instance; `default` = the unnamed one on 18332 |
| `RPC_URL` | `http://localhost:19741` | node RPC (user/pass `RPC_USER`/`RPC_PASS`, default bitcoin/bitcoin) |
| `FEE_RATE_SAT_PER_KB` | `100` | miner fee every transaction pays, deploys included |
| `POOL_SOURCE` | `../PairPool.runar.go` | the pool contract to compile |
| `VAULT_SOURCE` | `../Vault.runar.go` | the vault contract to compile |

The tests are independent: each makes its own keys and asset ids, funds a
fresh key from the node wallet, and deploys its own pairs. You can rerun them
against a long-lived node. `TestMain` mines to height 300 on a fresh chain.
The suite serializes its own mining, because two `generatetoaddress` calls
racing on one tip fork the chain. When the run ends, it prints every
transaction it sent, with size, the unlocking-script sizes of the first pool
and vault inputs, fee and the node's verdict, then the accepted/rejected
counts.

## The cases

| | test |
|---|---|
| deploy {30, 5, 10} + Close round trip | `TestDeployAndClose` |
| fee pair {30, 5, 10}: A-in, B-in, a Swap with token change and Rúnar sats change, 10 chained swaps alternating direction with validator key rotation, Rescind (with Rúnar change), Close sweeping both tokens to token-prefixed P2PKH | `TestLifecycleFeePair` |
| zero-fee pair {0, 0, 0}: both directions (3 outputs each), Close | `TestZeroFeePair` |
| Close on a fresh pair; Close after swaps without Rescind | `TestCloseFreshPair`, `TestCloseAfterSwapsWithoutRescind` |
| affirmation 0, 71, 72 bytes: deploy, Swap, Rescind, Close | `TestAffirmationSizes` |
| a pool deployed with 5,000 sats keeps them through Swaps and Rescind; Close sweeps them | `TestPairWithMoreSats` |
| Swap refused (the pool fails, the vault passes): payout +1 (both directions), vault one token short, vault replaced by a token-B P2PKH, vault missing, pool/vault outputs swapped, wrong validator key, validator fee missing, extra output, ReserveB in state one more than the vault's prefix, 32-byte next key | `TestSwapRejected` |
| Swap refused: continuation 1 sat short of a 5,000-sat pool, the sat routed to Rúnar change | `TestSwapRejected_PoolSatSkimmed` |
| pairing, for each of Swap, Rescind and Close: no vault input (pool fails); a foreign pair's vault at input 1 (both fail); its vault at input 2 (both fail); the pool at input 1, the vault at 0 (both fail) | `TestPairingRejected` |
| vault theft: the vault alone; after a plain funding input; another pair's pool honestly Closed at 0 with its vault at 1 and the victim vault at 2 (only the victim vault fails); another pair's pool Closed with the victim vault at 1 in place of its own (both fail); the victim's honest Close with the vault's preimage ALL\|ANYONECANPAY (only the vault fails) | `TestVaultTheftRejected` |
| Close refused: validator-signed, random key | `TestCloseRejected` |
| Rescind refused: LP-signed; second Rescind; Swap after Rescind | `TestRescindRejected` |
| hand-spliced template (fund lock of both tokens) | `TestHandSplicedTemplate_FundLock` |

### The hand-spliced template

At Rúnar HEAD, PairPool's code has three `verify_code_part_len` fields
(`04 <len:4 LE> OP_BIN2NUM OP_NUMEQUAL OP_VERIFY`). The artifact template
holds a compile-time lower bound in them (the template's own length, 4299
bytes at the time of writing), and only the SDK writes the deployed length
(about 5590 bytes: the vault code is spliced in twice).

`TestHandSplicedTemplate_FundLock` builds pool code from the template the
way a non-SDK builder would: constructor slots spliced, codeSepIndex slots
set to `OP_1`, length fields left alone. It deploys one pair per method,
under fee sets {30, 5, 10} and {0, 0, 0}, and tries two spends on each:

- the honest spend;
- `_codePart` truncated to the pinned length. Rúnar authenticates
  `_codePart` as `61ab || scriptCode[0:SIZE-2]`, so at the pinned SIZE this
  is the only `_codePart` that can pass.

Only the pool input is expected to fail. The vault moves only with its pool,
so if the node refuses both spends for Swap, Rescind and Close, neither
token can be recovered: the test passes and logs `FUNDS LOCKED`. If any of
them is accepted, the test fails. The last subtest writes the real code
length into the three fields, checks the result equals the SDK's bytes
exactly, and spends that pair through Swap both ways, Rescind and Close.

With a Rúnar whose artifact has no `codePartLenSlots` (the pinned one), the
test instead asserts the hand splice equals the SDK's code, and that it
spends.
