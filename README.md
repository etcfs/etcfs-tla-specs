# TLA+ specifications

`Fencing.tla` models the EtcFS fencing protocol — the three layers that keep a
partitioned node from corrupting the shared device, and the arena ownership
they hand back and forth.

Run everything with:

```sh
scripts/test/tla-check.sh          # 2-node models, ~30s
DEEP=1 scripts/test/tla-check.sh   # adds the 3-node model, several minutes
```

The script downloads `tla2tools.jar` into `specs/.tools/` on first use (it is
gitignored) and asserts the outcome each configuration is *supposed* to have.
Three of them are supposed to fail: a spec that proves everything proves
nothing, so the deliberately broken variants are checked to still produce a
counterexample.

## What each configuration is for

| Configuration | Fence re-checks incarnation | Guard | Fencer | Expected |
|---|---|---|---|---|
| `Fencing` | yes | on | reliable | no counterexample |
| `Fencing3Nodes` | yes | on | reliable | no counterexample |
| `FencingNoFencer` | yes | on | none (single-signal) | no counterexample |
| `FencingUnreliableFencer` | yes | on | unreliable | no counterexample |
| `FencingGuardIsBackstop` | **no** | on | reliable | no counterexample *(only `StaleWriteRejected` checked)* |
| `FencingAsImplemented` | **no** | on | reliable | breaks `NoHealthyNodeSevered` |
| `FencingNoGuard` | **no** | **off** | reliable | breaks `StaleWriteRejected` |
| `FencingArenaBug` | yes | on | none, **but reclaims arenas anyway** | breaks `ReleasedArenaHasNoLiveWriter` |

`FencingAsImplemented` is the protocol as the Go code currently implements it,
and it is the one that found a real defect — see
[docs/verification/tla-plus.md](../docs/verification/tla-plus.md) for the
trace and the analysis. `FenceChecksIncarnation = TRUE` is the proposed fix,
not something the code does today.

## Why TLA+ actions rather than PlusCal

The plan called for PlusCal. Every question this spec exists to answer is a
question about where one atomic etcd operation may be interleaved with
another — so as actions, those boundaries are the spec's own vocabulary and a
reader can see them directly. In PlusCal they would instead be a consequence
of where the labels happen to fall, which is exactly the detail that is
easiest to get quietly wrong in a spec whose whole purpose is to be right
about atomicity.

## What is deliberately not modelled

- **Real time.** TLA+ has no clock, so the watchdog's 2–3× lease-TTL margin
  becomes "may fire at any point after the lease is lost". The *bound* is
  measured by the chaos suite; what the spec checks is the ordering.
- **etcd itself.** Transactions are assumed linearizable and CAS is assumed
  atomic. Those are the assumptions the design rests on, stated as such;
  Porcupine checks the daemon's own use of them from recorded histories.
- **Two controllers fencing one node concurrently.** The per-node
  `fence_claim` lease serialises them, and `FenceBumpLostCAS` models the
  generation CAS losing, but two fully interleaved fence sequences for one
  node are not enumerated. A claim that expires under a live fencer is the
  case this would reach; it is the obvious next extension.
- **The gap between spec and code.** This is a model of the protocol as
  documented, not of `pkg/fencing`. That gap is closed by review.
