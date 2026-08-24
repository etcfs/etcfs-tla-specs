# TLA+ specifications

Two specifications, one per layer of the exclusion the filesystem rests on.

`Fencing.tla` models the EtcFS fencing protocol — the three layers that keep a
partitioned node from corrupting the shared device, and the arena ownership
they hand back and forth.

`CachedLock.tla` models the layer above it: the per-inode lock key, kept rather
than taken and released per operation, and the three caches that live under it
— the metadata snapshot, the kernel's data pages, and the writes a node has
acknowledged and not yet published. What it checks is that every one of those
caches dies with the key it was made under, and that nothing is ever published
without it.

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
| `FencingNoIncarnationCheck` | **no** | on | reliable | breaks `NoHealthyNodeSevered` |
| `FencingNoGuard` | **no** | **off** | reliable | breaks `StaleWriteRejected` |
| `FencingArenaBug` | yes | on | none, **but reclaims arenas anyway** | breaks `ReleasedArenaHasNoLiveWriter` |
| `FencingDepartureNotQuiescent` | yes | on | reliable, **departure announced without stopping** | breaks `ReleasedArenaHasNoLiveWriter` |

| Configuration | What it takes away | Expected |
|---|---|---|
| `CachedLock` | nothing: the protocol as implemented | no counterexample |
| `CachedLockNoLeaseIdentity` | the cached key is trusted while *any* session is alive | breaks `NoTwoHolders` |
| `CachedLockNoFlushKeyCheck` | the flush's comparison on this node's own lock key | breaks `NoPublishWithoutLock` |
| `CachedLockNoRecallFlush` | the flush a recall does before yielding | breaks `NoLostAckedWrite` |
| `CachedLockNoInvalidate` | the kernel page invalidation before yielding | breaks `NoStalePages` |
| `CachedLockStaleSnapshot` | dropping the metadata snapshot with the key | breaks `ViewMatchesTruth` |
| `CachedLockKeepsCacheOnKeyLoss` | dropping the caches when the key is found gone | breaks `NoStalePages` |

`ViewMatchesTruth` is the property every cache here rests on and the one no
other spec names: what a node believes an inode is equals what etcd records,
plus whatever that same node has buffered and not yet published.

`FencingNoIncarnationCheck` is the protocol as it stood *before* this work: it
is the configuration that found a real defect, and it is kept so the defect
stays checked rather than remembered. `FenceChecksIncarnation = TRUE` is what
`pkg/fencing/controller.go` now does. See
[docs/verification/tla-plus.md](../docs/verification/tla-plus.md) for the
traces, the analysis, and why the obvious liveness-based fix was rejected.

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
- **Time.** `CachedLock.tla` leaves out the want-key and the minimum hold
  time, which only ever *delay* a recall: omitting them admits every behaviour
  they would have allowed and more. It also leaves out the crash case, where
  unflushed writes are legitimately lost — that is `test/verify`'s extent
  model, which can see which node died and which writes were fsynced.
- **Two inodes.** Every action and every invariant in `CachedLock.tla` is about
  one inode, and nothing relates one to another, so a second would multiply the
  state space without adding a behaviour. Contention *between* inodes is a
  scheduling question and belongs to the chaos suite.
- **The gap between spec and code.** This is a model of the protocol as
  documented, not of `pkg/fencing`. That gap is closed by review.
