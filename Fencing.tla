-------------------------------- MODULE Fencing --------------------------------
(***************************************************************************)
(* The EtcFS fencing protocol: the three layers that are supposed to keep   *)
(* a partitioned node from corrupting the shared device, and the arena      *)
(* ownership they hand back and forth.                                      *)
(*                                                                          *)
(* The subject is the protocol described in                                 *)
(*   docs/architecture/fencing/fencing-generation-protocol.md                *)
(*   docs/architecture/fencing/self-fencing-watchdog.md                      *)
(*   docs/architecture/fencing/external-fencing-controller.md                *)
(* not the Go implementation. The gap between the two is closed by review.  *)
(*                                                                          *)
(* Written as TLA+ actions rather than PlusCal processes, which is a         *)
(* deviation from the plan in docs/verification/tla-plus.md. The reason is   *)
(* that every question this spec exists to answer is a question about where  *)
(* one atomic etcd operation may be interleaved with another. As actions,    *)
(* those boundaries are the spec's own vocabulary and a reader can see them  *)
(* directly; in PlusCal they would be a consequence of where the labels      *)
(* happen to fall, which is exactly the detail easiest to get quietly wrong. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Nodes,               \* the node identities in the cluster
    Arenas,              \* the arenas the shared device is carved into
    MaxGen,              \* generations are bounded so the state space is finite
    NoNode,              \* sentinel: an arena nobody owns
    FencerMode,          \* "reliable" | "unreliable" | "none"
    GuardEnabled,        \* FALSE is the broken variant: no generation guard
    ReleaseNeedsFencer,  \* FALSE is the broken variant: reclaim arenas unconfirmed
    FenceChecksIncarnation, \* TRUE is the implemented fix (see specs/README.md)
    HonorDeparture,      \* TRUE: a node that left on purpose is not fenced
    DepartureIsQuiescent \* FALSE is the broken variant: announce without releasing

ASSUME NoNode \notin Nodes
ASSUME FencerMode \in {"reliable", "unreliable", "none"}
ASSUME MaxGen \in Nat
ASSUME GuardEnabled \in BOOLEAN
ASSUME ReleaseNeedsFencer \in BOOLEAN
ASSUME FenceChecksIncarnation \in BOOLEAN
ASSUME HonorDeparture \in BOOLEAN
ASSUME DepartureIsQuiescent \in BOOLEAN

Gens  == 0..MaxGen
NoGen == MaxGen + 1   \* sentinel: no fence attempt is waiting to bump

(* FenceChecksIncarnation models the check pkg/fencing/controller.go performs
   before severing, before bumping and before releasing arenas: the fence
   compares the create-revision of fence_pending:<node> against the one it
   captured at the start, and abandons the attempt if it has changed or the
   key is gone.  Membership.grantAndRegister drops that key as the node
   re-registers, so a node that came back invalidates any fence still in
   flight for the departure it recovered from.  reRegistered models exactly
   that: set when the node restarts, cleared when a fence records a new
   intent for a new departure. *)

(* Nodes are interchangeable: permuting them maps any behaviour to another
   behaviour of the same spec, and none of the invariants name a node.  This
   lets TLC collapse those states.  Sound here because every property checked
   is itself symmetric. *)
Symmetry == Permutations(Nodes)

VARIABLES
    nodeState,      \* [Nodes -> {"Healthy","LeaseLost","SelfFenced","Down"}]
    lease,          \* [Nodes -> BOOLEAN]        etcd's view of membership
    startGen,       \* [Nodes -> Gens]           read ONCE at startup, then cached
    clusterGen,     \* [Nodes -> Gens]           gen:<node> as recorded in etcd
    deviceAccess,   \* [Nodes -> BOOLEAN]        can this node reach the device at all
    holds,          \* [Nodes -> SUBSET Arenas]  what the node BELIEVES it owns
    owner,          \* [Arenas -> Nodes \cup {NoNode}]  what etcd RECORDS
    fencePending,   \* [Nodes -> BOOLEAN]        fence_pending:<node>, the durable intent
    fenceDone,      \* [Nodes -> BOOLEAN]        fence_done:<node>, the completion mark
    fenceStep,      \* [Nodes -> {"idle","severed","bumped"}]  where fenceNode has got to
    fenceGen,       \* [Nodes -> Gens \cup {NoGen}]  generation the in-flight fence read
    reRegistered,   \* [Nodes -> BOOLEAN]  has n re-registered since its fence began?
    departed,       \* [Nodes -> BOOLEAN]  departed:<node>, "I left on purpose"
    fencedCommit    \* TRUE once a node commits metadata after being fenced

vars == << nodeState, lease, startGen, clusterGen, deviceAccess, holds,
           owner, fencePending, fenceDone, fenceStep, fenceGen, reRegistered,
           departed, fencedCommit >>

(***************************************************************************)
(* `holds' and `owner' are deliberately two variables and not one.  A node  *)
(* that has been partitioned cannot be told that its arena was taken away   *)
(* from it, so the cluster's record and the node's own belief diverge --     *)
(* and that divergence IS the hazard this whole protocol exists to prevent. *)
(* Modelling ownership as a single authoritative variable would make        *)
(* NoDoubleWriter true by construction and prove nothing.                   *)
(***************************************************************************)

Live(n) == nodeState[n] \in {"Healthy", "LeaseLost"}

(* A node has a write path to an arena when its process is running, it still
   believes it owns the arena, and nothing has severed it from the device. *)
CanWrite(n, a) == /\ a \in holds[n]
                  /\ deviceAccess[n]
                  /\ Live(n)

TypeOK ==
    /\ nodeState    \in [Nodes -> {"Healthy", "LeaseLost", "SelfFenced", "Down"}]
    /\ lease        \in [Nodes -> BOOLEAN]
    /\ startGen     \in [Nodes -> Gens]
    /\ clusterGen   \in [Nodes -> Gens]
    /\ deviceAccess \in [Nodes -> BOOLEAN]
    /\ holds        \in [Nodes -> SUBSET Arenas]
    /\ owner        \in [Arenas -> Nodes \cup {NoNode}]
    /\ fencePending \in [Nodes -> BOOLEAN]
    /\ fenceDone    \in [Nodes -> BOOLEAN]
    /\ fenceStep    \in [Nodes -> {"idle", "severed", "bumped"}]
    /\ fenceGen     \in [Nodes -> Gens \cup {NoGen}]
    /\ reRegistered \in [Nodes -> BOOLEAN]
    /\ departed     \in [Nodes -> BOOLEAN]
    /\ fencedCommit \in BOOLEAN

Init ==
    /\ nodeState    = [n \in Nodes |-> "Healthy"]
    /\ lease        = [n \in Nodes |-> TRUE]
    /\ startGen     = [n \in Nodes |-> 0]
    /\ clusterGen   = [n \in Nodes |-> 0]
    /\ deviceAccess = [n \in Nodes |-> TRUE]
    /\ holds        = [n \in Nodes |-> {}]
    /\ owner        = [a \in Arenas |-> NoNode]
    /\ fencePending = [n \in Nodes |-> FALSE]
    /\ fenceDone    = [n \in Nodes |-> FALSE]
    /\ fenceStep    = [n \in Nodes |-> "idle"]
    /\ fenceGen     = [n \in Nodes |-> NoGen]
    /\ reRegistered = [n \in Nodes |-> FALSE]
    /\ departed     = [n \in Nodes |-> FALSE]
    /\ fencedCommit = FALSE

(***************************************************************************)
(* Node lifecycle                                                           *)
(***************************************************************************)

(* The lease expires in etcd.  The node does NOT know yet: its process is
   still running, it still believes it owns its arenas, and it can still
   write to the device.  This is the whole danger, and the reason
   "LeaseLost" is a state distinct from "Down". *)
LeaseExpires(n) ==
    /\ nodeState[n] = "Healthy"
    /\ lease' = [lease EXCEPT ![n] = FALSE]
    /\ nodeState' = [nodeState EXCEPT ![n] = "LeaseLost"]
    /\ UNCHANGED << startGen, clusterGen, deviceAccess, holds, owner,
                    fencePending, fenceDone, fenceStep, fenceGen, reRegistered, departed, fencedCommit >>

(* The watchdog notices and the process exits.  The real watchdog fires
   2-3x the lease TTL after the lease dies; TLA+ has no clock, so the delay
   becomes "may happen at any point after LeaseLost" and the bound itself is
   left to the chaos tests, which measure it.  What is modelled is the part
   that matters for safety: the node stops writing.

   `owner' is deliberately NOT cleared.  main does try to release this
   node's arenas on the way out, but a self-fencing node is by definition
   one that cannot reach etcd, so that release is exactly the thing most
   likely to fail.  Assuming it succeeds would be assuming the good case. *)
SelfFence(n) ==
    /\ nodeState[n] = "LeaseLost"
    /\ nodeState' = [nodeState EXCEPT ![n] = "SelfFenced"]
    /\ holds' = [holds EXCEPT ![n] = {}]
    /\ UNCHANGED << lease, startGen, clusterGen, deviceAccess, owner,
                    fencePending, fenceDone, fenceStep, fenceGen, reRegistered, departed, fencedCommit >>

(* Power loss or kernel panic: no self-fence, no cleanup, but the process is
   genuinely gone and so are its writes. *)
NodeCrash(n) ==
    /\ Live(n)
    /\ nodeState' = [nodeState EXCEPT ![n] = "Down"]
    /\ lease' = [lease EXCEPT ![n] = FALSE]
    /\ holds' = [holds EXCEPT ![n] = {}]
    /\ UNCHANGED << startGen, clusterGen, deviceAccess, owner,
                    fencePending, fenceDone, fenceStep, fenceGen, reRegistered, departed, fencedCommit >>

(* A fenced node restarts and adopts whatever generation it now finds: the
   fence is an epoch boundary, not a permanent ban.  It comes back with a
   fresh lease, device access restored, and no arenas -- it must claim new
   ones, and must NOT recover the ones that were taken from it. *)
NodeRestart(n) ==
    /\ nodeState[n] \in {"SelfFenced", "Down"}
    /\ nodeState' = [nodeState EXCEPT ![n] = "Healthy"]
    /\ lease' = [lease EXCEPT ![n] = TRUE]
    /\ startGen' = [startGen EXCEPT ![n] = clusterGen[n]]
    /\ deviceAccess' = [deviceAccess EXCEPT ![n] = TRUE]
    \* Allocator.Reconstruct re-adopts every arena whose arena:<node>/<id>
    \* record still exists.  The node does not start empty: it starts owning
    \* whatever etcd still says it owns.
    /\ holds' = [holds EXCEPT ![n] = {a \in Arenas : owner[a] = n}]
    /\ reRegistered' = [reRegistered EXCEPT ![n] = TRUE]
    \* Membership.grantAndRegister drops departed:<node> as it re-registers, so
    \* a marker describes the departure it was written for and not the node
    \* for ever.  Without this a node could leave cleanly once and never be
    \* fenced again, however it died afterwards.
    /\ departed' = [departed EXCEPT ![n] = FALSE]
    /\ UNCHANGED << clusterGen, owner, fencePending, fenceDone, fenceStep,
                    fenceGen, fencedCommit >>

(* A node leaves on purpose.  This is one etcd transaction -- Put of
   departed:<n> together with the Delete of membership:<n>, conditioned on the
   membership key still being there -- so no controller can observe the
   departure without already being able to see the marker.  That atomicity is
   what removes any need for a grace window, and with it any clock.

   `lease[n]' as a precondition is the transaction's own comparison: a node
   whose lease has already timed out is no longer a member and cannot go back
   and declare its departure intentional.  That is what stops a partitioned
   node -- the node this entire protocol exists to contain -- from writing
   itself an exemption.

   DepartureIsQuiescent models the ordering leaveCluster depends on: the node
   has STOPPED SERVING before it gives anything back, so by the time the marker
   is published there is no write path left.  Setting it FALSE is the broken
   variant: the arenas go back and the marker is published by a node that is
   still running and still believes it owns them.

   Note what that variant is chosen to defeat.  The arena check in FenceStart
   catches a node that announces a departure while the records still show it as
   an owner -- so a mutation of that kind proves nothing, because the second
   line of defence holds.  The case worth checking is the one the arena check
   CANNOT see: records clean, node still alive.  `holds' and `owner' diverging
   is exactly how this spec represents a node that cannot be told what the
   cluster now believes, and it is why quiescence has to come first rather than
   be inferred from the bookkeeping. *)
LeaveCleanly(n) ==
    /\ nodeState[n] = "Healthy"
    /\ lease[n]
    /\ lease' = [lease EXCEPT ![n] = FALSE]
    /\ departed' = [departed EXCEPT ![n] = TRUE]
    /\ owner' = [a \in Arenas |-> IF owner[a] = n THEN NoNode ELSE owner[a]]
    /\ IF DepartureIsQuiescent
         THEN /\ nodeState' = [nodeState EXCEPT ![n] = "Down"]
              /\ holds' = [holds EXCEPT ![n] = {}]
         ELSE UNCHANGED << nodeState, holds >>
    /\ UNCHANGED << startGen, clusterGen, deviceAccess, fencePending,
                    fenceDone, fenceStep, fenceGen, reRegistered, fencedCommit >>

(***************************************************************************)
(* The external fencing controller                                          *)
(***************************************************************************)

(* A controller sees the membership key gone and records the durable intent.
   The intent is what makes the fence survive the death of whichever
   controller happened to observe the expiry. *)
FenceStart(n) ==
    \* fenceNode's progress is local to one goroutine invocation: a new fence
    \* always starts from scratch and severs afresh.  It never inherits a
    \* previous attempt's progress.
    /\ fenceStep[n] = "idle"
    /\ ~lease[n]
    \* Controller.departedCleanly: the marker is honoured only where the
    \* cluster's own arena records back it up.  A node still recorded as an
    \* owner has not given up what it says it gave up, so it is fenced exactly
    \* as it would have been -- which is what makes this a checked claim
    \* rather than a trusted one.
    /\ ~(HonorDeparture /\ departed[n] /\ (\A a \in Arenas : owner[a] # n))
    /\ ~fencePending[n]
    /\ ~fenceDone[n]
    /\ fencePending' = [fencePending EXCEPT ![n] = TRUE]
    /\ reRegistered' = [reRegistered EXCEPT ![n] = FALSE]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, fenceDone, fenceStep, fenceGen, departed,
                    fencedCommit >>

(* Sever the node's access to the device, then queue the generation the bump
   will CAS against.  The ordering is the point: severing is a PRECONDITION
   of the bump, because the bump is what tells peers they may reclaim this
   node's arenas.

   With FencerMode = "unreliable" this action is never enabled, which is
   faithful: a fence that cannot be confirmed aborts without bumping, and
   the intent is left in place for the sweep to retry forever. *)
FenceSever(n) ==
    /\ FencerMode = "reliable"
    /\ (FenceChecksIncarnation => ~reRegistered[n])
    /\ fencePending[n]
    /\ fenceStep[n] = "idle"
    /\ deviceAccess' = [deviceAccess EXCEPT ![n] = FALSE]
    /\ fenceStep' = [fenceStep EXCEPT ![n] = "severed"]
    /\ fenceGen' = [fenceGen EXCEPT ![n] = clusterGen[n]]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, holds, owner,
                    fencePending, fenceDone, reRegistered, departed, fencedCommit >>

(* Single-signal mode: no Fencer is configured, so the controller bumps on
   lease expiry alone.  Nothing severs the node from the device -- which is
   precisely why the arena release below refuses to run in this mode. *)
FenceSeverSkipped(n) ==
    /\ FencerMode = "none"
    /\ fencePending[n]
    /\ fenceStep[n] = "idle"
    /\ fenceStep' = [fenceStep EXCEPT ![n] = "severed"]
    /\ fenceGen' = [fenceGen EXCEPT ![n] = clusterGen[n]]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, fencePending, fenceDone, reRegistered, departed, fencedCommit >>

(* The CAS bump.  Succeeds only if the generation is still what the fence
   read; a concurrent fence that already bumped it makes this a no-op that
   abandons the attempt rather than double-incrementing. *)
FenceBump(n) ==
    /\ fenceStep[n] = "severed"
    /\ (FenceChecksIncarnation => ~reRegistered[n])
    /\ fenceGen[n] = clusterGen[n]
    /\ clusterGen[n] < MaxGen                  \* model bound, not a protocol rule
    /\ clusterGen' = [clusterGen EXCEPT ![n] = clusterGen[n] + 1]
    /\ fenceStep' = [fenceStep EXCEPT ![n] = "bumped"]
    /\ UNCHANGED << nodeState, lease, startGen, deviceAccess, holds, owner,
                    fencePending, fenceDone, fenceGen, reRegistered, departed, fencedCommit >>

(* The CAS lost: another fence bumped this node's generation in between.
   The controller re-reads, logs, and does not retry. *)
FenceBumpLostCAS(n) ==
    /\ fenceStep[n] = "severed"
    /\ fenceGen[n] # clusterGen[n]
    /\ fenceStep' = [fenceStep EXCEPT ![n] = "idle"]
    /\ fenceGen' = [fenceGen EXCEPT ![n] = NoGen]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, fencePending, fenceDone, reRegistered, departed, fencedCommit >>

(* Reclaim the fenced node's arena.  This runs INSIDE fenceNode, immediately
   after the bump and before the completion mark -- it is a separate etcd
   call, so anything at all may happen between the two.
   ReleaseNeedsFencer is invariant 4 from the Kleppmann analysis: in
   single-signal mode nothing has proved the node stopped writing, so the
   arena is deliberately leaked rather than handed to a peer that would then
   be the second writer.  Setting it FALSE is a broken variant.

   Note what the real ReleaseArenaID compares: only that the ownership
   record still exists.  Not which epoch wrote it. *)
FenceReleaseArena(n, a) ==
    /\ fenceStep[n] = "bumped"
    /\ (FenceChecksIncarnation => ~reRegistered[n])
    /\ owner[a] = n
    /\ (ReleaseNeedsFencer => FencerMode = "reliable")
    /\ owner' = [owner EXCEPT ![a] = NoNode]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, fencePending, fenceDone, fenceStep, fenceGen,
                    reRegistered, departed, fencedCommit >>

(* MarkFenceComplete then ClearFenceIntent: only now is nothing owed. *)
FenceComplete(n) ==
    /\ fenceStep[n] = "bumped"
    /\ fenceDone' = [fenceDone EXCEPT ![n] = TRUE]
    /\ fencePending' = [fencePending EXCEPT ![n] = FALSE]
    /\ fenceStep' = [fenceStep EXCEPT ![n] = "idle"]
    /\ fenceGen' = [fenceGen EXCEPT ![n] = NoGen]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, reRegistered, departed, fencedCommit >>

(* The controller dies part-way through.  Its claim lease expires; the intent
   survives, so the sweep retries the whole fence.  Device access stays
   severed -- severing is not undone by the death of the controller. *)
FenceAbort(n) ==
    /\ fenceStep[n] # "idle"
    /\ fenceStep' = [fenceStep EXCEPT ![n] = "idle"]
    /\ fenceGen' = [fenceGen EXCEPT ![n] = NoGen]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, fencePending, fenceDone, reRegistered, departed, fencedCommit >>

(* The sweep finds a live membership key for a node it was about to fence:
   the node has recovered from the expiry that triggered the fence, so the
   intent and the completion mark are both dropped.  Note this only drops the
   BOOKKEEPING -- a fence already past its sever step is not called back. *)
DropIntentOnReRegister(n) ==
    /\ lease[n]
    /\ (fencePending[n] \/ fenceDone[n])
    /\ fencePending' = [fencePending EXCEPT ![n] = FALSE]
    /\ fenceDone' = [fenceDone EXCEPT ![n] = FALSE]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, fenceStep, fenceGen, reRegistered, departed, fencedCommit >>

(***************************************************************************)
(* Arenas                                                                   *)
(***************************************************************************)

ClaimArena(n, a) ==
    /\ nodeState[n] = "Healthy"
    /\ owner[a] = NoNode
    /\ owner' = [owner EXCEPT ![a] = n]
    /\ holds' = [holds EXCEPT ![n] = holds[n] \cup {a}]
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    fencePending, fenceDone, fenceStep, fenceGen, reRegistered, departed, fencedCommit >>

(***************************************************************************)
(* The write path                                                           *)
(***************************************************************************)

(* A write commits its metadata only if the generation guard passes.  The
   guard compares the generation the node CACHED AT STARTUP against what
   etcd records now -- not a fresh read.  That is not an optimisation: a
   write that re-read the generation would read the already-bumped value
   and CAS it against itself, and every post-fence write would succeed.

   The bytes reaching the device are modelled by CanWrite alone; a guard
   failure orphans them rather than preventing them, which is why
   NoDoubleWriter is about CanWrite and StaleWriteRejected is about the
   commit.  They are separate properties because they are separate layers. *)
Write(n, a) ==
    /\ CanWrite(n, a)
    /\ (GuardEnabled => startGen[n] = clusterGen[n])
    /\ fencedCommit' = (fencedCommit \/ startGen[n] # clusterGen[n])
    /\ UNCHANGED << nodeState, lease, startGen, clusterGen, deviceAccess,
                    holds, owner, fencePending, fenceDone, fenceStep, fenceGen,
                    reRegistered, departed >>

(***************************************************************************)

Next ==
    \/ \E n \in Nodes :
        \/ LeaseExpires(n)
        \/ SelfFence(n)
        \/ NodeCrash(n)
        \/ NodeRestart(n)
        \/ LeaveCleanly(n)
        \/ FenceStart(n)
        \/ FenceSever(n)
        \/ FenceSeverSkipped(n)
        \/ FenceBump(n)
        \/ FenceBumpLostCAS(n)
        \/ FenceComplete(n)
        \/ FenceAbort(n)
        \/ DropIntentOnReRegister(n)
    \/ \E n \in Nodes, a \in Arenas :
        \/ FenceReleaseArena(n, a)
        \/ ClaimArena(n, a)
        \/ Write(n, a)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety                                                                   *)
(***************************************************************************)

(* The property the whole design exists for: never two nodes with a write
   path to one arena at the same time. *)
NoDoubleWriter ==
    \A a \in Arenas : Cardinality({n \in Nodes : CanWrite(n, a)}) <= 1

(* No node commits metadata after its generation has been bumped out from
   under it.  This is the layer that must hold even when the external
   fencer fails, and the reason FencerMode has an "unreliable" setting. *)
StaleWriteRejected == ~fencedCommit

(* A healthy node holding a live membership lease has not had its access to
   the device cut out from under it. *)
NoHealthyNodeSevered ==
    \A n \in Nodes :
        (nodeState[n] = "Healthy" /\ lease[n]) => deviceAccess[n]

(* A node that is healthy and holds a live membership lease can actually
   write.  startGen is cached for the life of the process, so a node whose
   generation is bumped after it restarted is wedged: every guarded mutation
   fails with EIO, for as long as the process lives, with nothing to correct
   it and nothing in the cluster reporting it as anything but healthy. *)
NoWedgedNode ==
    \A n \in Nodes :
        (nodeState[n] = "Healthy" /\ lease[n]) => startGen[n] = clusterGen[n]

(* A node's recorded generation never decreases. *)
GenerationMonotone ==
    [][\A n \in Nodes : clusterGen'[n] >= clusterGen[n]]_vars

(* A node that has been severed from the device is not still believed to be
   a live writer by the arena bookkeeping -- i.e. once the cluster hands an
   arena on, the previous holder really cannot reach it. *)
ReleasedArenaHasNoLiveWriter ==
    \A a \in Arenas :
        owner[a] = NoNode => \A n \in Nodes : ~CanWrite(n, a)

=============================================================================
