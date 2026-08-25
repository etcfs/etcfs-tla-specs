------------------------------ MODULE CachedLock ------------------------------
(***************************************************************************)
(* The EtcFS cached inode lock and the write delegation built on it.        *)
(*                                                                          *)
(* Fencing.tla models the arena layer: which node may touch which part of   *)
(* the device at all.  This spec models the layer above it, where the same  *)
(* question is asked per inode and answered by a lock key that is *kept*    *)
(* rather than taken and dropped per operation -- and where three caches    *)
(* now live under that key: the metadata snapshot, the kernel's data pages, *)
(* and the writes this node has acknowledged and not yet published.         *)
(*                                                                          *)
(* The subject is the protocol described in                                 *)
(*   docs/architecture/metadata/inode-locking.md                            *)
(*   docs/architecture/data/write-delegation.md                             *)
(* and implemented in internal/ipc/lockcache.go and delegate.go.  As in     *)
(* Fencing.tla the gap between spec and Go is closed by review, and the     *)
(* spec is written as actions rather than PlusCal so that the boundaries    *)
(* between etcd operations are the spec's own vocabulary.                   *)
(*                                                                          *)
(* What makes any of the caching sound is that a node holding an inode's    *)
(* key excludes every peer from that inode, so nothing it has cached can go *)
(* stale underneath it.  Everything checked here is a consequence of that   *)
(* one sentence being true at the moments it is relied on -- and of the     *)
(* obligations discharged when it stops being true, which is what the       *)
(* broken variants take away one at a time.                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Nodes,                \* the node identities in the cluster
    MaxVal,               \* file contents are a bounded counter, for finiteness
    MaxLease,             \* how many times a node's lock session may be replaced
    NoNode,               \* sentinel: the lock key nobody holds
    LeaseIdentityChecked, \* FALSE is the broken variant: trust a live session
    FlushChecksKey,       \* FALSE is the broken variant: publish without the key
    RecallFlushes,        \* FALSE is the broken variant: yield with writes buffered
    InvalidateOnYield,    \* FALSE is the broken variant: keep the kernel's pages
    DropSnapshotOnYield,  \* FALSE is the broken variant: keep a snapshot past the key
    DropCacheOnKeyLoss    \* FALSE is the broken variant: keep caches past the key

ASSUME NoNode \notin Nodes
ASSUME MaxVal \in Nat /\ MaxLease \in Nat
ASSUME LeaseIdentityChecked \in BOOLEAN
ASSUME FlushChecksKey \in BOOLEAN
ASSUME RecallFlushes \in BOOLEAN
ASSUME InvalidateOnYield \in BOOLEAN
ASSUME DropSnapshotOnYield \in BOOLEAN
ASSUME DropCacheOnKeyLoss \in BOOLEAN

Vals  == 1..MaxVal
NoVal == 0          \* sentinel: nothing written yet, or nothing buffered
Leases == 0..MaxLease

(* One inode.  Two would multiply the state space without adding a
   behaviour: the lock, the caches and the buffer are all per inode, no
   action relates one inode to another, and every invariant here is a
   statement about a single inode.  Contention *between* inodes is a
   scheduling question, and the chaos suite is where it belongs. *)

VARIABLES
    keyOwner,       \* Nodes \cup {NoNode}: who holds the inode's lock key in etcd
    cached,         \* [Nodes -> BOOLEAN]  does the node BELIEVE it holds the key
    keyLease,       \* [Nodes -> Leases]   the session its cached key was written under
    session,        \* [Nodes -> Leases]   the node's current lock session
    view,           \* [Nodes -> Vals \cup {NoVal}]  the cached metadata snapshot
    buf,            \* [Nodes -> Vals \cup {NoVal}]  acknowledged, not yet published
    pages,          \* [Nodes -> BOOLEAN]  the kernel holds data pages for the inode
    published,      \* Vals \cup {NoVal}: what etcd records, i.e. what a peer would read
    publishedUnowned, \* TRUE once a flush has committed without the key
    lostAckedWrite    \* TRUE once a recall has dropped acknowledged writes

vars == << keyOwner, cached, keyLease, session, view, buf, pages, published,
           publishedUnowned, lostAckedWrite >>

(***************************************************************************)
(* `cached' and `keyOwner' are two variables for the same reason `holds'    *)
(* and `owner' are in Fencing.tla: a node whose session expired is not told *)
(* so, and the whole hazard is the window in which the cluster's record and *)
(* the node's belief disagree.                                              *)
(*                                                                          *)
(* Holds is the guard every operation on the inode passes, and it is the    *)
(* one ensureLockKey actually implements: not "is my session alive" but "is *)
(* the key I cached still written under the session I have now".  A dead    *)
(* session is replaced lazily by the next acquisition on any inode, so      *)
(* liveness goes true again while this key -- written under the previous    *)
(* lease and deleted with it -- is already gone.  LeaseIdentityChecked      *)
(* FALSE is exactly that weaker test.                                       *)
(***************************************************************************)
Holds(n) == cached[n] /\ (LeaseIdentityChecked => keyLease[n] = session[n])

TypeOK ==
    /\ keyOwner  \in Nodes \cup {NoNode}
    /\ cached    \in [Nodes -> BOOLEAN]
    /\ keyLease  \in [Nodes -> Leases]
    /\ session   \in [Nodes -> Leases]
    /\ view      \in [Nodes -> Vals \cup {NoVal}]
    /\ buf       \in [Nodes -> Vals \cup {NoVal}]
    /\ pages     \in [Nodes -> BOOLEAN]
    /\ published \in Vals \cup {NoVal}
    /\ publishedUnowned \in BOOLEAN
    /\ lostAckedWrite   \in BOOLEAN

Init ==
    /\ keyOwner  = NoNode
    /\ cached    = [n \in Nodes |-> FALSE]
    /\ keyLease  = [n \in Nodes |-> 0]
    /\ session   = [n \in Nodes |-> 0]
    /\ view      = [n \in Nodes |-> NoVal]
    /\ buf       = [n \in Nodes |-> NoVal]
    /\ pages     = [n \in Nodes |-> FALSE]
    /\ published = NoVal
    /\ publishedUnowned = FALSE
    /\ lostAckedWrite   = FALSE

(***************************************************************************)
(* Taking and keeping the key                                               *)
(***************************************************************************)

(* Acquire the key and read the inode under it.  The snapshot is taken here
   and trusted until the key goes, which is the whole point of caching it: a
   node whose cache was dropped reads etcd, and one that still has a snapshot
   uses it.  That is why the *drop* is the load-bearing half, and why
   DropSnapshotOnYield FALSE -- a snapshot that outlives the key it was read
   under -- is the mistake the holder token exists to prevent. *)
(* A lock a node takes in the transaction that *creates* the inode is this
   action too, not a weaker one: the create asserts the same empty blocking
   range an ordinary acquisition asserts, and the snapshot it seeds is the
   record that transaction just wrote -- which is `published', exactly what
   this action already gives a node with no view of its own. *)
Acquire(n) ==
    /\ keyOwner = NoNode
    /\ ~cached[n]
    /\ keyOwner' = n
    /\ cached'   = [cached   EXCEPT ![n] = TRUE]
    /\ keyLease' = [keyLease EXCEPT ![n] = session[n]]
    /\ view'     = [view EXCEPT ![n] = IF view[n] = NoVal THEN published ELSE view[n]]
    /\ UNCHANGED << session, buf, pages, published, publishedUnowned, lostAckedWrite >>

(* A write is acknowledged out of RAM: its bytes are on no device and in no
   etcd record until a flush publishes them.  The node's own view moves with
   it, which is what lets a reader on this node see what it just wrote. *)
Write(n, v) ==
    /\ Holds(n)
    /\ buf'  = [buf  EXCEPT ![n] = v]
    /\ view' = [view EXCEPT ![n] = v]
    /\ UNCHANGED << keyOwner, cached, keyLease, session, pages, published,
                    publishedUnowned, lostAckedWrite >>

(* A read the kernel is allowed to cache, because this node holds the lock.
   From here the pages answer later reads without the daemon seeing them at
   all, which is why yielding the key has to take them away. *)
Read(n) ==
    /\ Holds(n)
    /\ pages' = [pages EXCEPT ![n] = TRUE]
    /\ UNCHANGED << keyOwner, cached, keyLease, session, view, buf, published,
                    publishedUnowned, lostAckedWrite >>

(* The flush: one transaction, with a comparison on this node's own lock key.
   That comparison is the only thing standing between a node that lost the
   inode and a peer's data, so FlushChecksKey FALSE is the interesting break.
   A rejected flush discards the buffer -- nothing in etcd ever referenced
   those blocks -- and that discard is not a lost acknowledged write in the
   sense NoLostAckedWrite means: the session was gone, which is the one case
   POSIX allows an unsynced write to vanish in.

   Nothing here says *when* a flush runs, and that is deliberate: it is enabled
   from the moment there is a buffer until something takes the buffer away, so
   every schedule the implementation could pick is already a behaviour of this
   spec.  Publishing on close(), publishing on a timer, and publishing several
   inodes in one transaction are the same action here -- the last of those
   because this is a one-inode model and a shared transaction adds atomicity
   *between* inodes, which no invariant below constrains.  What is not free to
   move is the comparison, which is per inode and stays per inode however many
   inodes ride one commit. *)
Flush(n) ==
    /\ cached[n]
    /\ buf[n] # NoVal
    /\ LET owns == keyOwner = n IN
        /\ IF owns \/ ~FlushChecksKey
             THEN /\ published' = buf[n]
                  /\ publishedUnowned' = (publishedUnowned \/ ~owns)
             ELSE UNCHANGED << published, publishedUnowned >>
    /\ buf' = [buf EXCEPT ![n] = NoVal]
    /\ UNCHANGED << keyOwner, cached, keyLease, session, view, pages, lostAckedWrite >>

(***************************************************************************)
(* Giving the key up                                                        *)
(***************************************************************************)

(* A peer wants the inode, so this node yields it.  Modelled as enabled
   whenever the key is held rather than gated on a request key and a minimum
   hold time: both only ever *delay* a recall, so leaving them out admits
   every behaviour they would have allowed and more.  What is not left out is
   the order the release runs in, which is where the obligations are:
   publish, then invalidate the kernel's pages, then delete the key.
   Everything cached under that key goes with it.

   Yielding several keys in one etcd transaction -- which is how the cache
   evicts -- is this action once per inode.  The order above is what has to hold
   per inode, and a shared delete only makes the last step of each atomic with
   the others, which is strictly stronger than the separate deletes modelled
   here. *)
Recall(n) ==
    /\ cached[n]
    /\ LET owns    == keyOwner = n
           flushed == RecallFlushes /\ owns /\ buf[n] # NoVal
       IN
        /\ published' = IF flushed THEN buf[n] ELSE published
        \* Yielding with writes still buffered loses them for good: the key is
        \* the flush's own comparison, so no later flush can ever publish them.
        /\ lostAckedWrite' = (lostAckedWrite \/ (owns /\ buf[n] # NoVal /\ ~flushed))
    /\ pages'    = [pages    EXCEPT ![n] = IF InvalidateOnYield THEN FALSE ELSE pages[n]]
    /\ cached'   = [cached   EXCEPT ![n] = FALSE]
    /\ view'     = [view     EXCEPT ![n] = IF DropSnapshotOnYield THEN NoVal ELSE view[n]]
    /\ buf'      = [buf      EXCEPT ![n] = NoVal]
    /\ keyOwner' = IF keyOwner = n THEN NoNode ELSE keyOwner
    /\ UNCHANGED << keyLease, session, publishedUnowned >>

(* The lock session expires.  etcd deletes the key with it and a peer may
   take the inode immediately; the node itself is still running and still
   believes it holds everything.  Its next operation is supposed to notice,
   and until it does this is the window every cache here is exposed in. *)
SessionLost(n) ==
    /\ session[n] < MaxLease
    /\ session'  = [session EXCEPT ![n] = session[n] + 1]
    /\ keyOwner' = IF keyOwner = n THEN NoNode ELSE keyOwner
    /\ UNCHANGED << cached, keyLease, view, buf, pages, published,
                    publishedUnowned, lostAckedWrite >>

(* The node notices, on its next operation, that the key it cached was
   written under a session it no longer has.  Nothing can be refused here --
   the key is not this node's to hold on to, and a peer may already own the
   inode -- so every cache under it is dropped rather than trusted.
   DropCacheOnKeyLoss FALSE keeps them, which is a node serving a peer's
   inode out of its own memory. *)
NoticeKeyLost(n) ==
    /\ cached[n]
    /\ keyLease[n] # session[n]
    /\ cached' = [cached EXCEPT ![n] = FALSE]
    /\ IF DropCacheOnKeyLoss
         THEN /\ view'  = [view  EXCEPT ![n] = NoVal]
              /\ buf'   = [buf   EXCEPT ![n] = NoVal]
              /\ pages' = [pages EXCEPT ![n] = FALSE]
         ELSE UNCHANGED << view, buf, pages >>
    /\ UNCHANGED << keyOwner, keyLease, session, published, publishedUnowned,
                    lostAckedWrite >>

(***************************************************************************)

Next ==
    \/ \E n \in Nodes :
        \/ Acquire(n)
        \/ Read(n)
        \/ Flush(n)
        \/ Recall(n)
        \/ SessionLost(n)
        \/ NoticeKeyLost(n)
    \/ \E n \in Nodes, v \in Vals : Write(n, v)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety                                                                   *)
(***************************************************************************)

(* Invariant 1.  No two nodes act on one inode as its holder at the same
   time -- and "acts as holder" is the node's own test, not the cluster's,
   because that test is what actually gates the operation. *)
NoTwoHolders == Cardinality({n \in Nodes : Holds(n)}) <= 1

(* Invariant 2.  Nothing is ever published by a node that does not hold the
   inode's key, whether it never had it or lost it mid-buffer. *)
NoPublishWithoutLock == ~publishedUnowned

(* Invariant 6, the half that is not about crashes: a recall must not lose
   writes this node already acknowledged.  A crash may; a peer asking for the
   inode may not, and the flush before the yield is what separates them. *)
NoLostAckedWrite == ~lostAckedWrite

(* Invariant 7.  No cached copy of an inode survives the yielding of its
   lock -- here the kernel's data pages, which are the copy this process
   cannot simply drop and the only one a peer's write cannot invalidate. *)
(* Stated against the node's own belief rather than against Holds: between a
   session expiring in etcd and this node observing it, the node still thinks
   it holds the inode and its pages are still there.  That window is real, it
   is bounded by the lock session's TTL, and it is the same window the
   metadata snapshot has -- see NoticeKeyLost.  What must never happen is a
   page surviving a key this node *knows* it gave up. *)
NoStalePages == \A n \in Nodes : pages[n] => cached[n]

(* The property the metadata cache and both data caches rest on, and the one
   no other spec names: what a node believes the inode is equals what etcd
   records, plus whatever that same node has buffered and not yet published. *)
ViewMatchesTruth ==
    \A n \in Nodes :
        Holds(n) => view[n] = IF buf[n] # NoVal THEN buf[n] ELSE published

(* Nodes are interchangeable and no invariant names one, so TLC may collapse
   states that differ only by a permutation of them. *)
Symmetry == Permutations(Nodes)

=============================================================================
