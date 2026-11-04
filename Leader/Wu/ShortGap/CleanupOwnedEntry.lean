import Leader.Wu.Comparison.ExpiringRepair
import Leader.Wu.ShortGap.CaptureEntry
import Leader.Wu.ShortGap.CaptureLifecycle
import Leader.Wu.Elimination.ArbitraryInputElimination
import Leader.Core.PhaseComposition


/-!
# Owned cleanup entry before short-gap capture


This file is specification-only.  It does not add a protocol state coordinate,
change a pair row, or assert an unproved theorem.


The physical carrier is exactly the current executable expiration carrier
`ExpiringAgentState`; `literalStep` is exactly the uniformly scheduled
`expiringProtocol` row.  The `CleanupSurface` record below is proof accounting:
it records the concrete object observations that an integrated capture row must
export.  It is deliberately not part of `PopulationProtocol.Q`.


Why the surface is explicit on current main:
* `ShortGapCaptureEntry` gives the finite capture `Actor`, proposal carrier and
  source lease only in its tagged extension;
* `ShortGapCaptureLifecycle` gives committed receipts/postcommit obligations
  only in its semantic quotient;
* neither is presently embedded into `ExpiringAgentState`.


Consequently a concrete full-surface instance is a later physical-refinement
obligation.  This file does not silently reinterpret unrelated P_PLL fields as
capture actors, leases, or receipts.


Feeders fixed for the later proof:
* `ShortGapCaptureEntry.CleanActors` and `cleanFrame_actors`: certified cleanup
  discharges to the clean capture-actor lane;
* `captureReady_of_bothCandidate`, `captureReady_stable`,
  `captureLaunch_only_ready`, `captureLaunch_enabled`: once on that lane,
  candidate ownership gives a stable, executable capture launch and forged
  states cannot launch merely from a local tag;
* `ShortGapCaptureLifecycle.Step.debt_lt`: supplies the local well-founded debt
  for a legitimate actor lifecycle;
* `Step.targetDeletion_irreversible` and `Step.protected_not_abort`: stale
  cleanup may not resurrect a committed target or turn a protected actor into
  an abort path;
* `K2ArbitraryElimination.arbitrary_elimination`: downstream arbitrary-state
  elimination consumer after cleanup/entry, not a replacement cleanup clock;
* `PhaseComposition.phase_compose_bellman`: consumes the stopped Bellman
  certificate below.  No independent random variable is introduced.


The arbitrary-state rank must explicitly cover all four hazards:
forged maximum-rank work, stale capture actors, stale leases, and partial
postcommit receipts.  Unowned live carriers/leases/receipts are also charged;
otherwise backflow is still possible.
-/


namespace CleanupOwnedEntry


open FiniteUniformStoppingTree
open PPLLExpiringComparisonRepair


set_option autoImplicit false


variable {n psi kappa tau : Nat}


/-- The actual current executable configuration type from the cleanup
seam.  No capture wrapper is inserted into the runtime state here. -/
abbrev Config (n psi kappa tau : Nat) :=
  Fin n -> ExpiringAgentState psi kappa tau


/-- One raw scheduler interaction of the literal corrected physical row. -/
def literalStep
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) :
    Config n psi kappa tau :=
  PopulationProtocol.step (expiringProtocol hpsi kappa tau) ring C e


/-- Logical classes of stale work that the cleanup rank is required to see.
`carrier` is kept separate from the four named arbitrary-state hazards because
an unowned live carrier must itself become charged stale work. -/
inductive StaleKind where
  | carrier
  | forgedMaximumRankWork
  | captureActor
  | lease
  | partialPostcommitReceipt
  deriving DecidableEq, Repr


def staleKinds : List StaleKind :=
  [ .carrier,
    .forgedMaximumRankWork,
    .captureActor,
    .lease,
    .partialPostcommitReceipt ]


/-- Proof-only observations/accounting over the actual physical configuration.
A future integrated capture implementation must instantiate these functions by
reading its real physical fields.  Nothing here extends the runtime carrier. -/
structure CleanupSurface (n psi kappa tau : Nat) where
  /-- Executable certification bit used only by the stopped wrapper. -/
  certified : Config n psi kappa tau -> Bool


  /-- Live objects whose ownership must be unique and structurally connected. -/
  liveCarrier : Config n psi kappa tau -> Fin n -> Bool
  liveLease : Config n psi kappa tau -> Fin n -> Bool
  liveReceipt : Config n psi kappa tau -> Fin n -> Bool
  liveCaptureActor : Config n psi kappa tau -> Fin n -> Bool


  /-- Unique owner roots.  `none` means the corresponding live object is
  presently unowned and therefore must be charged as stale work. -/
  carrierOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  leaseOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  receiptOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)


  /-- Physical support of one actor rooted at the first `Fin n` argument. -/
  actorMember : Config n psi kappa tau -> Fin n -> Fin n -> Bool


  /-- The four arbitrary-forged-state hazards. -/
  forgedMaximumRankWork : Config n psi kappa tau -> Fin n -> Bool
  staleCaptureActor : Config n psi kappa tau -> Fin n -> Bool
  staleLease : Config n psi kappa tau -> Fin n -> Bool
  partialPostcommitReceipt : Config n psi kappa tau -> Fin n -> Bool


  /-- Object presence and its remaining local erase depth.  Presence itself
  contributes one unit below, so a present stale object can never have zero
  cleanup charge merely because its local depth is zero. -/
  stalePresent : Config n psi kappa tau -> StaleKind -> Fin n -> Bool
  eraseDepth : Config n psi kappa tau -> StaleKind -> Fin n -> Nat


  /-- Uniform cap required by later phase composition. -/
  rankCap : Nat


/-- Clockwise connectivity inside one actor support.  This is a finite proof
object, not a scheduler path and not an additional state coordinate. -/
inductive ConnectedWithin {n : Nat}
    (ring : DirectedRing n) (member : Fin n -> Prop)
    (root : Fin n) : Fin n -> Prop where
  | base (hroot : member root) :
      ConnectedWithin ring member root root
  | next {v : Fin n}
      (hprev : ConnectedWithin ring member root v)
      (hnext : member (ring.rightNeighbor v)) :
      ConnectedWithin ring member root (ring.rightNeighbor v)


/-- Every occupied site of an actor is connected to its unique root. -/
def ActorSupportConnected
    (A : CleanupSurface n psi kappa tau)
    (ring : DirectedRing n) (C : Config n psi kappa tau)
    (root : Fin n) : Prop :=
  A.actorMember C root root = true /\
    forall i, A.actorMember C root i = true ->
      ConnectedWithin ring
        (fun j => A.actorMember C root j = true) root i


/-- One live object belongs to exactly the actor named by its owner function,
and its physical site is connected to that actor root.  Uniqueness comes from
`ownerOf` being a function into `Option (Fin n)`. -/
def OwnedByConnectedActor
    (A : CleanupSurface n psi kappa tau)
    (ring : DirectedRing n)
    (ownerOf : Config n psi kappa tau -> Fin n -> Option (Fin n))
    (C : Config n psi kappa tau) (i : Fin n) : Prop :=
  exists root,
    ownerOf C i = some root /\
      ActorSupportConnected A ring C root /\
      ConnectedWithin ring
        (fun j => A.actorMember C root j = true) root i


/-- One stale token's natural charge. -/
def staleCharge
    (A : CleanupSurface n psi kappa tau)
    (C : Config n psi kappa tau)
    (kind : StaleKind) (i : Fin n) : Nat :=
  if A.stalePresent C kind i then A.eraseDepth C kind i + 1 else 0


/-- All stale charges located at one physical site. -/
def localCleanupDebt
    (A : CleanupSurface n psi kappa tau)
    (C : Config n psi kappa tau) (i : Fin n) : Nat :=
  (staleKinds.map (fun kind => staleCharge A C kind i)).sum


/-- Unscaled cleanup debt on an arbitrary physical configuration. -/
def cleanupDebt
    (A : CleanupSurface n psi kappa tau)
    (C : Config n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n => localCleanupDebt A C i)).sum


/-- Natural-valued cleanup rank.


The factor `n` prepays the uniform waiting cost for one useful edge.  The final
unit pays the stopped certification interaction.  Thus a one-unit debt service
has enough credit for the scale-1 Bellman inequality. -/
def cleanupRank
    (A : CleanupSurface n psi kappa tau)
    (C : Config n psi kappa tau) : Nat :=
  n * cleanupDebt A C + 1


/-- Stopped potential; only terminal nodes have zero potential. -/
def cleanupPotential
    (A : CleanupSurface n psi kappa tau) :
    StopNode (Config n psi kappa tau) -> Nat
  | .active C => cleanupRank A C
  | .success => 0
  | .failure => 0


/-- A raw physical row services stale work only when it really lowers a present
stale token and lowers the aggregate debt.  This prevents a local erase from
being counted as progress while unrelated forged work is simultaneously
created elsewhere. -/
def ServicesStaleObject
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) : Prop :=
  let D := literalStep hpsi ring C e
  exists kind i,
    A.stalePresent C kind i = true /\
      staleCharge A D kind i < staleCharge A C kind i /\
      cleanupDebt A D < cleanupDebt A C


/-- Rank-decreasing physical cleanup edges. -/
def EraseRel
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (D C : Config n psi kappa tau) : Prop :=
  exists e : Fin n,
    D = literalStep hpsi ring C e /\
      ServicesStaleObject A hpsi ring C e


/-- A particular stale token is on an actual well-founded erase path: the whole
service relation is accessible from the current configuration, and this token
has a literal physical service edge that decreases both its charge and the
global cleanup debt. -/
def WellFoundedEraseAt
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau)
    (kind : StaleKind) (i : Fin n) : Prop :=
  Acc (EraseRel A hpsi ring) C /\
    exists e : Fin n,
      let D := literalStep hpsi ring C e
      staleCharge A D kind i < staleCharge A C kind i /\
        cleanupDebt A D < cleanupDebt A C


/-- The ownership boundary delivered by the cleanup phase.


Every live carrier, lease and receipt has one connected actor owner; every live
capture actor has connected support; and every remaining stale object is
already on a well-founded literal erase path.  This is deliberately stronger
than a collection of locally valid-looking tags. -/
def CleanupCertified
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Prop :=
  (forall i, A.liveCarrier C i = true ->
      OwnedByConnectedActor A ring A.carrierOwner C i) /\
  (forall i, A.liveLease C i = true ->
      OwnedByConnectedActor A ring A.leaseOwner C i) /\
  (forall i, A.liveReceipt C i = true ->
      OwnedByConnectedActor A ring A.receiptOwner C i) /\
  (forall root, A.liveCaptureActor C root = true ->
      ActorSupportConnected A ring C root) /\
  (forall kind i, A.stalePresent C kind i = true ->
      WellFoundedEraseAt A hpsi ring C kind i)


/-- Exact coverage obligation for the arbitrary-state seam.


The first four conjuncts are the four hazards.  The remaining
conjuncts prevent an unowned live carrier/lease/receipt or disconnected live
capture actor from escaping the rank by failing to call itself stale. -/
def cleanupRankCoversSeams
    (A : CleanupSurface n psi kappa tau)
    (ring : DirectedRing n) : Prop :=
  forall C i,
    (A.forgedMaximumRankWork C i = true ->
      A.stalePresent C .forgedMaximumRankWork i = true) /\
    (A.staleCaptureActor C i = true ->
      A.stalePresent C .captureActor i = true) /\
    (A.staleLease C i = true ->
      A.stalePresent C .lease i = true) /\
    (A.partialPostcommitReceipt C i = true ->
      A.stalePresent C .partialPostcommitReceipt i = true) /\
    (A.liveCarrier C i = true /\
        ¬ (OwnedByConnectedActor A ring A.carrierOwner C i) ->
      A.stalePresent C .carrier i = true) /\
    (A.liveLease C i = true /\
        ¬ (OwnedByConnectedActor A ring A.leaseOwner C i) ->
      A.stalePresent C .lease i = true) /\
    (A.liveReceipt C i = true /\
        ¬ (OwnedByConnectedActor A ring A.receiptOwner C i) ->
      A.stalePresent C .partialPostcommitReceipt i = true) /\
    (A.liveCaptureActor C i = true /\
        ¬ (ActorSupportConnected A ring C i) ->
      A.stalePresent C .captureActor i = true)


/-- The executable Bool used by the stopped wrapper must classify exactly the
structural predicate above; no local-tag shortcut is allowed. -/
def cleanupClassifierCorrect
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C,
    A.certified C = true <-> CleanupCertified A hpsi ring C


/-- Stopped cleanup wrapper.  Certification is observation only; every active
non-certified transition is exactly one `literalStep`.  There is no failure
branch and no scheduler reweighting. -/
def cleanupStopStep
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) :
    StopNode (Config n psi kappa tau) :=
  if A.certified C then
    .success
  else
    let D := literalStep hpsi ring C e
    if A.certified D then .success else .active D


/-- The raw cleanup rank never increases on any literal physical row. -/
def cleanupRank_nonincrease
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C e,
    cleanupRank A (literalStep hpsi ring C e) <= cleanupRank A C


/-- A row that services stale work strictly decreases the raw cleanup rank. -/
def cleanupRank_strict_on_service
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C e,
    ServicesStaleObject A hpsi ring C e ->
      cleanupRank A (literalStep hpsi ring C e) < cleanupRank A C


/-- Outside the certified boundary, at least one original scheduler edge is a
real stale-object service.  Together with the `n` scaling in `cleanupRank`,
this is the local source of the Bellman payment. -/
def cleanupServiceEnabled
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C, A.certified C = false ->
    exists e : Fin n, ServicesStaleObject A hpsi ring C e


/-- Uniform finite reserve used when this phase is composed with its successor. -/
def cleanupRank_bound
    (A : CleanupSurface n psi kappa tau) : Prop :=
  forall C, cleanupRank A C <= A.rankCap


/-- The exact one-step, division-free, scale-1 Bellman inequality. -/
def cleanup_one_step_bellman
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C,
    n + (List.ofFn (fun e : Fin n =>
      cleanupPotential A (cleanupStopStep A hpsi ring C e))).sum <=
        n * cleanupPotential A (.active C)


/-- Repository-standard Bellman interface consumed by phase composition. -/
def cleanup_owned_entry_bellman
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  NatBellmanSuperSolution
    (cleanupStopStep A hpsi ring) 1 (cleanupPotential A)


/-- Once the ownership/erase-path certificate is reached, every literal
physical row preserves it.  This is the no-backflow boundary needed before
short-gap and peak phase monotonicity can be trusted. -/
def cleanupCertified_closed
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C, CleanupCertified A hpsi ring C ->
    forall e : Fin n,
      CleanupCertified A hpsi ring (literalStep hpsi ring C e)


/-- Successful stopping is exactly certification before or after the one
literal row; this rules out an accidental second success semantics. -/
def cleanupSuccessExactlyCertified
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C e,
    cleanupStopStep A hpsi ring C e = .success <->
      CleanupCertified A hpsi ring C \/
        CleanupCertified A hpsi ring (literalStep hpsi ring C e)


/-- No Las-Vegas failure state is introduced by cleanup. -/
def cleanupNoFailure
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C e, cleanupStopStep A hpsi ring C e ≠ .failure


/-- Complete R2 obligation package.  These are propositions only; this R1 file
asserts none of them. -/
def cleanupOwnedEntryContract
    (A : CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  cleanupRankCoversSeams A ring /\
    cleanupClassifierCorrect A hpsi ring /\
    cleanupRank_nonincrease A hpsi ring /\
    cleanupRank_strict_on_service A hpsi ring /\
    cleanupServiceEnabled A hpsi ring /\
    cleanupRank_bound A /\
    cleanup_one_step_bellman A hpsi ring /\
    cleanup_owned_entry_bellman A hpsi ring /\
    cleanupCertified_closed A hpsi ring /\
    cleanupSuccessExactlyCertified A hpsi ring /\
    cleanupNoFailure A hpsi ring


/-! ## Frozen feeder names for the proof round -/


#check @ShortGapCaptureEntry.CleanActors
#check @ShortGapCaptureEntry.cleanFrame_actors
#check @ShortGapCaptureEntry.captureReady_of_bothCandidate
#check @ShortGapCaptureEntry.captureReady_stable
#check @ShortGapCaptureEntry.captureLaunch_only_ready
#check @ShortGapCaptureEntry.captureLaunch_enabled
#check @ShortGapCaptureLifecycle.Step.debt_lt
#check @ShortGapCaptureLifecycle.Step.targetDeletion_irreversible
#check @ShortGapCaptureLifecycle.Step.protected_not_abort
#check @K2ArbitraryElimination.arbitrary_elimination
#check @PhaseComposition.phase_compose_bellman


end CleanupOwnedEntry


#print axioms CleanupOwnedEntry.literalStep
#print axioms CleanupOwnedEntry.CleanupCertified
#print axioms CleanupOwnedEntry.cleanupDebt
#print axioms CleanupOwnedEntry.cleanupRank
#print axioms CleanupOwnedEntry.cleanupStopStep
#print axioms CleanupOwnedEntry.cleanupRankCoversSeams
#print axioms CleanupOwnedEntry.cleanupRank_nonincrease
#print axioms CleanupOwnedEntry.cleanupRank_strict_on_service
#print axioms CleanupOwnedEntry.cleanup_owned_entry_bellman
#print axioms CleanupOwnedEntry.cleanupCertified_closed
#print axioms CleanupOwnedEntry.cleanupOwnedEntryContract
