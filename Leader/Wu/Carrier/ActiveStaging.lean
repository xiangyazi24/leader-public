import Leader.Wu.Carrier.LinearPacking
import Leader.AAFJ.Centered.Protocol

/-!
# Fixed active/staging publication interface

This module isolates the clean transaction linearization used by a physical
one-`Fin h` compiler.  Staging contains a complete AAFJ successor.  The first
postcommit interaction copies the sole possibly-changing leader slot into the
fixed active bank and installs a current `postLease` marker.  From that state
the semantic view is the complete staging bank while active bits roll forward.

The spatial words and roll list are semantic objects, not extra local fields.
The concrete root/leader interaction at the end of the file only updates
fields already present in `PackedCell`: two payload bits, `rootCtl`, and
`trail`.  Arbitrary-state production of a clean lease/head corridor remains a
separate dynamical obligation.
-/

namespace PPLLFixedActiveStaging

open AAFJPK PPLLLinearCarrierPacking PPLLPairedFivePassCarrier

set_option autoImplicit false
set_option warningAsError true

inductive BlockSide
  | source
  | target
  deriving DecidableEq, Repr

abbrev SpatialWord (k : Nat) := Fin (width k) -> Bool

def pairState {k : Nat} (q : State k × State k) : BlockSide -> State k
  | .source => q.1
  | .target => q.2

def pairWord {k : Nat} (q : State k × State k)
    (side : BlockSide) : SpatialWord k :=
  sourceBit (pairState q side)

/-- The centered repair never changes the initiator label. -/
theorem centered_transition_source_label {k : Nat} (hk : 0 < k)
    (u v : State k) :
    (CenteredRenewal.transition hk u v).1.label = u.label := by
  classical
  by_cases hready : CenteredRenewal.PairAdvanceReady hk u v
  · rcases hready with ⟨hbarrier, hphase⟩
    rw [CenteredRenewal.transition_of_barrier hk u v hbarrier,
      CenteredRenewal.barrierStep_phase_one hk u v hphase]
    simp
  · exact
      (CenteredRenewal.transition_labels_of_not_pairAdvanceReady
        hk u v hready).1

/-- On a centered phase-one advance the responder takes the initiator's
successor label. -/
theorem centered_transition_target_label_of_ready {k : Nat} (hk : 0 < k)
    (u v : State k) (hready : CenteredRenewal.PairAdvanceReady hk u v) :
    (CenteredRenewal.transition hk u v).2.label = succLabel hk u.label := by
  rcases hready with ⟨hbarrier, hphase⟩
  rw [CenteredRenewal.transition_of_barrier hk u v hbarrier,
    CenteredRenewal.barrierStep_phase_one hk u v hphase]

/-- Outside that branch the responder label is also framed. -/
theorem centered_transition_target_label_of_not_ready {k : Nat} (hk : 0 < k)
    (u v : State k) (hready : ¬ CenteredRenewal.PairAdvanceReady hk u v) :
    (CenteredRenewal.transition hk u v).2.label = v.label :=
  (CenteredRenewal.transition_labels_of_not_pairAdvanceReady
    hk u v hready).2

/-- Every spatial source-label bit survives the centered transition; only the
four source-control slots may need a finite branch-code rewrite. -/
theorem centered_transition_source_labelBit {k : Nat} (hk : 2 ≤ k)
    (u v : State k) (j : Fin (bitLength k)) :
    sourceBit (CenteredRenewal.transition (by omega) u v).1 (labelSlot j) =
      sourceBit u (labelSlot j) := by
  rw [sourceBit_labelSlot hk, sourceBit_labelSlot hk,
    centered_transition_source_label]

def leaderSlot (k : Nat) : Fin (width k) :=
  ⟨1, by unfold width; omega⟩

theorem sourceBit_leader {k : Nat} (hk : 2 <= k) (q : State k) :
    sourceBit q (leaderSlot k) = q.leader := by
  have h := congrArg (fun r : State k => r.leader)
    (decodeSource_sourceBits hk q)
  change (sourceBits q).getLsbD 1 = q.leader at h
  rw [BitVec.getLsbD_eq_getElem (by unfold width; omega)] at h
  simpa [sourceBit, leaderSlot, BitVec.getLsb_eq_getElem] using h

structure PairBanks (k : Nat) where
  active : BlockSide -> SpatialWord k
  staging : BlockSide -> SpatialWord k

def preparedBanks {k : Nat} (hk : 0 < k) (old : State k × State k) :
    PairBanks k :=
  { active := pairWord old
    staging := pairWord (CenteredRenewal.transition hk old.1 old.2) }

def preLease : Trail16 := ⟨12, by omega⟩
def postLease : Trail16 := ⟨13, by omega⟩

def linSourcePhase : RootCtl32 := ⟨24, by omega⟩
def linTargetPhase : RootCtl32 := ⟨25, by omega⟩
def linNonePhase : RootCtl32 := ⟨26, by omega⟩
def rollForwardPhase : RootCtl32 := ⟨27, by omega⟩
def releasePhase : RootCtl32 := ⟨28, by omega⟩

structure LockedPair (k : Nat) where
  banks : PairBanks k
  lease : Trail16

def preparedPair {k : Nat} (hk : 0 < k) (old : State k × State k) :
    LockedPair k :=
  { banks := preparedBanks hk old
    lease := preLease }

/-- A current marker chooses the semantic view.  Only literal `postLease`
selects staging; every other arbitrary trail value has the pre view. -/
def currentWord {k : Nat} (q : LockedPair k) : BlockSide -> SpatialWord k :=
  if q.lease = postLease then q.banks.staging else q.banks.active

@[simp] theorem currentWord_preparedPair {k : Nat} (hk : 0 < k)
    (old : State k × State k) :
    currentWord (preparedPair hk old) = pairWord old := by
  simp [currentWord, preparedPair, preparedBanks, preLease, postLease]

def copySlot {k : Nat} (banks : PairBanks k)
    (chosen : BlockSide) (slot : Fin (width k)) : PairBanks k :=
  { banks with
    active := fun side i =>
      if side = chosen then
        if i = slot then banks.staging side i else banks.active side i
      else banks.active side i }

@[simp] theorem copySlot_staging {k : Nat} (banks : PairBanks k)
    (chosen : BlockSide) (slot : Fin (width k)) :
    (copySlot banks chosen slot).staging = banks.staging := rfl

def commitSide : Option BlockSide -> BlockSide
  | some side => side
  | none => .source

/-- The unchosen endpoint's output is unchanged; `none` means both outputs
are unchanged. -/
def LeaderSupport {k : Nat} (site : Option BlockSide)
    (old new : State k × State k) : Prop :=
  match site with
  | some .source => new.2.leader = old.2.leader
  | some .target => new.1.leader = old.1.leader
  | none => new.1.leader = old.1.leader ∧
      new.2.leader = old.2.leader

/-- Literal AAFJ changes leader output on at most one endpoint. -/
theorem transition_leader_at_most_one {k : Nat} (hk : 0 < k)
    (left right : State k) :
    let q := CenteredRenewal.transition hk left right
    q.1.leader = left.leader ∨ q.2.leader = right.leader := by
  rcases left with ⟨lb, ll, lx, lp, lh⟩
  rcases right with ⟨rb, rl, rx, rp, rh⟩
  by_cases halign : succLabel hk lx = rx
  · cases lb <;> cases ll <;> cases lp <;> cases lh <;>
      cases rb <;> cases rl <;> cases rp <;> cases rh <;>
      simp [CenteredRenewal.transition, IsBarrier, nonBarrierStep, halign]
  · cases lb <;> cases ll <;> cases lp <;> cases lh <;>
      cases rb <;> cases rl <;> cases rp <;> cases rh <;>
      simp [CenteredRenewal.transition, IsBarrier, CenteredRenewal.barrierStep,
        probeHitsBarrier, halign]

theorem exists_leaderSupport {k : Nat} (hk : 0 < k)
    (old : State k × State k) :
    let new := CenteredRenewal.transition hk old.1 old.2
    exists site, LeaderSupport site old new := by
  let new := CenteredRenewal.transition hk old.1 old.2
  have hatMost := transition_leader_at_most_one hk old.1 old.2
  change new.1.leader = old.1.leader ∨
    new.2.leader = old.2.leader at hatMost
  rcases hatMost with hsource | htarget
  · by_cases htarget' : new.2.leader = old.2.leader
    · exact ⟨none, hsource, htarget'⟩
    · exact ⟨some .target, hsource⟩
  · exact ⟨some .source, htarget⟩

/-- The linearization copies the designated leader slot and atomically
installs the postcommit marker. -/
def linearize {k : Nat} (site : Option BlockSide)
    (q : LockedPair k) : LockedPair k :=
  { banks := copySlot q.banks (commitSide site) (leaderSlot k)
    lease := postLease }

@[simp] theorem currentWord_linearize {k : Nat} (site : Option BlockSide)
    (q : LockedPair k) :
    currentWord (linearize site q) = q.banks.staging := by
  simp [currentWord, linearize, postLease]

def physicalLeaders {k : Nat} (q : LockedPair k) : BlockSide -> Bool :=
  fun side => q.banks.active side (leaderSlot k)

def StagingOutputCoherent {k : Nat} (q : LockedPair k) : Prop :=
  forall side,
    q.banks.active side (leaderSlot k) =
      q.banks.staging side (leaderSlot k)

/-- At the first postcommit state, fixed physical leader outputs already equal
the successor outputs on both blocks. -/
theorem linearize_prepared_output_coherent {k : Nat} (hk : 2 <= k)
    (old : State k × State k) (site : Option BlockSide)
    (hsupport : LeaderSupport site old
      (CenteredRenewal.transition (by omega) old.1 old.2)) :
    StagingOutputCoherent
      (linearize site (preparedPair (by omega) old)) := by
  intro side
  cases site with
  | none =>
      rcases hsupport with ⟨hsource, htarget⟩
      cases side <;>
        simp [linearize, copySlot, commitSide, preparedPair, preparedBanks,
          pairWord, pairState, sourceBit_leader hk, hsource, htarget]
  | some site =>
      cases site with
      | source =>
          cases side with
          | source =>
              simp [linearize, copySlot, commitSide, preparedPair,
                preparedBanks, pairWord, pairState, sourceBit_leader hk]
          | target =>
              have hs :
                  (CenteredRenewal.transition (by omega) old.1 old.2).2.leader =
                    old.2.leader := hsupport
              simp [linearize, copySlot, commitSide, preparedPair,
                preparedBanks, pairWord, pairState, sourceBit_leader hk,
                hs.symm]
      | target =>
          cases side with
          | source =>
              have hs :
                  (CenteredRenewal.transition (by omega) old.1 old.2).1.leader =
                    old.1.leader := hsupport
              simp [linearize, copySlot, commitSide, preparedPair,
                preparedBanks, pairWord, pairState, sourceBit_leader hk,
                hs.symm]
          | target =>
              simp [linearize, copySlot, commitSide, preparedPair,
                preparedBanks, pairWord, pairState, sourceBit_leader hk]

/-- A clean linearization switches the complete semantic pair from old to the
literal AAFJ successor in one current-state cut. -/
theorem currentWord_linearize_prepared {k : Nat} (hk : 0 < k)
    (old : State k × State k) (site : Option BlockSide) :
    currentWord (linearize site (preparedPair hk old)) =
      pairWord (CenteredRenewal.transition hk old.1 old.2) := by
  simp [currentWord_linearize, preparedPair, preparedBanks]

def rollService {k : Nat} (q : LockedPair k)
    (side : BlockSide) (slot : Fin (width k)) : LockedPair k :=
  { banks := copySlot q.banks side slot
    lease := q.lease }

@[simp] theorem rollService_lease {k : Nat} (q : LockedPair k)
    (side : BlockSide) (slot : Fin (width k)) :
    (rollService q side slot).lease = q.lease := rfl

theorem currentWord_rollService_of_post {k : Nat} (q : LockedPair k)
    (hpost : q.lease = postLease)
    (side : BlockSide) (slot : Fin (width k)) :
    currentWord (rollService q side slot) = currentWord q := by
  simp [currentWord, rollService, copySlot_staging, hpost]

theorem outputCoherent_rollService {k : Nat} (q : LockedPair k)
    (hq : StagingOutputCoherent q)
    (chosen : BlockSide) (slot : Fin (width k)) :
    StagingOutputCoherent (rollService q chosen slot) := by
  intro side
  by_cases hs : side = chosen
  · subst side
    by_cases hi : leaderSlot k = slot
    · simp [rollService, copySlot, hi]
    · simp [rollService, copySlot, hi, hq chosen]
  · simp [rollService, copySlot, hs, hq side]

/-- Execute any interrupted prefix of a proof-level roll plan. -/
def runRoll {k : Nat} : LockedPair k ->
    List (BlockSide × Fin (width k)) -> LockedPair k
  | q, [] => q
  | q, item :: rest => runRoll (rollService q item.1 item.2) rest

theorem runRoll_preserves_post_view {k : Nat} (q : LockedPair k)
    (hpost : q.lease = postLease)
    (plan : List (BlockSide × Fin (width k))) :
    currentWord (runRoll q plan) = currentWord q := by
  induction plan generalizing q with
  | nil => rfl
  | cons item rest ih =>
      rw [runRoll, ih (rollService q item.1 item.2) (by simp [hpost])]
      exact currentWord_rollService_of_post q hpost item.1 item.2

theorem runRoll_preserves_output {k : Nat} (q : LockedPair k)
    (hq : StagingOutputCoherent q)
    (plan : List (BlockSide × Fin (width k))) :
    StagingOutputCoherent (runRoll q plan) := by
  induction plan generalizing q with
  | nil => exact hq
  | cons item rest ih =>
      exact ih (rollService q item.1 item.2)
        (outputCoherent_rollService q hq item.1 item.2)

/-- The plan length is a proof-level rank: servicing its head strictly lowers
it.  It is not a locally stored counter. -/
theorem rollPlan_rank_decreases {k : Nat}
    (item : BlockSide × Fin (width k))
    (rest : List (BlockSide × Fin (width k))) :
    rest.length < (item :: rest).length := by simp

/-- Final roll-forward installs staging as fixed active and retains the
post-view until release. -/
def finishRoll {k : Nat} (q : LockedPair k) : LockedPair k :=
  { banks := { active := q.banks.staging, staging := q.banks.staging }
    lease := postLease }

def release {k : Nat} (q : LockedPair k) : LockedPair k :=
  { q with lease := preLease }

@[simp] theorem currentWord_release_finishRoll {k : Nat} (q : LockedPair k) :
    currentWord (release (finishRoll q)) = q.banks.staging := by
  simp [currentWord, release, finishRoll, preLease, postLease]

/-! ## The literal root/leader radius-one linearization row -/

/-- One ordered interaction on the root-to-slot-one edge.  It copies both
available staging bits, writes the current post lease, and enters roll-forward.
The outer three geometry Booleans of the preferred framed carrier are absent
from this function and hence are framed by construction. -/
def linearizeRootLeader {h : Nat}
    (root leader : PackedCell h) : PackedCell h × PackedCell h :=
  ({ root with
      activeBit := root.stagingBit
      rootCtl := rollForwardPhase
      trail := postLease },
   { leader with activeBit := leader.stagingBit })

@[simp] theorem linearizeRootLeader_postLease {h : Nat}
    (root leader : PackedCell h) :
    (linearizeRootLeader root leader).1.trail = postLease := rfl

@[simp] theorem linearizeRootLeader_leader_active {h : Nat}
    (root leader : PackedCell h) :
    (linearizeRootLeader root leader).2.activeBit = leader.stagingBit := rfl

@[simp] theorem linearizeRootLeader_positions {h : Nat}
    (root leader : PackedCell h) :
    (linearizeRootLeader root leader).1.pos = root.pos ∧
      (linearizeRootLeader root leader).2.pos = leader.pos := by
  exact ⟨rfl, rfl⟩

theorem base_transaction_carrier_count (h : Nat) :
    (packedCellStates h).values.length = 262144 * h :=
  packedCellStates_length h

end PPLLFixedActiveStaging
