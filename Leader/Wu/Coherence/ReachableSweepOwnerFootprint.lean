import Leader.Wu.Coherence.ReachableSweepFresh


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableSweepFresh2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableSweep
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableCover R2CoherenceV31ReachableCover2
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31MainClearTruth
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSweepFresh
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh


variable {n ψ κ τ : Nat}


/-- Exact missing current-owner trace fact. -/
def CurrentOpenRSweepFootprintFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (sweep owner p : Fin n),
    (C sweep).ctl.tok = .sweep →
    (C owner).ctl.tok = .openR →
    InSweepWideReadV31 ring C sweep p →
    InOpenRFreshFootprintV31 ring C owner p →
      FreshnessClearV31 (C p)


instance currentOpenRSweepFootprintFreshV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (CurrentOpenRSweepFootprintFreshV31 ring C) := by
  unfold CurrentOpenRSweepFootprintFreshV31
  unfold InSweepWideReadV31 InOpenRFreshFootprintV31 FreshnessClearV31
  infer_instance


/-- This is deliberately trace-level: the source witness below shows that
it is not preserved by SEEK on arbitrary Fresh-good states. -/
def ReachableCurrentOpenRSweepFootprintFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
      CurrentOpenRSweepFootprintFreshV31 ring C


private theorem sweep_token_of_branch_sf2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) : l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem fwd_zero_sf2
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]


/-- The named trace fact closes exactly the remaining served clause. -/
theorem sweepCurrentOpenRServedFootprintFresh_of_reachableInvariant
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hInv : ReachableCurrentOpenRSweepFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    SweepCurrentOpenRServedFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e o _hg ht _hFresh hb ho
  have hI := hInv C ht
  have hs := sweep_token_of_branch_sf2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hpos : 0 < ψ - (raw (C e)).label.val := by
    have hlt := (raw (C e)).label.isLt
    omega
  let d0 : Fin (ψ - (raw (C e)).label.val) := ⟨0, hpos⟩
  have heRead : InSweepWideReadV31 ring C e e := by
    right
    refine ⟨d0, ?_⟩
    simpa [d0] using fwd_zero_sf2 ring e
  have hrRead :
      InSweepWideReadV31 ring C e (ring.rightNeighbor e) := Or.inl rfl
  constructor
  · intro hf
    exact hI e o e hs ho heRead hf
  · intro hf
    exact hI e o (ring.rightNeighbor e) hs ho hrRead hf


theorem stepPreservesFresh_sweep_of_reachableCurrentOverlap
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hInv : ReachableCurrentOpenRSweepFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    StepPreservesV31_sweep_fresh (κ := κ) (τ := τ) hψ h2 ring := by
  exact stepPreservesFresh_sweep_closed hψ h2 ring
    (sweepCurrentOpenRServedFootprintFresh_of_reachableInvariant
      hψ h2 ring hInv)
    hCov



namespace SeekBreaksCurrentOpenRFootprintFresh


private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩


/-- Sites 0/1 deliberately have a non-bot path; site 2 is the live openR and
has bot path, so the installed forward-R1 Fresh clause holds there. -/
private def literal (lab : Fin 3) (clearPath : Bool) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := match clearPath with
        | true => .bot
        | false => .some lab 0
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


private def cell
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩


/-- SEEK@1 is behind current openR@2.  There is no sweep yet. -/
private def pre : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cell (literal 0 false) .closing .none
  | 1 => cell (literal 1 false) .closing .seek
  | _ => cell (literal 2 true) .releasing .openR


private def after : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 pre 0


theorem pre_election : ElectionGeometryV31 ring3 pre := by
  decide +kernel


theorem pre_fresh : ReachablePhaseFactsFreshV31 ring3 pre := by
  unfold ReachablePhaseFactsFreshV31
  unfold SweepOpenROverlapFreshV31 SweepOpenROverlapFreshWideV31
    SeekIncomingSweepOpenROverlapFreshWideV31
    OpenRForwardFreshnessClearV31
    R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F
  unfold R2CoherenceV31MainClearTruth.WeakFreshnessLayer.SweepOpenRSafeFreshV31
    PendingOpenROwnerV31 InSweepWideReadV31 InOpenRFreshFootprintV31
    FreshnessClearV31 PhaseOwnedV31
  decide +kernel


theorem pre_overlapFresh :
    CurrentOpenRSweepFootprintFreshV31 ring3 pre := by
  decide +kernel


theorem pre_branch :
    branchAtV3 h3 h23 (pre 0) (pre (ring3.rightNeighbor 0)) = .seek := by
  decide +kernel


theorem after_fresh : ReachablePhaseFactsFreshV31 ring3 after := by
  unfold ReachablePhaseFactsFreshV31
  unfold SweepOpenROverlapFreshV31 SweepOpenROverlapFreshWideV31
    SeekIncomingSweepOpenROverlapFreshWideV31
    OpenRForwardFreshnessClearV31
    R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F
  unfold R2CoherenceV31MainClearTruth.WeakFreshnessLayer.SweepOpenRSafeFreshV31
    PendingOpenROwnerV31 InSweepWideReadV31 InOpenRFreshFootprintV31
    FreshnessClearV31 PhaseOwnedV31
  decide +kernel


theorem after_local_obstruction :
    branchAtV3 h3 h23 (after 0) (after (ring3.rightNeighbor 0)) = .sweep ∧
    (after 2).ctl.tok = .openR ∧
    ¬ PendingOpenROwnerV31 ring3 after 2 ∧
    InSweepWideReadV31 ring3 after 0 0 ∧
    InOpenRFreshFootprintV31 ring3 after 2 0 ∧
    ¬ FreshnessClearV31 (after 0) := by
  unfold PendingOpenROwnerV31 InSweepWideReadV31
    InOpenRFreshFootprintV31 FreshnessClearV31
  decide +kernel


theorem after_not_overlapFresh :
    ¬ CurrentOpenRSweepFootprintFreshV31 ring3 after := by
  decide +kernel


/-- Source-level branch obstruction.  No reachability claim is made for `pre`:
this shows why the missing fact must be trace/provenance information rather
than another consequence of the current Fresh payload. -/
theorem seek_breaks_currentOpenRSweepFootprintFresh :
    ∃ (C : FC 3 3 3 48) (e : Fin 3),
      ElectionGeometryV31 ring3 C ∧
      ReachablePhaseFactsFreshV31 ring3 C ∧
      CurrentOpenRSweepFootprintFreshV31 ring3 C ∧
      branchAtV3 h3 h23 (C e) (C (ring3.rightNeighbor e)) = .seek ∧
      ReachablePhaseFactsFreshV31 ring3 (stepV3 h3 h23 ring3 C e) ∧
      ¬ CurrentOpenRSweepFootprintFreshV31 ring3
        (stepV3 h3 h23 ring3 C e) := by
  exact ⟨pre, 0, pre_election, pre_fresh, pre_overlapFresh,
    pre_branch, after_fresh, after_not_overlapFresh⟩


end SeekBreaksCurrentOpenRFootprintFresh
end R2CoherenceV31ReachableSweepFresh2
