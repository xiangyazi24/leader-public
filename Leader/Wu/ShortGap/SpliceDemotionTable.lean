import Leader.Wu.ShortGap.SpliceDemotion

namespace ShortGapSpliceDemotion

open ShortGapLiteralGapRows
open ShortGapCaptureReservation
open ShortGapCaptureCommitRows
open ShortGapSpliceCommit
open ShortGapSpliceFusedRow
open ShortGapSpliceCommitCorrected

set_option autoImplicit false

/-! ## WithDemotion dispatcher: demotion before the Corrected table -/

/-- The former-B tombstone is ready to be removed, and its immediate
counterclockwise neighbour has already reached the armed next-episode state. -/
def DemotionEnabled (a b : SNode) : Prop :=
  SpentBridge b ∧ a.splice = .armed

instance instDecidableDemotionEnabled (a b : SNode) :
    Decidable (DemotionEnabled a b) := by
  unfold DemotionEnabled SpentBridge
  infer_instance

/-- WithDemotion adds exactly one priority row to Corrected: an enabled spent bridge is erased
atomically at its right endpoint; every other pair is dispatched by Corrected. -/
def spliceRowWithDemotion (a b : SNode) : SNode × SNode :=
  if h : DemotionEnabled a b then
    (a, demote b)
  else
    spliceRowCorrected a b

/-- Off the new guard, WithDemotion is definitionally the Corrected dispatcher. -/
theorem spliceRowWithDemotion_eq_of_not_demotion (a b : SNode)
    (h : ¬ DemotionEnabled a b) :
    spliceRowWithDemotion a b = spliceRowCorrected a b := by
  simp [spliceRowWithDemotion, h]

/-- On the new guard, WithDemotion performs exactly the demotion row. -/
theorem spliceRowWithDemotion_demotes (a b : SNode)
    (h : DemotionEnabled a b) :
    spliceRowWithDemotion a b = (a, demote b) := by
  simp [spliceRowWithDemotion, h]

/--
On a demotion-enabled pre-state, the old Corrected table cannot report any tail rule
whose right-endpoint guard is ruled out by `SpentBridge`.  `directAdopt` is not
listed here because its guard is left-endpoint-only; the statement is exactly
the five right-reading tail rules excluded by `demotion_disjoint_from_tail`.
-/
theorem demotion_not_tail_ruleCorrected (a b : SNode)
    (hD : DemotionEnabled a b) :
    spliceRuleCorrected a b ∉
      [SRuleCorrected.retireLaunch, SRuleCorrected.retireBackward,
        SRuleCorrected.retireDeposit, SRuleCorrected.retireFused,
        SRuleCorrected.adoptDeposit] := by
  rcases demotion_disjoint_from_tail a b hD.1 with
    ⟨hRetireLaunch, hRetireDeposit, hRetireBackward,
      hRetireFused, hAdoptDeposit⟩
  have hs := spliceRuleCorrected_sound a b
  intro hm
  cases hk : spliceRuleCorrected a b with
  | core k =>
      simp [hk] at hm
  | freshFlush =>
      simp [hk] at hm
  | freshLaunch =>
      simp [hk] at hm
  | freshForward =>
      simp [hk] at hm
  | retireFused =>
      exact hRetireFused (hs.2.2.2.1 hk)
  | retireLaunch =>
      exact hRetireLaunch (hs.2.2.2.2.1 hk)
  | retireBackward =>
      exact hRetireBackward (hs.2.2.2.2.2.1 hk)
  | retireDeposit =>
      exact hRetireDeposit (hs.2.2.2.2.2.2.1 hk)
  | adoptDeposit =>
      exact hAdoptDeposit (hs.2.2.2.2.2.2.2.1 hk)
  | directAdopt =>
      simp [hk] at hm
  | handoffArm =>
      simp [hk] at hm

/-- The demotion row exposes the exact `SEmpty` right endpoint required by the
next fresh declaration service. -/
theorem demotion_then_fresh (a b : SNode)
    (h : DemotionEnabled a b) :
    (spliceRowWithDemotion a b).2 = demote b ∧
      SEmpty (spliceRowWithDemotion a b).2 := by
  constructor
  · rw [spliceRowWithDemotion_demotes a b h]
  · rw [spliceRowWithDemotion_demotes a b h]
    exact demote_empty h.1

/-- Demotion is one-shot: its output has splice state `inactive`, hence cannot
again satisfy the spent-bridge `drained` guard. -/
theorem demotion_once (a b : SNode) :
    ¬ DemotionEnabled a (demote b) := by
  intro h
  have hspent : SpentBridge (demote b) := h.1
  have hsplice : (demote b).splice = SpliceCtl.drained := hspent.2.1
  have hbad : SpliceCtl.inactive = SpliceCtl.drained := by
    simpa [demote] using hsplice
  cases hbad

#print axioms spliceRowWithDemotion_eq_of_not_demotion
#print axioms spliceRowWithDemotion_demotes
#print axioms demotion_not_tail_ruleCorrected
#print axioms demotion_then_fresh
#print axioms demotion_once

end ShortGapSpliceDemotion
