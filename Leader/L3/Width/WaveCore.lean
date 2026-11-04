import Leader.L3.Bank.RepairDigitStructuralClean

/-!
# The value wave after the entry cut, at a digit reference

`cleanWaveAfterEntry` (BankRepairDigitStructuralClean) and the block machinery under it are
stated on the masked BANK reference only by their types: the BANK dynamics enter through two
facts, `bankRepairDigitLeadBankEdge` (on the fixed layout the digit layer steps by `phiD`, the
native root is the only `l` bit, and the pair word keeps both `beta` bits) and
`bankRepairDigitLayoutFixedStep` (the fixed layout persists).  Both hold at every digit
reference whose singleton class fixes the word root (`hfix`, the `singletonFixed` field of
`WidthBoundaryReference`): `widthLeadEdge`, `widthLayoutFixedStep`, from `digitStep`,
`wordStep`, `singletonClosed`, `singletonDrained`.

This module restates the 88 BANK-typed declarations that `cleanWaveAfterEntry` depends on at a
reference `ref` with `hfix` (mechanical port: `BankReferenceState ring hbank` → `ref.State`,
`bankRepairNext ring hbank` → `ref.next`, `z.val.1` → `ref.phys z`, names prefixed `width`; the
BANK-free lemmas are used as they are), ending in `widthCleanWaveAfterEntry`.
-/

namespace L3.WidthWave

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open L3
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.BlockCuts
open L3.BlockEntry
open L3.BlockStart
open L3.CloseReceipt
open L3.CohortClose
open L3.CohortDomination
open L3.CohortEntry
open L3.CohortIdentity
open L3.CohortLedger
open L3.CohortOrder
open L3.CohortSites
open L3.CohortStages
open L3.CohortTail
open L3.CohortTransfer
open L3.CohortWindow
open L3.Correspondence
open L3.DigitEntryPhase
open L3.DigitPairsClean
open L3.FiveClose
open L3.FiveReach
open L3.FiveTransfer
open L3.GhostBridge
open L3.HClose
open L3.HeadlineRenewal
open L3.PacketClass
open L3.PairBlock
open L3.Projection
open L3.Rearm
open L3.Recording
open L3.RenewalReferenceClock
open L3.SitePin
open L3.UseCells
open L3.UseRows
open L3.UseTrack
open L3.ValueCorr
open L3.ValueLedger
open L3.ValueWaveClose
open L3.WidthDigit
open UniformFirstHit
open L3.DigitStructuralClean

set_option autoImplicit false

section Leaf

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
    WFixedRoot ring root (piW (ref.phys z)))

/-- The fixed layout persists (generic `bankRepairDigitLayoutFixedStep`). Consumer: the ported
cohort step `widthCohortStep`. -/
theorem widthLayoutFixedStep (root : Fin n) (z : ref.State)
    (hz : WidthDigitLayoutFixed ref root z) (e : Fin n) :
    WidthDigitLayoutFixed ref root (ref.next z e) := by
  refine ⟨ref.singletonClosed root z hz.1 e, ?_⟩
  rw [ref.wordStep z (ref.singletonDrained root z hz.1) e]
  exact (AcceptedReceipts.qword_step ring _ hz.2 e).2

include hfix in
/-- One edge on the fixed layout (generic `bankRepairDigitLeadBankEdge`). Consumer: the ported
step lemmas of the window machinery. -/
theorem widthLeadEdge (hn : 5 ≤ n) (root : Fin n) (z : ref.State)
    (hz : WidthDigitLayoutFixed ref root z) (e : Fin n) :
    piD (ref.phys (ref.next z e)) = phiD ring (piD (ref.phys z)) e ∧
    (∀ i, (piD (ref.phys z) i).word.native.l = true ↔ i = root) ∧
    (pairW (piD (ref.phys z) e).word (piD (ref.phys z) (ring.rightNeighbor e)).word).1.beta =
      (piD (ref.phys z) e).word.beta ∧
    (pairW (piD (ref.phys z) e).word (piD (ref.phys z) (ring.rightNeighbor e)).word).2.beta =
      (piD (ref.phys z) (ring.rightNeighbor e)).word.beta := by
  refine ⟨ref.digitStep z (ref.singletonDrained root z hz.1) e, ?_⟩
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW (ref.phys z)) e) i =
      AcceptedReceipts.wordVisible (piW (ref.phys z)) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  have hW := hfix root z hz.1
  refine ⟨fun i => ⟨fun hi => hW.2.1 i hi, ?_⟩, hbX, hbY⟩
  rintro rfl
  exact hW.1

end Leaf

-- from BankRepairDigitCohortSites L3.CohortSites.cohortBankStep
section


/-- One reference letter: the layout class is closed, and the masked projection moves by the T22
lane step of the drawn pair edge. Consumer: `widthCohortCycLaneStage`, `widthCohortCycTransportCharge`, `widthGhostCorrDistinctStep`. -/
theorem widthCohortStep {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
     (root : Fin n)
    (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (z : ref.State) (hz : WidthCohortLayout ref root src R z)
    (e : Fin n) :
    WidthCohortLayout ref root src R (ref.next z e) ∧
      cohortProj ring root lane src R (piD (ref.phys (ref.next z e))) =
        cohortLaneStep R (cohortProj ring root lane src R (piD (ref.phys z)))
          (cohortEdgeOf root src R e) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root z hL e
  have hbeta := (bankRepairDigitPhiDAt ring (by omega) (piD (ref.phys z)) e hbX hbY).2.2.2
  refine ⟨⟨widthLayoutFixedStep ref root z hL e, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [heq, hbeta]
    exact hb0
  · rw [heq, hbeta]
    exact hbR
  · rw [heq, hbeta]
    exact hb2R
  · intro k h1 h2 h3
    rw [heq, hbeta]
    exact hbF k h1 h2 h3
  · rw [heq]
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact cohortProjStep ring (by omega) root (piD (ref.phys z)) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF lane j hj hbX hbY

end

-- from BankRepairDigitRearm L3.Rearm.cohortCycleNext
section


/-- The reference chain paired with the proof-only cycle ghost. -/
noncomputable def widthCohortCycleNext {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
     (root : Fin n)
    (lane : DigitLane) (src R : Nat)
    (w : ref.State × ((Nat → Nat) × Nat)) (e : Fin n) :
    ref.State × ((Nat → Nat) × Nat) :=
  (ref.next w.1 e,
    cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2
      (cohortEdgeOf root src R e))

end

-- from BankRepairDigitRearm L3.Rearm.CohortCycSim
section


/-- The transport simulation of cycle `j` by T22's model chain. Consumer: `widthCohortCycTransportCharge`. -/
def WidthCohortCycSim {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
     (root : Fin n)
    (lane : DigitLane) (src R j : Nat)
    (w : ref.State × ((Nat → Nat) × Nat)) (y : CohortLane × (Nat → Nat)) :
    Prop :=
  WidthCohortLayout ref root src R w.1 ∧
    ((y.1 = cohortProj ring root lane src R (piD (ref.phys w.1)) ∧ y.2 = w.2.1 ∧
        CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 (2 * R + 1) ∧
        ∀ i, i < R → cohortTok R (cohortProj ring root lane src R (piD (ref.phys w.1)))
          (cohortPos R w.2.1 i) ≠ .other) ∨
      (CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 ∧
        gridDone R R y.2))

end

-- from BankRepairDigitRearm L3.Rearm.cohortCycLaneStage
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- A one-letter lane stage on the reference chain with the cycle ghost. Consumer: `widthCohortCycleStageCharge`, `widthCycleOldChain`, `widthCycleEntryCharge`. -/
theorem widthCohortCycLaneStage (A B : CohortLane → (Nat → Nat) × Nat → Prop) (κ : Nat)
    (hκ : κ < 2 * R)
    (hcl : ∀ s g, A s g → ¬ B s g → ∀ ke,
      A (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) ∨
        B (cohortLaneStep R s ke) (cohortCycleGhost R s g ke))
    (hch : ∀ s g, A s g → ¬ B s g →
      B (cohortLaneStep R s (some κ)) (cohortCycleGhost R s g (some κ))) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        A (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        B (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (2 * n) := by
  apply chargedOneStep _ _ _ (fun _ => digitSite ring root (src + κ))
  · intro w hw hnB e
    obtain ⟨hL, hA⟩ := hw
    have hnB' : ¬ B (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 :=
      fun hb => hnB ⟨hL, hb⟩
    obtain ⟨hL', hst⟩ := widthCohortStep ref hfix hn root lane src R hR hsrc hend w.1 hL e
    have key := hcl _ _ hA hnB' (cohortEdgeOf root src R e)
    rw [← hst] at key
    rcases key with h1 | h1
    · exact Or.inl ⟨hL', h1⟩
    · exact Or.inr ⟨hL', h1⟩
  · intro w hw hnB
    obtain ⟨hL, hA⟩ := hw
    have hnB' : ¬ B (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 :=
      fun hb => hnB ⟨hL, hb⟩
    obtain ⟨hL', hst⟩ := widthCohortStep ref hfix hn root lane src R hR hsrc hend w.1 hL
      (digitSite ring root (src + κ))
    have key := hch _ _ hA hnB'
    rw [← cohortEdgeOfSite ring root src R hend κ hκ, ← hst] at key
    exact ⟨hL', key⟩

end

-- from BankRepairDigitRearm L3.Rearm.cohortCycTransportCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- Transport of cycle `j` on the reference chain with the cycle ghost: T22's `32 n R`, through the
simulation by the model chain `cohortNext`. Consumer: `widthCohortCycleStageCharge`, `widthCycleEntryCharge`. -/
theorem widthCohortCycTransportCharge (j : Nat) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycMat R j R (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (32 * n * R) := by
  intro w hw T
  obtain ⟨hL, hM⟩ := hw
  have hsim := L3.CohortTransfer.costNumeratorSimLe (widthCohortCycleNext ref root lane src R)
    (cohortNext R (cohortEdgeOf root src R)) (WidthCohortCycSim ref root lane src R j)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (CohortDone R)
    (by
      intro w y e hs hng
      obtain ⟨hL, hc⟩ := hs
      rcases hc with ⟨hy1, hy2, hin, hm⟩ | ⟨hs, -⟩
      · obtain ⟨hL', hst⟩ := widthCohortStep ref hfix hn root lane src R hR hsrc hend w.1 hL e
        have hy : y = (cohortProj ring root lane src R (piD (ref.phys w.1)), w.2.1) := Prod.ext hy1 hy2
        subst hy
        have hst' : cohortProj ring root lane src R
            (piD (ref.phys (widthCohortCycleNext ref root lane src R w e).1)) =
            cohortLaneStep R (cohortProj ring root lane src R (piD (ref.phys w.1)))
              (cohortEdgeOf root src R e) := hst
        unfold WidthCohortCycSim
        refine ⟨hL', ?_⟩
        rw [hst']
        rcases cohortCycTransportStep hin hm (cohortEdgeOf root src R e) with
          ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨rfl, h1, h2, h3⟩
        · exact Or.inr ⟨h1, h2⟩
      · exact absurd ⟨hL, hs⟩ hng)
    (by
      intro w y hs hd
      obtain ⟨hL, hc⟩ := hs
      rcases hc with ⟨-, hy2, hin, -⟩ | ⟨hs, -⟩
      · exact (hin.2.2.2 (by rw [← hy2]; exact hd)).elim
      · exact ⟨hL, hs⟩)
  have hy : ∃ y, WidthCohortCycSim ref root lane src R j w y ∧ CohortClass R y := by
    rcases hM with ⟨hin, hm⟩ | hs
    · exact ⟨(cohortProj ring root lane src R (piD (ref.phys w.1)), w.2.1),
        ⟨hL, Or.inl ⟨rfl, rfl, hin, fun i hi => hm i hi hi⟩⟩,
        Or.inl (cohortGenPost hin.2.1 (fun i hi => hm i hi hi)).1⟩
    · exact ⟨(cohortProj ring root lane src R (piD (ref.phys w.1)), fun _ => R),
        ⟨hL, Or.inr ⟨hs, fun _ _ => Nat.le_refl R⟩⟩, Or.inr (fun _ _ => Nat.le_refl R)⟩
  obtain ⟨y, hwy, hcls⟩ := hy
  have hdom := cohortDominationCharge (n := n) (R := R) (by omega)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk) y hcls T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (hsim T w y hwy)) hdom

end

-- from BankRepairDigitRearm L3.Rearm.cohortCycleStageCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- One cycle on the reference chain with the cycle ghost: from the start of cycle `j` to the start
of cycle `j + 1` (the `j + 1`-st arrival), `≤ 39 n R` doubled. Consumer: `widthCycleCutCharge`. -/
theorem widthCohortCycleStageCharge (j : Nat) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycStart R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (39 * n * R) := by
  have hold := bankRepairDigitChargedChain (widthCohortCycleNext ref root lane src R)
    (fun o w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R j o (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2) (2 * n)
    (fun o => widthCohortCycLaneStage ref hfix hn root lane src R hR hsrc hend
      (CohortCycOld R j o) (CohortCycOld R j (o + 1)) (cohortGenEdgeAt R o)
      (cohortGenEdgeAtLt hR o) (cohortCycOldStage j o).1 (cohortCycOldStage j o).2) (2 * R + 1)
  have hmat := bankRepairDigitChargedChain (widthCohortCycleNext ref root lane src R)
    (fun a w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycMat R j a (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2) (2 * n)
    (fun a => widthCohortCycLaneStage ref hfix hn root lane src R hR hsrc hend
      (CohortCycMat R j a) (CohortCycMat R j (a + 1)) (R - 1 - a) (by omega)
      (cohortCycMatStage j a).1 (cohortCycMatStage j a).2) R
  have h1 := bankRepairDigitChargedWeaken (widthCohortCycleNext ref root lane src R)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R j 0 (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycStart R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R j (2 * R + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycMat R j 0 (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    _ (fun _ hw => ⟨hw.1, Or.inl ⟨0, Or.inl (Nat.le_refl 0), hw.2⟩⟩)
    (fun _ hw => ⟨hw.1, cohortCycOldToMat hw.2⟩) hold
  have h2 := bankRepairDigitZeroCompose _ _ _ _ _ _ h1 hmat
  have h3 := bankRepairDigitZeroCompose _ _ _ _ _ _ h2
    (widthCohortCycTransportCharge ref hfix hn root lane src R hR hsrc hend j)
  have e1 : (2 * R + 1) * (2 * n) = 2 * (R * (2 * n)) + 2 * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : R * (2 * n) = 2 * (n * R) := by rw [Nat.mul_comm R, Nat.mul_assoc]
  have e3 : 32 * n * R = 32 * (n * R) := Nat.mul_assoc _ _ _
  have e4 : 39 * n * R = 39 * (n * R) := Nat.mul_assoc _ _ _
  have hnR : n * 2 ≤ n * R := Nat.mul_le_mul_left n hR
  have hle : (2 * R + 1) * (2 * n) + R * (2 * n) + 32 * n * R ≤ 39 * n * R := by
    rw [e1, e2, e3, e4]
    omega
  intro x hx T
  exact Nat.le_trans (h3 x hx T) (Nat.mul_le_mul_left _ hle)

end

-- from BankRepairDigitCohortIdentity L3.CohortIdentity.ghostCorrDistinctBankStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.CohortIdentity.ghostCorrDistinctBankStep`. Consumer: `widthWinInvDStep`. -/
theorem widthGhostCorrDistinctStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref root src R z.1)
    (hc : GhostCorrDistinct ring root lane src R Base (piD (ref.phys z.1)) z.2) (e : Fin n) :
    WidthCohortLayout ref root src R (widthDigitAuditNext ref z e).1 ∧
    GhostCorrDistinct ring root lane src R Base
      (piD (ref.phys (widthDigitAuditNext ref z e).1))
      (widthDigitAuditNext ref z e).2 := by
  refine ⟨(widthCohortStep ref hfix hn root lane src R hR hsrc hend z.1 hz e).1, ?_⟩
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root z.1 hL e
  show GhostCorrDistinct ring root lane src R Base (piD (ref.phys (ref.next z.1 e)))
    (digitAuditStep ring (piD (ref.phys z.1)) z.2 e)
  rw [heq]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact ghostCorrDistinctStep ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hb0
    hbR hb2R hbF lane Base z.2 j hj hbX hbY hc

end

-- from BankRepairDigitCohortWindow L3.CohortWindow.exportsBackRun
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

/-- Recorded exports only accumulate along the coupled chain. Consumer: `widthPinStateStep`, `widthIdStateStep`. -/
theorem widthExportsBackRun (word : List (Fin n)) :
    ∀ w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      ExportsBack w.1.2 (word.foldl (widthWindowNext ref root lane src R) w).1.2 := by
  induction word with
  | nil => intro w x hx _; exact hx
  | cons e rest ih =>
      intro w x hx ht
      have h1 := ih (widthWindowNext ref root lane src R w e) x hx
        (by show x.time ≤ w.1.2.clock + 1; omega)
      exact exportsBackStep ring (piD (ref.phys w.1.1)) w.1.2 e x h1 ht

end

-- from BankRepairDigitCohortClose L3.CohortClose.winInvDStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **Step of the strengthened window invariant**: every letter keeps `WidthWinInvD`; the arrival
counter stays, or advances by one with a closed window whose crossings carry the atoms. Consumer: `widthCohortCycleStageCharge`, `widthJustClosedStart`, `widthWindowSimCharge`. -/
theorem widthWinInvDStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WidthWinInvD ref root lane src R Base z g) (e : Fin n) :
    WidthWinInvD ref root lane src R Base (widthDigitAuditNext ref z e)
      (widthWindowGhost ref root lane src R z g e) ∧
    ((widthWindowGhost ref root lane src R z g e).2 = g.2 ∨
      ((widthWindowGhost ref root lane src R z g e).2 = g.2 + 1 ∧
        ∃ (lam : Nat → Nat) (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
          (t0 : Nat), gridDone R R lam ∧
          CycWin ring root lane src R (widthDigitAuditNext ref z e).2 lam
            chi t0 ∧
          ChiAtoms ring root lane src R Base (widthDigitAuditNext ref z e).2
            lam chi)) := by
  obtain ⟨hlay, hfo, hgd, ⟨o, hcyc⟩, chi, t0, hw, ha⟩ := h
  have hgd' := (widthGhostCorrDistinctStep ref hfix hn root lane src R hR hsrc hend Base z hlay
    hgd e).2
  obtain ⟨hlay', hproj⟩ := widthCohortStep ref hfix hn root lane src R hR hsrc hend z.1 hlay e
  have hfo' : AuditFrameOrder (widthDigitAuditNext ref z e).2 :=
    auditFrameOrderStep ring (piD (ref.phys z.1)) z.2 e hfo
  have hcs := cohortCycStep hcyc (cohortEdgeOf root src R e)
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD (ref.phys z.1)) z.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD (ref.phys z.1))) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2 hbX hbY
  have hop : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD (ref.phys z.1)) z.2 (digitSite ring root jx))).exported =
          some x →
        x.operand = (laneCells ring root lane src z.2.current (R - 1)).out.atom := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delOperand ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2 hbX hbY
  have hw' := cycWinStep ring root lane src R (piD (ref.phys z.1)) z.2 hfo (digitSite ring root jx)
    (cohortProj ring root lane src R (piD (ref.phys z.1)))
    (cohortEdgeOf root src R (digitSite ring root jx)) hedge hkeDel hdel hcyc chi t0 hw
  have ha' := chiAtomsStep ring root lane src R Base (piD (ref.phys z.1)) z.2 (digitSite ring root jx)
    (cohortEdgeOf root src R (digitSite ring root jx)) hedge hdel hop hgd.1 hcyc chi ha
  have hcyc' : ∃ o', CohortCycIn R (widthWindowGhost ref root lane src R z g
      (digitSite ring root jx)).2
      (cohortProj ring root lane src R
        (piD (ref.phys (widthDigitAuditNext ref z (digitSite ring root jx)).1)))
      (widthWindowGhost ref root lane src R z g (digitSite ring root jx)) o' := by
    show ∃ o', CohortCycIn R _ (cohortProj ring root lane src R
      (piD (ref.phys (ref.next z.1 (digitSite ring root jx))))) _ o'
    rw [hproj]
    rcases hcs with ⟨o', -, hin, -⟩ | hst
    · refine ⟨o', ?_⟩
      unfold widthWindowGhost
      rw [hin.1]
      exact hin
    · refine ⟨0, ?_⟩
      unfold widthWindowGhost
      rw [hst.1]
      exact hst
  unfold widthWindowGhost cohortCycleGhost at hcyc' ⊢
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys z.1)))
      g.1 (cohortEdgeOf root src R (digitSite ring root jx)))
  · rw [if_pos hd] at hcyc' ⊢
    exact ⟨⟨hlay', hfo', hgd', hcyc', chi, _,
      cycWinStart ring root lane src R _ hfo' chi, chiAtomsStart ring root lane src R Base _ chi⟩,
      Or.inr ⟨rfl, _, _, t0, hd, hw', ha'⟩⟩
  · rw [if_neg hd] at hcyc' ⊢
    exact ⟨⟨hlay', hfo', hgd', hcyc', _, t0, hw', ha'⟩, Or.inl rfl⟩

end

-- from BankRepairDigitCohortLedger L3.CohortLedger.ledgerOkBankStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.CohortLedger.ledgerOkBankStep`. Consumer: `widthValInvStep`. -/
theorem widthLedgerOkStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref root src R z.1)
    (hc : LedgerOk ring root lane src R z.2) (e : Fin n) :
    WidthCohortLayout ref root src R (widthDigitAuditNext ref z e).1 ∧
    LedgerOk ring root lane src R (widthDigitAuditNext ref z e).2 := by
  refine ⟨(widthCohortStep ref hfix hn root lane src R hR hsrc hend z.1 hz e).1, ?_⟩
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root z.1 hL e
  show LedgerOk ring root lane src R (digitAuditStep ring (piD (ref.phys z.1)) z.2 e)
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact ledgerOkStep ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hb0
    hbR hb2R hbF lane z.2 j hj hbX hbY hc

end

-- from BankRepairDigitCohortOrder L3.CohortOrder.OrderInv
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

/-- The order invariant with cycle start `t0`: layout, the cycle class in some old phase `o`,
and once the old cohort is gone (`o = 2R + 1`) a terminal receipt recorded since `t0`. Consumer: `widthOrderInvStep`, `WidthOldCompletionPair`, `WidthFiveInvPair`. -/
def WidthOrderInv (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (t0 : Nat) : Prop :=
  WidthCohortLayout ref root src R z.1 ∧ t0 ≤ z.2.clock ∧
  ∃ o, CohortCycIn R g.2 (cohortProj ring root lane src R (piD (ref.phys z.1))) g o ∧
    (o = 2 * R + 1 → TermSince ring root lane src R z.2 t0)

end

-- from BankRepairDigitCohortOrder L3.CohortOrder.orderInvStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- **Order step**: every letter keeps the order invariant. A non-closing letter keeps the cycle
start; a closing letter (arrival counter `j → j + 1`) starts the next cycle at the new clock, and
**before it a terminal receipt on the terminal edge was recorded after the cycle start**. Consumer: `widthFiveInvPairStep`. -/
theorem widthOrderInvStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (t0 : Nat) (h : WidthOrderInv ref root lane src R z g t0)
    (e : Fin n) :
    ((widthWindowGhost ref root lane src R z g e).2 = g.2 ∧
      WidthOrderInv ref root lane src R (widthDigitAuditNext ref z e)
        (widthWindowGhost ref root lane src R z g e) t0) ∨
    ((widthWindowGhost ref root lane src R z g e).2 = g.2 + 1 ∧
      WidthOrderInv ref root lane src R (widthDigitAuditNext ref z e)
        (widthWindowGhost ref root lane src R z g e) (z.2.clock + 1) ∧
      TermSince ring root lane src R z.2 t0) := by
  obtain ⟨hlay, ht0, o, ⟨hm, hg, hY, hnd⟩, hterm⟩ := h
  obtain ⟨hlay', hproj⟩ := widthCohortStep ref hfix hn root lane src R hR hsrc hend z.1 hlay e
  have hlay0 := hlay
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay0
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  obtain ⟨o', ho, hg', hY', hx⟩ := genStepClosedRef hg hY hnd
    (cohortEdgeOf root src R (digitSite ring root jx))
  have hclk : (widthDigitAuditNext ref z (digitSite ring root jx)).2.clock =
      z.2.clock + 1 := rfl
  have hnext : (widthDigitAuditNext ref z (digitSite ring root jx)).2 =
      digitAuditStep ring (piD (ref.phys z.1)) z.2 (digitSite ring root jx) := rfl
  have hprj : cohortProj ring root lane src R
      (piD (ref.phys (widthDigitAuditNext ref z (digitSite ring root jx)).1)) =
      cohortLaneStep R (cohortProj ring root lane src R (piD (ref.phys z.1)))
        (cohortEdgeOf root src R (digitSite ring root jx)) := hproj
  unfold widthWindowGhost cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys z.1)))
      g.1 (cohortEdgeOf root src R (digitSite ring root jx)))
  · rw [if_pos hd]
    right
    obtain ⟨a, b, d⟩ := cohortGenDoneStart hg' hY' hd
    have hoo : o' = 2 * R + 1 := by
      have hl := hd (R - 1) (by omega)
      exact (cohortGenArrived hg' (by omega)).1
    have hT : TermSince ring root lane src R z.2 t0 := by
      rcases hx with hx | hx | ⟨-, hx⟩
      · omega
      · exact hterm hx
      · exact absurd hx (closingHop hR hnd _ hd)
    refine ⟨rfl, ⟨hlay', by rw [hclk]; omega, 0, ?_, fun h0 => by omega⟩, hT⟩
    rw [hprj]
    exact ⟨rfl, a, b, d⟩
  · rw [if_neg hd]
    left
    refine ⟨rfl, hlay', by rw [hclk]; omega, o', ?_, fun h2 => ?_⟩
    · rw [hprj]
      exact ⟨hm, hg', hY', hd⟩
    · rw [hnext]
      rcases hx with hx | hx | ⟨hx1, hx2⟩
      · omega
      · exact termSinceStep ring root lane src R _ _ _ _ (hterm hx)
      · have hje : jx = src + (2 * R - 1) := edgeOfSome ring root src R jx _ hj hx2
        subst hje
        have hold := hg.1
        rw [hx1, cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega)]
          at hold
        have hlive := hold.1
        rw [show R + (2 * R - R) - 1 = 2 * R - 1 by omega,
          projLive ring root lane src R (piD (ref.phys z.1)) (2 * R - 1) (by omega) (by omega)]
          at hlive
        exact termNow ring root (piD (ref.phys z.1)) R src hR hend hroot hb2R lane z.2 hbY hlive t0
          ht0

end

-- from BankRepairDigitBlockStart L3.BlockStart.cycleOldChain
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- The old-cohort stages of cycle `j`: phase `0` to phase `o` at `2n` per phase. Consumer: `widthCycleEntryCharge`, `widthCycleCutCharge`. -/
theorem widthCycleOldChain (j o : Nat) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycOld R j 0 (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycOld R j o (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (o * (2 * n)) :=
  bankRepairDigitChargedChain (widthCohortCycleNext ref root lane src R)
    (fun o w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R j o (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2) (2 * n)
    (fun o => widthCohortCycLaneStage ref hfix hn root lane src R hR hsrc hend
      (CohortCycOld R j o) (CohortCycOld R j (o + 1)) (cohortGenEdgeAt R o)
      (cohortGenEdgeAtLt hR o) (cohortCycOldStage j o).1 (cohortCycOldStage j o).2) o

end

-- from BankRepairDigitBlockStart L3.BlockStart.cycleEntryCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- **Entrance**: from any state of the cycle class in cycle `j`, the first closing letter (the
start of cycle `j + 1`) costs `≤ 39 n R` doubled. Consumer: `widthBlockModelCharge`. -/
theorem widthCycleEntryCharge (j : Nat) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 o)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (39 * n * R) := by
  have hold := widthCycleOldChain ref hfix hn root lane src R hR hsrc hend j (2 * R + 1)
  have hmat := bankRepairDigitChargedChain (widthCohortCycleNext ref root lane src R)
    (fun a w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycMat R j a (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2) (2 * n)
    (fun a => widthCohortCycLaneStage ref hfix hn root lane src R hR hsrc hend
      (CohortCycMat R j a) (CohortCycMat R j (a + 1)) (R - 1 - a) (by omega)
      (cohortCycMatStage j a).1 (cohortCycMatStage j a).2) R
  have h1 := bankRepairDigitChargedWeaken (widthCohortCycleNext ref root lane src R)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R j 0 (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 o)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R j (2 * R + 1) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycMat R j 0 (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    _ (fun _ hw => ⟨hw.1, Or.inl (by
        obtain ⟨o, ho⟩ := hw.2
        exact ⟨o, Or.inl (Nat.zero_le o), ho⟩)⟩)
    (fun _ hw => ⟨hw.1, cohortCycOldToMat hw.2⟩) hold
  have h2 := bankRepairDigitZeroCompose _ _ _ _ _ _ h1 hmat
  have h3 := bankRepairDigitZeroCompose _ _ _ _ _ _ h2
    (widthCohortCycTransportCharge ref hfix hn root lane src R hR hsrc hend j)
  have e1 : (2 * R + 1) * (2 * n) = 2 * (R * (2 * n)) + 2 * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : R * (2 * n) = 2 * (n * R) := by rw [Nat.mul_comm R, Nat.mul_assoc]
  have e3 : 32 * n * R = 32 * (n * R) := Nat.mul_assoc _ _ _
  have e4 : 39 * n * R = 39 * (n * R) := Nat.mul_assoc _ _ _
  have hnR : n * 2 ≤ n * R := Nat.mul_le_mul_left n hR
  have hle : (2 * R + 1) * (2 * n) + R * (2 * n) + 32 * n * R ≤ 39 * n * R := by
    rw [e1, e2, e3, e4]
    omega
  intro x hx T
  exact Nat.le_trans (h3 x hx T) (Nat.mul_le_mul_left _ hle)

end

-- from BankRepairDigitBlockStart L3.BlockStart.cycleCutCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- **The cut inside a block**: from the start of cycle `j`, the old cohort of cycle `j + K` is
gone (its terminal has fired) at cost `≤ K · 39 n R + (2R + 1) · 2n` doubled. Consumer: `widthBlockModelCharge`. -/
theorem widthCycleCutCharge (j K : Nat) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycStart R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycOld R (j + K) (2 * R + 1) (cohortProj ring root lane src R (piD (ref.phys w.1)))
          w.2)
      (K * (39 * n * R) + (2 * R + 1) * (2 * n)) := by
  have hcyc := bankRepairDigitChargedChain (widthCohortCycleNext ref root lane src R)
    (fun i w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycStart R (j + i) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (39 * n * R)
    (fun i => widthCohortCycleStageCharge ref hfix hn root lane src R hR hsrc hend (j + i)) K
  have hold := bankRepairDigitChargedWeaken (widthCohortCycleNext ref root lane src R)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycOld R (j + K) 0 (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    (fun w => WidthCohortLayout ref root src R w.1 ∧
      CohortCycStart R (j + K) (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
    _ _ _ (fun _ hw => ⟨hw.1, Or.inl ⟨0, Or.inl (Nat.le_refl 0), hw.2⟩⟩) (fun _ hw => hw)
    (widthCycleOldChain ref hfix hn root lane src R hR hsrc hend (j + K) (2 * R + 1))
  exact bankRepairDigitZeroCompose _ _ _ _ _ _ hcyc hold

end

-- from BankRepairDigitBlockStart L3.BlockStart.blockModelCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
include hfix

include hn hR hsrc hend in
/-- **The block on the model chain**: from any state of the cycle class in cycle `j`, through
the first closing letter (entrance), four full cycles, and the old phase of the fifth cycle
after the entrance (the fifth old cohort's terminal), at cost `≤ 200 n R` doubled. Consumer: `widthBlockCharge`. -/
theorem widthBlockModelCharge (j : Nat) :
    BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2 o)
      (fun w => WidthCohortLayout ref root src R w.1 ∧
        CohortCycOld R (j + 1 + 4) (2 * R + 1)
          (cohortProj ring root lane src R (piD (ref.phys w.1))) w.2)
      (200 * n * R) :=
  bankRepairDigitChargedMono _ _ _ (blockBudget hR)
    (bankRepairDigitZeroCompose _ _ _ _ _ _
      (widthCycleEntryCharge ref hfix hn root lane src R hR hsrc hend j)
      (widthCycleCutCharge ref hfix hn root lane src R hR hsrc hend (j + 1) 4))

end

-- from BankRepairDigitBlockStart L3.BlockStart.JustClosed
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The block entrance**: the coupled state (reference state × audit × cycle ghost) just after a closing
letter, i.e. the image under a letter that advanced the arrival counter of a state carrying the
strengthened window invariant. Consumer: `widthJustClosedStart`, `widthJustClosedLam`, `widthRunInvStart`. -/
def WidthJustClosed
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  ∃ (w0 : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n),
    WidthWinInvD ref root lane src R Base w0.1 w0.2 ∧
    w = widthWindowNext ref root lane src R w0 e ∧ w.2.2 = w0.2.2 + 1

end

-- from BankRepairDigitBlockStart L3.BlockStart.justClosedStart
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- At the block entrance: the strengthened window invariant holds and the lane is at the start
of the cycle numbered by the arrival counter (the closed cohort is the old cohort, in phase `0`). Consumer: `widthRunInvStart`, `widthUseFactReach`, `widthCompletionOfPair`. -/
theorem widthJustClosedStart
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : WidthJustClosed ref root lane src R Base w) :
    WidthWinInvD ref root lane src R Base w.1 w.2 ∧
    CohortCycStart R w.2.2 (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2 := by
  obtain ⟨w0, e, hw0, rfl, hcl⟩ := h
  refine ⟨(widthWinInvDStep ref hfix hn root lane src R hR hsrc hend Base w0.1 w0.2 hw0 e).1, ?_⟩
  obtain ⟨hlay, -, -, ⟨o, hcyc⟩, -⟩ := hw0
  have hproj := (widthCohortStep ref hfix hn root lane src R hR hsrc hend w0.1.1 hlay e).2
  rcases cohortCycStep hcyc (cohortEdgeOf root src R e) with ⟨o', -, hin, -⟩ | hst
  · have h1 := hin.1
    have h2 : (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w0.1.1))) w0.2
        (cohortEdgeOf root src R e)).2 = w0.2.2 + 1 := hcl
    omega
  · have h2 : (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w0.1.1))) w0.2
        (cohortEdgeOf root src R e)).2 = w0.2.2 + 1 := hcl
    show CohortCycStart R (cohortCycleGhost R (cohortProj ring root lane src R
        (piD (ref.phys w0.1.1))) w0.2 (cohortEdgeOf root src R e)).2
      (cohortProj ring root lane src R (piD (ref.phys (ref.next w0.1.1 e))))
      (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w0.1.1))) w0.2
        (cohortEdgeOf root src R e))
    rw [hproj, h2]
    exact hst

end

-- from BankRepairDigitBlockStart L3.BlockStart.windowSimCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **Generic window transfer**: on the coupled chain `widthWindowNext`, a real target `Good` and an
invariant `Inv` carried by every letter off `Good` (on `WidthWinInvD`), with every model state of `B`
forcing `Good`: the first hit of `Good` costs at most the model charge of any stage `A → B` of
`widthCohortCycleNext`. Consumer: `widthBlockCharge`. -/
theorem widthWindowSimCharge
    (Inv Good : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (A B : ref.State × ((Nat → Nat) × Nat) → Prop) (c : Nat)
    (hinv : ∀ w e, WidthWinInvD ref root lane src R Base w.1 w.2 → Inv w → ¬ Good w →
      Inv (widthWindowNext ref root lane src R w e))
    (hgood : ∀ w, WidthWinInvD ref root lane src R Base w.1 w.2 → Inv w → B (w.1.1, w.2) →
      Good w)
    (hc : BankRepairDigitChargedStage (widthCohortCycleNext ref root lane src R) A B c)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2) (hi : Inv w) (ha : A (w.1.1, w.2))
    (T : Nat) :
    2 * costNumerator (widthWindowNext ref root lane src R) Good w T ≤ n ^ T * c := by
  have hsim := costNumeratorSimLe (widthWindowNext ref root lane src R)
    (widthCohortCycleNext ref root lane src R)
    (fun w y => y = (w.1.1, w.2) ∧ WidthWinInvD ref root lane src R Base w.1 w.2 ∧ Inv w)
    Good B
    (fun w y e h hg => by
      obtain ⟨rfl, hw, hi⟩ := h
      exact ⟨rfl, (widthWinInvDStep ref hfix hn root lane src R hR hsrc hend Base w.1 w.2 hw e).1,
        hinv w e hw hi hg⟩)
    (fun w y h hb => by
      obtain ⟨rfl, hw, hi⟩ := h
      exact hgood w hw hi hb)
    T w (w.1.1, w.2) ⟨rfl, hw, hi⟩
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hsim) (hc _ ha T)

end

-- from BankRepairDigitBlockStart L3.BlockStart.blockCharge
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **The block on the coupled chain**: from any state with the strengthened window invariant and
an invariant `Inv` carried by every letter off `Good`, if every state at which the old cohort of
the fifth cycle after the entrance is gone satisfies `Good`, the first hit of `Good` costs
`≤ 200 n R` doubled: entrance `39 n R`, four cycles `4 · 39 n R`, the fifth old phase
`(2R + 1) · 2n ≤ 5 n R`. Consumer: `widthWindowCoupledBlock`. -/
theorem widthBlockCharge
    (Inv Good : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hinv : ∀ w e, WidthWinInvD ref root lane src R Base w.1 w.2 → Inv w → ¬ Good w →
      Inv (widthWindowNext ref root lane src R w e))
    (j : Nat)
    (hgood : ∀ w, WidthWinInvD ref root lane src R Base w.1 w.2 → Inv w →
      (WidthCohortLayout ref root src R w.1.1 ∧
        CohortCycOld R (j + 1 + 4) (2 * R + 1)
          (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2) → Good w)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2) (hi : Inv w) (hj : w.2.2 = j)
    (T : Nat) :
    2 * costNumerator (widthWindowNext ref root lane src R) Good w T ≤ n ^ T * (200 * n * R) := by
  obtain ⟨o, hcyc⟩ := hw.2.2.2.1
  exact widthWindowSimCharge ref hfix hn root lane src R hR hsrc hend Base Inv Good
    (fun v => WidthCohortLayout ref root src R v.1 ∧
      ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys v.1))) v.2 o)
    (fun v => WidthCohortLayout ref root src R v.1 ∧
      CohortCycOld R (j + 1 + 4) (2 * R + 1) (cohortProj ring root lane src R (piD (ref.phys v.1)))
        v.2)
    (200 * n * R) hinv hgood (widthBlockModelCharge ref hfix hn root lane src R hR hsrc hend j) w hw
    hi ⟨hw.1, o, by rw [← hj]; exact hcyc⟩ T

end

-- from BankRepairDigitProjection L3.Projection.CoupledBlock
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  

/-- A block stage `P → Q` of the R10c clock, charged on some coupled chain projecting to
`bankRepairNext`. Consumer: `widthChargedOfCoupledBlock`, `widthWindowCoupledBlock`, `widthCoupledBlockSigma`. -/
def WidthCoupledBlock (P Q : ref.State → Prop) (c : Nat) : Prop :=
  ∃ (X : Type) (next' : X → Fin n → X) (π : X → ref.State)
    (A B : X → Prop),
    (∀ x e, π (next' x e) = ref.next (π x) e) ∧
    (∀ z, P z → ∃ x, π x = z ∧ A x) ∧ (∀ x, B x → Q (π x)) ∧
    BankRepairDigitChargedStage next' A B c

end

-- from BankRepairDigitProjection L3.Projection.chargedOfCoupledBlock
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  

/-- Generic port of `L3.Projection.chargedOfCoupledBlock`. Consumer: `widthCleanWaveAfterEntry`. -/
theorem widthChargedOfCoupledBlock (P Q : ref.State → Prop) (c : Nat)
    (h : WidthCoupledBlock ref P Q c) :
    BankRepairDigitChargedStage (ref.next) P Q c := by
  obtain ⟨X, next', π, A, B, hπ, hA, hB, hc⟩ := h
  exact chargedProject _ next' π hπ A B P Q c hA hB hc

end

-- from BankRepairDigitProjection L3.Projection.winInvDReset
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The arrival counter of the cycle ghost is free: it can be reset at a block start. Consumer: `widthCleanEntryBlockStage`. -/
theorem widthWinInvDReset
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WidthWinInvD ref root lane src R Base z g) (j : Nat) :
    WidthWinInvD ref root lane src R Base z (g.1, j) := by
  obtain ⟨h1, h2, h3, ⟨o, -, hg, hy, hd⟩, h5⟩ := h
  exact ⟨h1, h2, h3, ⟨o, rfl, hg, hy, hd⟩, h5⟩

end

-- from BankRepairDigitProjection L3.Projection.windowCoupledBlock
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **Item 1's block as the consumed per-block clock**: if every physical block-start state lifts
to a coupled state with the strengthened window invariant, the invariant `Inv` and arrival
counter `0`; `Inv` is carried off `Good`; the old cohort of cycle `5` being gone forces `Good`;
and `Good` projects into the block finish: the block stage costs `≤ 200 n R` doubled on
`bankRepairNext`. Consumer: `widthRunPairBlock`. -/
theorem widthWindowCoupledBlock
    (P Q : ref.State → Prop)
    (Inv Good : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hinv : ∀ w e, WidthWinInvD ref root lane src R Base w.1 w.2 → Inv w → ¬ Good w →
      Inv (widthWindowNext ref root lane src R w e))
    (hgood : ∀ w, WidthWinInvD ref root lane src R Base w.1 w.2 → Inv w →
      (WidthCohortLayout ref root src R w.1.1 ∧
        CohortCycOld R 5 (2 * R + 1) (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2) →
      Good w)
    (hA : ∀ z, P z → ∃ w : (ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ (WidthWinInvD ref root lane src R Base w.1 w.2 ∧ Inv w ∧ w.2.2 = 0))
    (hB : ∀ w, Good w → Q w.1.1) :
    WidthCoupledBlock ref P Q (200 * n * R) :=
  ⟨_, widthWindowNext ref root lane src R, fun w => w.1.1,
    fun w => WidthWinInvD ref root lane src R Base w.1 w.2 ∧ Inv w ∧ w.2.2 = 0, Good,
    fun _ _ => rfl, hA, hB,
    fun w hw T => widthBlockCharge ref hfix hn root lane src R hR hsrc hend Base Inv Good hinv 0
      hgood w hw.1 hw.2.1 hw.2.2 T⟩

end

-- from BankRepairDigitHClose L3.HClose.auditFold
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Audit facts preserved by every letter persist along the coupled chain. Consumer: `widthFramesExactFold`, `widthReceiptOfPins`, `widthCompletionOfPair`. -/
theorem widthAuditFold (P : DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop)
    (hP : ∀ S A e, P A → P (digitAuditStep ring S A e)) :
    ∀ (word : List (Fin n))
      (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
        ((Nat → Nat) × Nat)),
      P w.1.2 → P (word.foldl (widthWindowNext ref root lane src R) w).1.2
  | [], _, h => h
  | e :: word, w, h =>
      widthAuditFold P hP word (widthWindowNext ref root lane src R w e)
        (hP (piD (ref.phys w.1.1)) w.1.2 e h)

end

-- from BankRepairDigitHClose L3.HClose.ChiPrev
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The previous window at a just-closed state `wc`: its crossings are recorded on the delimiter
edge into the target block start, with increasing times, and no other export lies between the
first and the last crossing along any continuation (T28 `windowClosingD`, plus destinations). Consumer: `widthFramesExactFold`, `widthChiPrevOfCore`, `WidthCloseReceipt`. -/
def WidthChiPrev (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∀ i, i < R → DigitRecordedExport wc.1.2 (chi i) ∧ OnEdge ring root lane src R (chi i) ∧
    (chi i).destination = digitSite ring root (src + R)) ∧
  (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
  ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedExport (word.foldl (widthWindowNext ref root lane src R) wc).1.2 x →
    OnEdge ring root lane src R x → (chi 0).time ≤ x.time → x.time ≤ (chi (R - 1)).time →
    ∃ i, i < R ∧ x = chi i

end

-- from BankRepairDigitCloseReceipt L3.CloseReceipt.framesExactFold
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Exact frames along the coupled chain. Consumer: `widthReceiptOfCore`. -/
theorem widthFramesExactFold (word : List (Fin n))
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (h : FramesExact ring w.1.2) :
    FramesExact ring (word.foldl (widthWindowNext ref root lane src R) w).1.2 :=
  widthAuditFold ref root lane src R (FramesExact ring)
    (fun S A e hA => framesExactStep ring S A e hA) word w h

end

-- from BankRepairDigitCloseReceipt L3.CloseReceipt.chiPrevOfCore
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

include hR in
/-- **Item 1**: under exact frames the core window clauses give `WidthChiPrev` (destinations). Consumer: `widthReceiptOfCore`. -/
theorem widthChiPrevOfCore
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hfe : FramesExact ring wc.1.2) (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthChiCore ref root lane src R wc chi) :
    WidthChiPrev ref root lane src R wc chi := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i hi => ⟨(h1 i hi).1, (h1 i hi).2, ?_⟩, h2, h3⟩
  exact onEdgeDest ring root lane src R (by omega) wc.1.2 hfe (chi i) (h1 i hi).1 (h1 i hi).2

end

-- from BankRepairDigitCloseReceipt L3.CloseReceipt.CloseReceipt
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The hclose receipt of one terminal `U` in the cycle started at `wc`. Consumer: `widthReceiptOfCore`, `widthReceiptOfPins`, `widthCompletionOfPair`. -/
def WidthCloseReceipt
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
    WidthChiPrev ref root lane src R wc chi ∧ ChiSampled ring root lane src R wc.1.2 chi ∧
    CloseUses ring root src R wc.1.2.clock U chi

end

-- from BankRepairDigitCloseReceipt L3.CloseReceipt.receiptOfCore
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **Item 1 inside the receipt**: under exact frames, the receipt needs the core window, the
sample exactness, and `CloseUses` without its destination clause. Consumer: `widthReceiptOfPins`. -/
theorem widthReceiptOfCore (hR1 : 2 ≤ R)
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hfe : FramesExact ring wc.1.2)
    (hU : DigitRecordedTerminal (word.foldl (widthWindowNext ref root lane src R) wc).1.2 U)
    (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hcore : WidthChiCore ref root lane src R wc chi)
    (hsamp : ChiSampled ring root lane src R wc.1.2 chi)
    (huse : ∃ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
      U.ledger = some L ∧ L.inherited = none ∧ L.uses.length = R ∧
      UsesOk ring root src R U.time L.uses ∧
      ∀ j (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[j]? = some u →
        u.operand = (chi (R - 1 - j)).operand ∧ u.value = (chi (R - 1 - j)).value ∧
        u.tail = (chi (R - 1 - j)).tail ∧ wc.1.2.clock < u.time) :
    WidthCloseReceipt ref root lane src R wc U :=
  ⟨chi, widthChiPrevOfCore ref root lane src R hR1 wc hfe chi hcore, hsamp,
    closeDest ring root src R (by omega) _
      (widthFramesExactFold ref root lane src R word wc hfe) U hU hUs, huse⟩

end

-- from BankRepairDigitValueLedger L3.ValueLedger.valInvBankStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.ValueLedger.valInvBankStep`. Consumer: `widthLedgerOkStep`. -/
theorem widthValInvStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref root src R z.1)
    (hc : WidthValInv ref root lane src R z) (e : Fin n) :
    WidthValInv ref root lane src R (widthDigitAuditNext ref z e) := by
  have hlo := (widthLedgerOkStep ref hfix hn root lane src R hR hsrc hend z hz hc.2.2.2 e).2
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root z.1 hL e
  obtain ⟨hv, hx, hu, -⟩ := hc
  show ValCorr ring root lane src R (piD (ref.phys (ref.next z.1 e)))
      (digitAuditStep ring (piD (ref.phys z.1)) z.2 e) ∧
    ExportVal ring root lane src R (digitAuditStep ring (piD (ref.phys z.1)) z.2 e) ∧
    UseVal ring root lane src R (digitAuditStep ring (piD (ref.phys z.1)) z.2 e) ∧
    LedgerOk ring root lane src R (digitAuditStep ring (piD (ref.phys z.1)) z.2 e)
  rw [heq]
  refine ⟨?_, exportValStep ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2 e
    hbX hbY hv hx, ?_, hlo⟩
  · obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact valCorrStep ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF lane z.2 j hj hbX hbY hv
  · obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact useValStep ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hbR hbF
      lane z.2 j hj hbX hbY hv hu

end

-- from BankRepairDigitValueLedger L3.ValueLedger.valReachStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Every `widthWindowNext` letter from a state with the window invariant keeps the value reach. Consumer: `widthPinReachStep`. -/
theorem widthValReachStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (h : WidthValReach ref root lane src R w) :
    WidthValReach ref root lane src R (widthWindowNext ref root lane src R w e) :=
  ⟨framesExactStep ring (piD (ref.phys w.1.1)) w.1.2 e h.1,
    widthValInvStep ref hfix hn root lane src R hR hsrc hend w.1 hw.1 h.2 e⟩

end

-- from BankRepairDigitValueLedger L3.ValueLedger.receiptOfPins
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hR in
/-- **The receipt from the operand facts**: at a cycle start `wc` with exact frames, ordered
frames and the delimiter-time clause of the distinct correspondence, a core window `chi` with the
site pin, and a terminal `U` recorded later with the value invariant there and the operand
tracking, `U` has its receipt. Consumer: `widthOldCompletionPairReach`. -/
theorem widthReceiptOfPins
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hfe : FramesExact ring wc.1.2) (hfo : AuditFrameOrder wc.1.2)
    (hxv0 : ExportVal ring root lane src R wc.1.2)
    (htime : ∀ (x : DigitExport (compileAdvice (ceilLogTwo n)) n) (id : DigitStamp n),
      DigitRecordedExport wc.1.2 x → OnEdge ring root lane src R x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ wc.1.2.clock)
    (hval : WidthValInv ref root lane src R
      (word.foldl (widthWindowNext ref root lane src R) wc).1)
    (hU : DigitRecordedTerminal (word.foldl (widthWindowNext ref root lane src R) wc).1.2 U)
    (hUl : U.lane = lane) (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hcore : WidthChiCore ref root lane src R wc chi)
    (hpin : SitePin ring root lane src R wc.1.2 chi)
    (hop : UseTrack R wc.1.2.clock U chi) :
    WidthCloseReceipt ref root lane src R wc U := by
  have hfoF : AuditFrameOrder (word.foldl (widthWindowNext ref root lane src R) wc).1.2 :=
    widthAuditFold ref root lane src R AuditFrameOrder
      (fun S A e hA => auditFrameOrderStep ring S A e hA) word wc hfo
  have hsamp := chiSampledOf ring root lane src R hR wc.1.2 hfo hxv0 htime chi
    (fun i hi => (hcore.1 i hi)) hpin
  have hchiF : ∀ i, i < R →
      DigitRecordedExport (word.foldl (widthWindowNext ref root lane src R) wc).1.2 (chi i) ∧
      OnEdge ring root lane src R (chi i) ∧ ∃ id, (chi i).operand = some (.sampled id) := by
    intro i hi
    obtain ⟨s, hs, -⟩ := hpin i hi
    exact ⟨widthAuditFold ref root lane src R (fun A => DigitRecordedExport A (chi i))
      (fun S A e hA => recordedExportStep ring S A e _ hA) word wc (hcore.1 i hi).1,
      (hcore.1 i hi).2, s.id, hs⟩
  obtain ⟨-, hxvF, huvF, hloF⟩ := hval
  exact widthReceiptOfCore ref root lane src R hR wc word U hfe hU hUs chi hcore hsamp
    (closeUsesOf ring root lane src R hR _ hfoF hxvF huvF hloF chi hchiF wc.1.2.clock U hU hUl
      hUs hop)

end

-- from BankRepairDigitSitePin L3.SitePin.windowPinFacts
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **One coupled letter**: the pinned classes of the younger cells, of the chosen slots and of
the crossings, and the window, all move to the generated ghost `cohortGenStep` of the letter. Consumer: `widthPinStateStep`, `widthIdStateStep`. -/
theorem widthWindowPinFacts
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2) (e : Fin n) :
    (YoungInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 →
      YoungInv R (SPin ring root lane src (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e))
        (tracked ring root lane src R (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e))
        (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e))) ∧
    (ChosenInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 →
      ChosenInv R (SPin ring root lane src (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e))
        (tracked ring root lane src R (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e))
        (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e))) ∧
    (∀ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
      CycWin ring root lane src R w.1.2 w.2.1 chi t0 →
      CycWin ring root lane src R (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e)
        (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e))
        (chiNext ring root lane src R (piD (ref.phys w.1.1)) w.1.2 e w.2.1 chi) t0) ∧
    (∀ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChosenInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 →
      ChiInv R (SPin ring root lane src w.1.2) chi w.2.1 →
      ChiInv R (SPin ring root lane src (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e))
        (chiNext ring root lane src R (piD (ref.phys w.1.1)) w.1.2 e w.2.1 chi)
        (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e))) := by
  obtain ⟨hlay, hfo, hgd, ⟨o, hcyc⟩, -⟩ := hw
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root w.1.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD (ref.phys w.1.1)) w.1.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD (ref.phys w.1.1)) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  have hop : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD (ref.phys w.1.1)) w.1.2
          (digitSite ring root jx))).exported = some x →
        x.operand = (laneCells ring root lane src w.1.2.current (R - 1)).out.atom := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delOperand ring root (piD (ref.phys w.1.1)) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  have hch := hcyc.2.1.2
  have hY := hcyc.2.2.1
  obtain ⟨hYs, hCs⟩ := letterPin ring (by omega) root (piD (ref.phys w.1.1)) R src hR hsrc hend hroot
    hb0 hbR hb2R hbF lane Base w.1.2 jx hj hbX hbY hgd hch hY
  refine ⟨hYs, hCs, fun chi t0 hcw => ?_, fun chi hC hci => ?_⟩
  · exact cycWinStep ring root lane src R (piD (ref.phys w.1.1)) w.1.2 hfo (digitSite ring root jx)
      (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      (cohortEdgeOf root src R (digitSite ring root jx)) hedge hkeDel hdel hcyc chi t0 hcw
  · exact chiInvStep ring root lane src R Base (piD (ref.phys w.1.1)) w.1.2 (digitSite ring root jx)
      (cohortEdgeOf root src R (digitSite ring root jx)) hedge hdel hop hgd.1 hch
      (sPinStep ring root lane src (piD (ref.phys w.1.1)) w.1.2 (digitSite ring root jx)) hC chi hci

end

-- from BankRepairDigitSitePin L3.SitePin.chiCoreStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Generic port of `L3.SitePin.chiCoreStep`. Consumer: `widthPinStateStep`. -/
theorem widthChiCoreStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthChiCore ref root lane src R w chi) :
    WidthChiCore ref root lane src R (widthWindowNext ref root lane src R w e) chi := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun i hi => ⟨recordedExportStep ring (piD (ref.phys w.1.1)) w.1.2 e _ (h1 i hi).1,
    (h1 i hi).2⟩, h2, fun word x hx ho ha hb => h3 (e :: word) x hx ho ha hb⟩

end

-- from BankRepairDigitSitePin L3.SitePin.pinStateStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **`WidthPinState` is carried by every letter**; a closing letter records the closed window with
its site pin as the last closed window. Consumer: `widthWindowPinFacts`, `widthPinReachStep`. -/
theorem widthPinStateStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (h : WidthPinState ref root lane src R w) (e : Fin n) :
    WidthPinState ref root lane src R (widthWindowNext ref root lane src R w e) := by
  obtain ⟨hYs, hCs, hWs, hXs⟩ :=
    widthWindowPinFacts ref hfix hn root lane src R hR hsrc hend Base w hw e
  have hfo' : AuditFrameOrder (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) :=
    auditFrameOrderStep ring (piD (ref.phys w.1.1)) w.1.2 e hw.2.1
  obtain ⟨hC, hYi, chi, t0, hcw, hci, hlast⟩ := h
  have hw' := hWs chi t0 hcw
  have hci' := hXs chi hC hci
  have hY' := hYs hYi
  have hC' := hCs hC
  have hA : (widthWindowNext ref root lane src R w e).1.2 =
      digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e := rfl
  have hg : (widthWindowNext ref root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2
        (cohortEdgeOf root src R e) := rfl
  unfold WidthPinState WidthYInv WidthLastClose
  rw [hA, hg]
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    dsimp only
    have hall : ∀ i, i < R → R ≤ cohortPos R (cohortGenStep R
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1 (cohortEdgeOf root src R e)) i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    refine ⟨chosenRestart hR hY' hd, youngRestart, chi, _,
      cycWinStart ring root lane src R _ hfo' chi, ?_, fun _ =>
        ⟨chiNext ring root lane src R (piD (ref.phys w.1.1)) w.1.2 e w.2.1 chi, ?_, ?_, ?_⟩⟩
    · intro i hi hc
      have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
      omega
    · refine ⟨fun i hi => ⟨(hw'.2.2.1 i hi (hall i hi)).1, (hw'.2.2.1 i hi (hall i hi)).2.1⟩,
        fun a b hab hb => hw'.2.2.2 a b hab hb (hall b hb), fun word x hx ho h1 h2 => ?_⟩
      exact noExtraExport ring root lane src R hR _ _ hfo'
        (widthExportsBackRun ref root lane src R word _) _ _ t0 hw' hd x hx ho h1 h2
    · intro i hi
      obtain ⟨a, ha, s, h1, h2, h3, h4, h5⟩ := hci' i hi (hall i hi)
      exact ⟨s, by rw [ha, h1], h2, h3, h4, h5⟩
    · intro x hx ho _
      by_cases hxt : t0 < x.time
      · obtain ⟨i, hi, -, rfl⟩ := hw'.2.1 x hx ho hxt
        rcases Nat.lt_or_ge i (R - 1) with hlt | hge
        · exact Nat.le_of_lt (hw'.2.2.2 i (R - 1) hlt (by omega) (hall _ (by omega)))
        · have hiR : i = R - 1 := by omega
          subst hiR
          exact Nat.le_refl _
      · have := (hw'.2.2.1 (R - 1) (by omega) (hall _ (by omega))).2.2
        omega
  · rw [if_neg hd]
    dsimp only
    refine ⟨hC', hY', _, t0, hw', hci', fun h1 => ?_⟩
    obtain ⟨chiOld, hcore, hpin, hlat⟩ := hlast h1
    refine ⟨chiOld, widthChiCoreStep ref root lane src R w e chiOld hcore,
      sitePinStep ring root lane src R _ _ _ chiOld hpin, fun x hx ho ht => ?_⟩
    rcases recordedExportStepCases ring (piD (ref.phys w.1.1)) w.1.2 _ x hx with hx' | ⟨hxt, -, -⟩
    · exact hlat x hx' ho ht
    · have := hcw.1
      omega

end

-- from BankRepairDigitSitePin L3.SitePin.pinReachStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.SitePin.pinReachStep`. Consumer: `widthPinReachRun`. -/
theorem widthPinReachStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (h : WidthPinReach ref root lane src R w) :
    WidthPinReach ref root lane src R (widthWindowNext ref root lane src R w e) :=
  ⟨widthValReachStep ref hfix hn root lane src R hR hsrc hend Base w e hw h.1,
    widthPinStateStep ref hfix hn root lane src R hR hsrc hend Base w hw h.2 e⟩

end

-- from BankRepairDigitSitePin L3.SitePin.pinReachRun
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.SitePin.pinReachRun`. Consumer: `widthPinReachStep`. -/
theorem widthPinReachRun (word : List (Fin n)) :
    ∀ w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WidthWinInvD ref root lane src R Base w.1 w.2 → WidthPinReach ref root lane src R w →
      WidthPinReach ref root lane src R (word.foldl (widthWindowNext ref root lane src R) w) := by
  induction word with
  | nil => intro w _ h; exact h
  | cons e rest ih =>
      intro w hw h
      exact ih _ (widthWinInvDStep ref hfix hn root lane src R hR hsrc hend Base w.1 w.2 hw e).1
        (widthPinReachStep ref hfix hn root lane src R hR hsrc hend Base w e hw h)

end

-- from BankRepairDigitSitePin L3.SitePin.justClosedLam
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- A just-closed state is a cycle start after at least one arrival. Consumer: `widthUseFactReach`. -/
theorem widthJustClosedLam
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : WidthJustClosed ref root lane src R Base wc) :
    wc.2.1 = (fun _ => 0) ∧ 1 ≤ wc.2.2 := by
  obtain ⟨w0, e, -, rfl, hcl⟩ := h
  refine ⟨?_, by omega⟩
  have hcl' : (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w0.1.1))) w0.2
      (cohortEdgeOf root src R e)).2 = w0.2.2 + 1 := hcl
  show (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w0.1.1))) w0.2
      (cohortEdgeOf root src R e)).1 = fun _ => 0
  unfold cohortCycleGhost at hcl' ⊢
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w0.1.1)))
      w0.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
  · rw [if_neg hd] at hcl'
    dsimp only at hcl'
    omega

end

-- from BankRepairDigitUseTrack L3.UseTrack.letterRows
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **The target facts of one coupled letter**: the cycle class before, the chosen class after,
the correspondence before and after, the input and ledger rows (`MoveH`, `CarryH`), the
crossing map, the delimiter export, and the terminal receipt. Consumer: `widthIdStateStep`, `widthRunInvStep`. -/
theorem widthLetterRows
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2) (e : Fin n) :
    ∃ (o c' : Nat) (stamp : DigitStamp n) (gxo : DigitOutGhost n)
      (Ok Ok' : Bool → DigitAtom n → Prop),
      CohortCycIn R w.2.2 (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2 o ∧
      CohortChosen R (cohortLaneStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
          (cohortEdgeOf root src R e))
        (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e)) c' ∧
      (∀ q, R ≤ q → q < 2 * R →
        InCorr Ok ((cohortProj ring root lane src R (piD (ref.phys w.1.1))).inp q)
          (inA ring root lane src w.1.2 q) ∧
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))).live q =
          (caA ring root lane src w.1.2 q).isSome) ∧
      (∀ q, R ≤ q → q < 2 * R →
        InCorr Ok' ((cohortLaneStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
          (cohortEdgeOf root src R e)).inp q)
          (inA ring root lane src (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) q)) ∧
      MoveH R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) (cohortEdgeOf root src R e)
        (inA ring root lane src w.1.2)
        (inA ring root lane src (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e)) stamp gxo ∧
      CarryH R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) (cohortEdgeOf root src R e)
        (inA ring root lane src w.1.2) (caA ring root lane src w.1.2)
        (caA ring root lane src (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e))
        (w.1.2.clock + 1) ∧
      (∀ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (i : Nat),
        chiNext ring root lane src R (piD (ref.phys w.1.1)) w.1.2 e w.2.1 chi i =
          if cohortPos R w.2.1 i = R - 1 ∧ cohortEdgeOf root src R e = some (R - 1) then
            ((digitReceiptLane lane (svcAt ring (piD (ref.phys w.1.1)) w.1.2 e)).exported).getD
              (chi i)
          else chi i) ∧
      (cohortEdgeOf root src R e = some (R - 1) → ∀ T,
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))).out (R - 1) = .D T →
        cohortTok R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) R = .empty →
        ∃ x, (digitReceiptLane lane (svcAt ring (piD (ref.phys w.1.1)) w.1.2 e)).exported = some x ∧
          x.operand = gxo.atom) ∧
      (∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD (ref.phys w.1.1)) w.1.2 e)).terminal = some U →
        cohortEdgeOf root src R e = some (2 * R - 1) →
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))).live (2 * R - 1) = true ∧
          U.ledger = caA ring root lane src w.1.2 (2 * R - 1)) := by
  obtain ⟨hlay, -, hgd, ⟨o, hcyc⟩, -⟩ := hw
  have hgd' := (widthGhostCorrDistinctStep ref hfix hn root lane src R hR hsrc hend Base w.1 hlay
    hgd e).2
  have hproj := (widthCohortStep ref hfix hn root lane src R hR hsrc hend w.1.1 hlay e).2
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root w.1.1 hL e
  obtain ⟨o', -, hgen', -, -⟩ :=
    cohortGenStepClosed hcyc.2.1 hcyc.2.2.1 hcyc.2.2.2 (cohortEdgeOf root src R e)
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD (ref.phys w.1.1)) R src hR hsrc hend hroot hbR hb2R
    hbF lane w.1.2 jx hj hbX hbY
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD (ref.phys w.1.1)) w.1.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD (ref.phys w.1.1)) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  have hop : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD (ref.phys w.1.1)) w.1.2
          (digitSite ring root jx))).exported = some x →
        x.operand = (laneCells ring root lane src w.1.2.current (R - 1)).out.atom := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delOperand ring root (piD (ref.phys w.1.1)) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  refine ⟨o, cohortBottom R o', DigitStamp.mk (w.1.2.clock + 1) (digitSite ring root jx) lane,
    (laneCells ring root lane src w.1.2.current (R - 1)).out, GhostOk ring root lane src R Base w.1.2,
    GhostOk ring root lane src R Base
      (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 (digitSite ring root jx)),
    hcyc, hgen'.2, fun q h1 h2 => hgd.1.2 q h1 h2, fun q h1 h2 => ?_,
    ⟨fun q h1 h2 h3 h4 => congrArg DigitLaneGhost.input (hrows.1 q h1 h2 h3 h4),
      fun hk => (hrows.2.1 hk).1, fun k hk h1 h2 => (hrows.2.2.1 k hk h1 h2).1,
      fun hk => (hrows.2.2.2 hk).1⟩,
    ⟨fun q h1 h2 h3 h4 => congrArg DigitLaneGhost.carry (hrows.1 q h1 h2 h3 h4),
      fun hk => (hrows.2.1 hk).2, fun k hk h1 h2 => (hrows.2.2.1 k hk h1 h2).2,
      fun hk => (hrows.2.2.2 hk).2.1⟩, fun chi i => ?_, ?_, fun U hU hk => ?_⟩
  · have hc := (hgd'.1.2 q h1 h2).1
    change InCorr _ ((cohortProj ring root lane src R
      (piD (ref.phys (ref.next w.1.1 (digitSite ring root jx))))).inp q)
      ((laneCells ring root lane src
        (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 (digitSite ring root jx)).current q).input)
      at hc
    rw [hproj] at hc
    exact hc
  · unfold chiNext
    by_cases hc : cohortPos R w.2.1 i = R - 1 ∧
        digitSite ring root jx = digitSite ring root (src + (R - 1))
    · rw [if_pos hc, if_pos ⟨hc.1, hkeDel hc.2⟩]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, hedge h.2⟩)]
  · intro hk T hD hemp
    have he := hedge hk
    rw [cohortTokTgt _ (Nat.le_refl R)] at hemp
    obtain ⟨hE, hLv⟩ := inEmptyOf hemp
    obtain ⟨x, hx, -, -, -⟩ := (hdel he).2 T hD hE hLv
    exact ⟨x, hx, hop he x hx⟩
  · exact (hrows.2.2.2 hk).2.2 U hU

end

-- from BankRepairDigitUseTrack L3.UseTrack.idStateStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **`WidthIdState` is carried by every letter**; a closing letter turns the crossed slots' identity
into the old cells' identity for the window it closes. Consumer: `widthUseReachStep`. -/
theorem widthIdStateStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (hp : WidthPinState ref root lane src R w)
    (h : WidthIdState ref root lane src R w) (e : Fin n) :
    WidthIdState ref root lane src R (widthWindowNext ref root lane src R w e) := by
  obtain ⟨-, -, hWs, hXs⟩ :=
    widthWindowPinFacts ref hfix hn root lane src R hR hsrc hend Base w hw e
  have hfo' : AuditFrameOrder (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) :=
    auditFrameOrderStep ring (piD (ref.phys w.1.1)) w.1.2 e hw.2.1
  obtain ⟨o, c', stamp, gxo, Ok, Ok', hcyc, hch', hcorr, hcorr', hm, -, hchi, hxe, -⟩ :=
    widthLetterRows ref hfix hn root lane src R hR hsrc hend Base w hw e
  obtain ⟨chi, t0, hcw, hci, hcur, hlast⟩ := h
  have hw' := hWs chi t0 hcw
  have hci' := hXs chi hp.1 hci
  have hcur' := curIdStep hcyc hch' (fun q h1 h2 => (hcorr q h1 h2).1) hcorr' hm chi _ _
    (hchi chi) hxe hcur
  have hA : (widthWindowNext ref root lane src R w e).1.2 =
      digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e := rfl
  have hg : (widthWindowNext ref root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2
        (cohortEdgeOf root src R e) := rfl
  unfold WidthIdState WidthLastClose
  rw [hA, hg]
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    dsimp only
    have hall : ∀ i, i < R → R ≤ cohortPos R (cohortGenStep R
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1 (cohortEdgeOf root src R e)) i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    refine ⟨chi, _, cycWinStart ring root lane src R _ hfo' chi, ?_, ?_, fun _ =>
        ⟨chiNext ring root lane src R (piD (ref.phys w.1.1)) w.1.2 e w.2.1 chi, ⟨?_, ?_, ?_⟩,
          oldOfCur hch' hd _ hcur'⟩⟩
    · intro i hi hc
      have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
      omega
    · intro i hi hc
      have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
      omega
    · refine ⟨fun i hi => ⟨(hw'.2.2.1 i hi (hall i hi)).1, (hw'.2.2.1 i hi (hall i hi)).2.1⟩,
        fun a b hab hb => hw'.2.2.2 a b hab hb (hall b hb), fun word x hx ho h1 h2 => ?_⟩
      exact noExtraExport ring root lane src R hR _ _ hfo'
        (widthExportsBackRun ref root lane src R word _) _ _ t0 hw' hd x hx ho h1 h2
    · intro i hi
      obtain ⟨a, ha, s, h1, h2, h3, h4, h5⟩ := hci' i hi (hall i hi)
      exact ⟨s, by rw [ha, h1], h2, h3, h4, h5⟩
    · intro x hx ho _
      by_cases hxt : t0 < x.time
      · obtain ⟨i, hi, -, rfl⟩ := hw'.2.1 x hx ho hxt
        rcases Nat.lt_or_ge i (R - 1) with hlt | hge
        · exact Nat.le_of_lt (hw'.2.2.2 i (R - 1) hlt (by omega) (hall _ (by omega)))
        · have hiR : i = R - 1 := by omega
          subst hiR
          exact Nat.le_refl _
      · have := (hw'.2.2.1 (R - 1) (by omega) (hall _ (by omega))).2.2
        omega
  · rw [if_neg hd]
    dsimp only
    refine ⟨_, t0, hw', hci', hcur', fun h1 => ?_⟩
    obtain ⟨chiOld, ⟨hcore, hpin, hlat⟩, hold⟩ := hlast h1
    refine ⟨chiOld, ⟨widthChiCoreStep ref root lane src R w e chiOld hcore,
      sitePinStep ring root lane src R _ _ _ chiOld hpin, fun x hx ho ht => ?_⟩,
      oldIdStep hcyc hm chiOld hold⟩
    rcases recordedExportStepCases ring (piD (ref.phys w.1.1)) w.1.2 _ x hx with hx' | ⟨hxt, -, -⟩
    · exact hlat x hx' ho ht
    · have := hcw.1
      omega

end

-- from BankRepairDigitUseTrack L3.UseTrack.useReachStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.UseTrack.useReachStep`. Consumer: `widthRunPairBlock`. -/
theorem widthUseReachStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (h : WidthUseReach ref root lane src R w) :
    WidthUseReach ref root lane src R (widthWindowNext ref root lane src R w e) :=
  ⟨widthPinReachStep ref hfix hn root lane src R hR hsrc hend Base w e hw h.1,
    widthIdStateStep ref hfix hn root lane src R hR hsrc hend Base w hw h.1.2 h.2 e⟩

end

-- from BankRepairDigitUseTrack L3.UseTrack.RunInv
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The run invariant** from a block entrance stamped `t0` with closed window `chiOld`: the old
target cells' identity, clean ledgers reading the old operands after `t0`, and every terminal on
the terminal edge recorded after `t0` with the operand tracking. Consumer: `widthRunInvStep`, `widthRunInvRun`, `widthRunInvStart`. -/
def WidthRunInv (t0 : Nat) (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  t0 ≤ w.1.2.clock ∧ OldIdA R w.2.1 (inA ring root lane src w.1.2) chiOld ∧
  LedgerA R t0 chiOld (caA ring root lane src w.1.2) ∧
  ∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n, DigitRecordedTerminal w.1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) → t0 < U.time →
    UseTrack R t0 U chiOld

end

-- from BankRepairDigitUseTrack L3.UseTrack.countStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Generic port of `L3.UseTrack.countStep`. Consumer: `widthCountRun`. -/
theorem widthCountStep
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n) :
    (widthWindowNext ref root lane src R w e).2.2 = w.2.2 ∨
      (widthWindowNext ref root lane src R w e).2.2 = w.2.2 + 1 := by
  show (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2
    (cohortEdgeOf root src R e)).2 = w.2.2 ∨
    (cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2
    (cohortEdgeOf root src R e)).2 = w.2.2 + 1
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    exact Or.inr rfl
  · rw [if_neg hd]
    exact Or.inl rfl

end

-- from BankRepairDigitUseTrack L3.UseTrack.countRun
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Generic port of `L3.UseTrack.countRun`. Consumer: `widthCountStep`. -/
theorem widthCountRun (word : List (Fin n)) :
    ∀ w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      w.2.2 ≤ (word.foldl (widthWindowNext ref root lane src R) w).2.2 := by
  induction word with
  | nil => intro w; exact Nat.le_refl _
  | cons e rest ih =>
      intro w
      have h1 := ih (widthWindowNext ref root lane src R w e)
      rcases widthCountStep ref root lane src R w e with h2 | h2
      · show w.2.2 ≤ (rest.foldl (widthWindowNext ref root lane src R)
          (widthWindowNext ref root lane src R w e)).2.2
        omega
      · show w.2.2 ≤ (rest.foldl (widthWindowNext ref root lane src R)
          (widthWindowNext ref root lane src R w e)).2.2
        omega

end

-- from BankRepairDigitUseTrack L3.UseTrack.runInvStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **One non-closing letter keeps the run invariant**: launch, consumption and terminal. Consumer: `widthRunInvRun`. -/
theorem widthRunInvStep (t0 : Nat) (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (hc : (widthWindowNext ref root lane src R w e).2.2 = w.2.2)
    (h : WidthRunInv ref root lane src R t0 chiOld w) :
    WidthRunInv ref root lane src R t0 chiOld (widthWindowNext ref root lane src R w e) := by
  obtain ⟨o, c', stamp, gxo, Ok, Ok', hcyc, -, hcorr, -, hm, hcar, -, -, hterm⟩ :=
    widthLetterRows ref hfix hn root lane src R hR hsrc hend Base w hw e
  obtain ⟨ht0, hold, hled, htm⟩ := h
  have hA : (widthWindowNext ref root lane src R w e).1.2 =
      digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e := rfl
  have hg : (widthWindowNext ref root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2
        (cohortEdgeOf root src R e) := rfl
  have hnd : ¬ gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e)) := by
    intro hd
    rw [hg] at hc
    unfold cohortCycleGhost at hc
    rw [if_pos hd] at hc
    dsimp only at hc
    omega
  have hlam : (widthWindowNext ref root lane src R w e).2.1 =
      cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
        (cohortEdgeOf root src R e) := by
    rw [hg]
    unfold cohortCycleGhost
    rw [if_neg hnd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA]
    show t0 ≤ w.1.2.clock + 1
    omega
  · rw [hlam, hA]
    exact oldIdStep hcyc hm chiOld hold
  · rw [hA]
    exact ledgerStep hcyc (fun q h1 h2 => (hcorr q h1 h2).1) (fun q h1 h2 => (hcorr q h1 h2).2)
      chiOld hold hcar (by omega) hled
  · rw [hA]
    intro U hU hUl hUs hUt
    rcases recordedTerminalStepCases ring (piD (ref.phys w.1.1)) w.1.2 e U hU with hU' |
        ⟨-, hUe, hUr⟩
    · exact htm U hU' hUl hUs hUt
    · have he : e = digitSite ring root (src + (2 * R - 1)) := by rw [← hUe, hUs]
      have hk : cohortEdgeOf root src R e = some (2 * R - 1) := by
        rw [he]
        exact cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
      rw [hUl] at hUr
      obtain ⟨hlv, hled'⟩ := hterm U hUr hk
      obtain ⟨L, hL⟩ : ∃ L, caA ring root lane src w.1.2 (2 * R - 1) = some L := by
        have h3 := (hcorr (2 * R - 1) (by omega) (by omega)).2
        rw [hlv] at h3
        cases h0 : caA ring root lane src w.1.2 (2 * R - 1) with
        | none => rw [h0] at h3; cases h3
        | some L => exact ⟨L, rfl⟩
      obtain ⟨hi0, -, hops⟩ := hled (2 * R - 1) (by omega) (by omega) L hL
      exact ⟨L, by rw [hled', hL], hi0, fun j u hj => hops j u hj⟩

end

-- from BankRepairDigitUseTrack L3.UseTrack.runInvRun
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- Generic port of `L3.UseTrack.runInvRun`. Consumer: `widthUseFactReach`. -/
theorem widthRunInvRun (t0 : Nat) (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) :
    ∀ w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WidthWinInvD ref root lane src R Base w.1 w.2 →
      (word.foldl (widthWindowNext ref root lane src R) w).2.2 = w.2.2 →
      WidthRunInv ref root lane src R t0 chiOld w →
      WidthRunInv ref root lane src R t0 chiOld
        (word.foldl (widthWindowNext ref root lane src R) w) := by
  induction word with
  | nil => intro w _ _ h; exact h
  | cons e rest ih =>
      intro w hw hc h
      have hc' : (rest.foldl (widthWindowNext ref root lane src R)
          (widthWindowNext ref root lane src R w e)).2.2 = w.2.2 := hc
      have h1 := widthCountRun ref root lane src R rest (widthWindowNext ref root lane src R w e)
      have h2 := widthCountStep ref root lane src R w e
      have hce : (widthWindowNext ref root lane src R w e).2.2 = w.2.2 := by omega
      exact ih _ (widthWinInvDStep ref hfix hn root lane src R hR hsrc hend Base w.1 w.2 hw e).1
        (by rw [hce]; exact hc')
        (widthRunInvStep ref hfix hn root lane src R hR hsrc hend Base t0 chiOld w e hw hce h)

end

-- from BankRepairDigitUseTrack L3.UseTrack.runInvStart
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- At a block entrance the run invariant starts with the entrance clock: no target cell is live
and no terminal is recorded after the clock. Consumer: `widthUseFactReach`. -/
theorem widthRunInvStart
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hjc : WidthJustClosed ref root lane src R Base wc)
    (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hold : OldIdA R wc.2.1 (inA ring root lane src wc.1.2) chiOld) :
    WidthRunInv ref root lane src R wc.1.2.clock chiOld wc := by
  obtain ⟨hwd, hst⟩ := widthJustClosedStart ref hfix hn root lane src R hR hsrc hend Base wc hjc
  refine ⟨Nat.le_refl _, hold, fun q h1 h2 L hL => ?_, fun U hU _ _ hUt => ?_⟩
  · exfalso
    have h3 := (hwd.2.2.1.1.2 q h1 h2).2
    rw [noLiveStart hst q h1 h2] at h3
    have h4 : caA ring root lane src wc.1.2 q = some L := hL
    unfold caA at h4
    rw [h4] at h3
    cases h3
  · exfalso
    obtain ⟨f, hf, ht, -⟩ := hU
    have := (hwd.2.1.2.1 f hf).2
    omega

end

-- from BankRepairDigitUseTrack L3.UseTrack.useFactReach
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **Item 4 (operand tracking) at every reachable block entrance**: the window closed there
satisfies T32's core clauses, site pin and latest-window clause, and every later terminal of the
old cohort on the terminal edge has a clean ledger whose `j`-th use, made after the entrance,
reads the operand of `chi (R - 1 - j)`. Consumer: `widthRunInvStep`, `widthOldCompletionPairReach`. -/
theorem widthUseFactReach
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (hre : WidthUseReach ref root lane src R wc)
    (hjc : WidthJustClosed ref root lane src R Base wc)
    (hcnt : (word.foldl (widthWindowNext ref root lane src R) wc).2.2 = wc.2.2) :
    ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      WidthChiCore ref root lane src R wc chi ∧ SitePin ring root lane src R wc.1.2 chi ∧
      (∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x →
        OnEdge ring root lane src R x → x.time ≤ (chi (R - 1)).time) ∧
      ∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
        DigitRecordedTerminal (word.foldl (widthWindowNext ref root lane src R) wc).1.2 U →
        U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
        wc.1.2.clock < U.time → UseTrack R wc.1.2.clock U chi := by
  obtain ⟨hwd, -⟩ := widthJustClosedStart ref hfix hn root lane src R hR hsrc hend Base wc hjc
  obtain ⟨hlam, h1⟩ := widthJustClosedLam ref root lane src R Base wc hjc
  obtain ⟨-, chi', t0, hcw, -, -, hlast⟩ := hre
  obtain ⟨chi, ⟨hcore, hpin, hlat⟩, hold⟩ := hlast h1
  have hrun := widthRunInvRun ref hfix hn root lane src R hR hsrc hend Base wc.1.2.clock chi word
    wc hwd hcnt (widthRunInvStart ref hfix hn root lane src R hR hsrc hend Base wc hjc chi hold)
  refine ⟨chi, hcore, hpin, fun x hx ho => hlat x hx ho ?_, fun U hU hUl hUs hUt =>
    hrun.2.2.2 U hU hUl hUs hUt⟩
  rcases Nat.lt_or_ge t0 x.time with hlt | hge
  · exfalso
    obtain ⟨i, hi, hc, -⟩ := hcw.2.1 x hx ho hlt
    rw [hlam] at hc
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · exact hge

end

-- from BankRepairDigitBlockCuts L3.BlockCuts.coupledBlockSigma
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  

/-- **Union of coupled blocks**: if every start state lies in some piece `Pi i` and every piece
is a coupled block into `Q` of charge `c`, so is the whole stage (the coupled chain is the
disjoint union of the pieces' chains). Consumer: `BankRepairDigitValueWaveClose` (the block
geometry, leader and anchor time depend on the run). -/
theorem widthCoupledBlockSigma {ι : Type} (P Q : ref.State → Prop) (c : Nat)
    (Pi : ι → ref.State → Prop) (hcov : ∀ z, P z → ∃ i, Pi i z)
    (h : ∀ i, WidthCoupledBlock ref (Pi i) Q c) : WidthCoupledBlock ref P Q c := by
  have s0 : ∀ i, ∃ (X : Type) (next' : X → Fin n → X) (π : X → ref.State)
      (A B : X → Prop),
      (∀ x e, π (next' x e) = ref.next (π x) e) ∧
      (∀ z, Pi i z → ∃ x, π x = z ∧ A x) ∧ (∀ x, B x → Q (π x)) ∧
      BankRepairDigitChargedStage next' A B c := h
  let X : ι → Type := fun i => Classical.choose (s0 i)
  have s1 := fun i => Classical.choose_spec (s0 i)
  let nx : (i : ι) → X i → Fin n → X i := fun i => Classical.choose (s1 i)
  have s2 := fun i => Classical.choose_spec (s1 i)
  let π : (i : ι) → X i → ref.State := fun i => Classical.choose (s2 i)
  have s3 := fun i => Classical.choose_spec (s2 i)
  let A : (i : ι) → X i → Prop := fun i => Classical.choose (s3 i)
  have s4 := fun i => Classical.choose_spec (s3 i)
  let B : (i : ι) → X i → Prop := fun i => Classical.choose (s4 i)
  have s5 := fun i => Classical.choose_spec (s4 i)
  have hπ : ∀ i x e, π i (nx i x e) = ref.next (π i x) e := fun i => (s5 i).1
  have hA : ∀ i z, Pi i z → ∃ x, π i x = z ∧ A i x := fun i => (s5 i).2.1
  have hB : ∀ i x, B i x → Q (π i x) := fun i => (s5 i).2.2.1
  have hc : ∀ i, BankRepairDigitChargedStage (nx i) (A i) (B i) c := fun i => (s5 i).2.2.2
  refine ⟨(i : ι) × X i, fun x e => ⟨x.1, nx x.1 x.2 e⟩, fun x => π x.1 x.2,
    fun x => A x.1 x.2, fun x => B x.1 x.2, fun x e => hπ x.1 x.2 e, fun z hz => ?_,
    fun x hx => hB x.1 x.2 hx, fun x hx T => ?_⟩
  · obtain ⟨i, hi⟩ := hcov z hz
    obtain ⟨x, hx, hax⟩ := hA i z hi
    exact ⟨⟨i, x⟩, hx, hax⟩
  · have hle := costProjectLe
      (fun (y : (i : ι) × X i) e => (⟨y.1, nx y.1 y.2 e⟩ : (i : ι) × X i))
      (nx x.1) (fun y => (⟨x.1, y⟩ : (i : ι) × X i)) (fun _ _ => rfl)
      (fun y => B y.1 y.2) (B x.1) (fun _ h => h) x.2 T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hle) (hc x.1 x.2 hx T)

end

-- from BankRepairDigitBlockCuts L3.BlockCuts.coupledBlockOfImp
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  

/-- **A trivial block**: an inclusion `P ⊆ Q` is a coupled block of every charge (the first hit
costs nothing). Consumer: `BankRepairDigitValueWaveClose` (blocks past the last complete pair). -/
theorem widthCoupledBlockOfImp (P Q : ref.State → Prop) (c : Nat)
    (h : ∀ z, P z → Q z) : WidthCoupledBlock ref P Q c := by
  refine ⟨ref.State, ref.next, fun z => z, P, Q,
    fun _ _ => rfl, fun z hz => ⟨z, rfl, hz⟩, fun x hx => hx, fun x hx T => ?_⟩
  rw [costNumerator_terminal _ _ _ (h x hx) T, Nat.mul_zero]
  exact Nat.zero_le _

end

-- from BankRepairDigitBlockCuts L3.BlockCuts.pinStateReset
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The arrival counter of a `WidthPinState` can be relabelled `0`. Consumer: `startOfClose`,
`widthUseReachReset`. -/
theorem widthPinStateReset
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WidthPinState ref root lane src R (x, g)) :
    WidthPinState ref root lane src R (x, (g.1, 0)) := by
  obtain ⟨hC, hY, chi, t0, hcw, hci, -⟩ := h
  exact ⟨hC, hY, chi, t0, hcw, hci, fun h1 => absurd h1 (Nat.not_succ_le_zero 0)⟩

end

-- from BankRepairDigitBlockCuts L3.BlockCuts.useReachReset
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The arrival counter of a `WidthUseReach` state can be relabelled `0`. Consumer:
`BankRepairDigitValueWaveClose` (the entrance lift may come with any cycle numbering). -/
theorem widthUseReachReset
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WidthUseReach ref root lane src R (x, g)) :
    WidthUseReach ref root lane src R (x, (g.1, 0)) := by
  obtain ⟨⟨hv, hp⟩, chi, t0, hcw, hci, hcur, -⟩ := h
  exact ⟨⟨hv, widthPinStateReset ref root lane src R x g hp⟩, chi, t0, hcw, hci, hcur,
    fun h1 => absurd h1 (Nat.not_succ_le_zero 0)⟩

end

-- from BankRepairDigitPairBlock L3.PairBlock.completionOfPair
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **`completionOfReceipt` from the complete pair** (no anchor): the receipt of a terminal
recorded after a just-closed cycle start makes it a `DigitCompletion`. Consumer:
`widthOldCompletionPairReach`. -/
theorem widthCompletionOfPair
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hjc : WidthJustClosed ref root lane src R Base wc)
    (hpair : PairIn ring root src R wc.1.2)
    (hU : DigitRecordedTerminal (word.foldl (widthWindowNext ref root lane src R) wc).1.2 U)
    (hUl : U.lane = lane) (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (hr : WidthCloseReceipt ref root lane src R wc U) :
    DigitCompletion ring (word.foldl (widthWindowNext ref root lane src R) wc).1.2 root src
      (src + R) lane 0 U := by
  obtain ⟨chi, ⟨hrec, hinc, hextra⟩, ⟨samp, hsamp⟩, hUd, L, hL, hLi, hLl, hLu, huse⟩ := hr
  have hspan : digitSpan (compileAdvice (ceilLogTwo n)) = R := by
    have := hpair.2.1
    omega
  have hstart : (word.foldl (widthWindowNext ref root lane src R) wc).1.2.start =
      wc.1.2.start :=
    widthAuditFold ref root lane src R (fun A => A.start = wc.1.2.start)
      (fun S A e hA => hA) word wc rfl
  have hfo0 : AuditFrameOrder wc.1.2 :=
    (widthJustClosedStart ref hfix hn root lane src R hR hsrc hend Base wc hjc).1.2.1
  have hfo : AuditFrameOrder (word.foldl (widthWindowNext ref root lane src R) wc).1.2 :=
    widthAuditFold ref root lane src R AuditFrameOrder
      (fun S A e hA => auditFrameOrderStep ring S A e hA) word wc hfo0
  have hclk : U.time ≤ (word.foldl (widthWindowNext ref root lane src R) wc).1.2.clock := by
    obtain ⟨f, hf, hft, -⟩ := hU
    rw [← hft]
    exact (hfo.2.1 f hf).2
  have hrecF : ∀ i, i < R →
      DigitRecordedExport (word.foldl (widthWindowNext ref root lane src R) wc).1.2 (chi i) :=
    fun i hi => widthAuditFold ref root lane src R (fun A => DigitRecordedExport A (chi i))
      (fun S A e hA => recordedExportStep ring S A e _ hA) word wc (hrec i hi).1
  have hsampF : ∀ i, i < R →
      DigitRecordedSample (word.foldl (widthWindowNext ref root lane src R) wc).1.2 (samp i) :=
    fun i hi => widthAuditFold ref root lane src R (fun A => DigitRecordedSample A (samp i))
      (fun S A e hA => recordedSampleStep ring S A e _ hA) word wc (hsamp i hi).1
  have hchiT : ∀ i, i < R → (chi i).time ≤ wc.1.2.clock :=
    fun i hi => recordedTimeLe wc.1.2 hfo0 (chi i) (hrec i hi).1
  refine ⟨by rw [hstart]; exact hpair, hU, hUl, ?_, ?_, hclk, by omega, L,
    fun j => samp (R - 1 - j.val), fun j => chi (R - 1 - j.val),
    fun j => L.uses[j.val]'(by have := j.isLt; omega), hL, hLi, by omega, ?_, ?_, ?_⟩
  · rw [hUs]
    exact congrArg (digitSite ring root) (by omega)
  · rw [hUd]
    exact congrArg (digitSite ring root) (by omega)
  · intro j
    have hj := j.isLt
    have hjR : j.val < R := by omega
    have hi : R - 1 - j.val < R := by omega
    have hback : R - 1 - (R - 1 - j.val) = j.val := by omega
    obtain ⟨-, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsamp (R - 1 - j.val) hi
    rw [hback] at s4 s9
    obtain ⟨-, ⟨x1, x2⟩, x3⟩ := hrec (R - 1 - j.val) hi
    have hget : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨u1, u2, u3, u4⟩ := huse j.val _ hget
    obtain ⟨v1, v2, -⟩ := hLu j.val _ hget
    have hct := hchiT (R - 1 - j.val) hi
    refine ⟨hsampF _ hi, s3, s4, s5, s9, hrecF _ hi, x1,
      x2.trans (congrArg (digitSite ring root) (by omega)), x3, s2, s7, s8, hget, v1,
      u1.trans s2, u2.trans s7, u3.trans s8, s6, Nat.lt_of_le_of_lt hct u4, v2⟩
  · intro i j hij
    have hj := j.isLt
    have hgi : L.uses[i.val]? = some (L.uses[i.val]'(by have := i.isLt; omega)) :=
      List.getElem?_eq_getElem (by have := i.isLt; omega)
    have hgj : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    exact ⟨hinc (R - 1 - j.val) (R - 1 - i.val) (by omega) (by omega),
      (hLu j.val _ hgj).2.2 i.val _ hij hgi⟩
  · intro other ho o1 o2 o3 o4 o5
    have e0 : R - 1 - (digitSpan (compileAdvice (ceilLogTwo n)) - 1) = 0 := by omega
    have e1 : R - 1 - 0 = R - 1 := by omega
    have o4' : (chi 0).time ≤ other.time := by
      have h4 := o4
      dsimp only at h4
      rw [e0] at h4
      exact h4
    have o5' : other.time ≤ (chi (R - 1)).time := by
      have h5 := o5
      dsimp only at h5
      rw [e1] at h5
      exact h5
    obtain ⟨i, hi, rfl⟩ := hextra word other ho
      ⟨o1, o2.trans (congrArg (digitSite ring root) (by omega))⟩ o4' o5'
    refine ⟨⟨R - 1 - i, by omega⟩, ?_⟩
    show chi i = chi (R - 1 - (R - 1 - i))
    rw [show R - 1 - (R - 1 - i) = i by omega]

end

-- from BankRepairDigitPairBlock L3.PairBlock.OldCompletionPair
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **`OldCompletionOn` with the complete pair in place of the anchor** (and no `after`). Consumer: `widthOldCompletionPairReach`, `widthFiveInvPairStep`, `widthFiveGoodPair`. -/
def WidthOldCompletionPair
    (Reach : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) : Prop :=
  ∀ (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    Reach wc → WidthJustClosed ref root lane src R Base wc →
    PairIn ring root src R wc.1.2 →
    (word.foldl (widthWindowNext ref root lane src R) wc).2.2 = wc.2.2 →
    WidthOrderInv ref root lane src R (word.foldl (widthWindowNext ref root lane src R) wc).1
      (word.foldl (widthWindowNext ref root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (widthWindowNext ref root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    DigitCompletion ring (word.foldl (widthWindowNext ref root lane src R) wc).1.2 root src
      (src + R) lane 0 U

end

-- from BankRepairDigitPairBlock L3.PairBlock.oldCompletionPairReach
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **The completion obligation on `WidthUseReach` states from the complete pair, with no other
premise** (T33's `hCloseOnPinReach` + `oldCompletionOn`, whose receipt never read the anchor).
Consumer: `widthRunPairBlock`. -/
theorem widthOldCompletionPairReach :
    WidthOldCompletionPair ref root lane src R Base (WidthUseReach ref root lane src R) := by
  intro wc word U hre hjc hp hcnt _ hU hUl hUs hUt
  obtain ⟨hwd, -⟩ := widthJustClosedStart ref hfix hn root lane src R hR hsrc hend Base wc hjc
  obtain ⟨chi, hcore, hpin, -, huse⟩ :=
    widthUseFactReach ref hfix hn root lane src R hR hsrc hend Base wc word hre hjc hcnt
  have hreF := widthPinReachRun ref hfix hn root lane src R hR hsrc hend Base word wc hwd hre.1
  exact widthCompletionOfPair ref hfix hn root lane src R hR hsrc hend Base wc word U hjc hp hU hUl
    hUs (widthReceiptOfPins ref root lane src R hR wc word U hre.1.1.1 hwd.2.1 hre.1.1.2.2.1
      hwd.2.2.1.2.2.2.1 hreF.1.2 hU hUl hUs chi hcore hpin (huse U hU hUl hUs hUt))

end

-- from BankRepairDigitPairBlock L3.PairBlock.FiveInvPair
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The five-cohort invariant with the complete pair**: `FiveInvOn` with `PairIn` (now and at
the cycle start) in place of the anchor. Consumer: `widthFiveInvPairStep`, `widthFiveGoodPair`, `widthRunPairBlock`. -/
def WidthFiveInvPair
    (Reach : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  Reach w ∧ PairIn ring root src R w.1.2 ∧
  ((w.2.2 = 0 ∧ after ≤ w.1.2.clock) ∨
  (1 ≤ w.2.2 ∧ ∃ (wc : (ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) (word : List (Fin n)),
    Reach wc ∧ WidthJustClosed ref root lane src R Base wc ∧
    w = word.foldl (widthWindowNext ref root lane src R) wc ∧ wc.2.2 = w.2.2 ∧
    WidthOrderInv ref root lane src R w.1 w.2 wc.1.2.clock ∧ after ≤ wc.1.2.clock ∧
    PairIn ring root src R wc.1.2 ∧
    FwdIn ring root src (src + R) lane w.1.2 (w.2.2 - 1) after wc.1.2.clock))

end

-- from BankRepairDigitPairBlock L3.PairBlock.fiveInvPairStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- `WidthFiveInvPair` is carried by every letter (`FiveReach.fiveInvOnStep` with the pair).
Consumer: `widthRunPairBlock`. -/
theorem widthFiveInvPairStep
    (Reach : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (hReach : ∀ w e, WidthWinInvD ref root lane src R Base w.1 w.2 → Reach w →
      Reach (widthWindowNext ref root lane src R w e))
    (hcomp : WidthOldCompletionPair ref root lane src R Base Reach)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (hi : WidthFiveInvPair ref root lane src R Base Reach after w) :
    WidthFiveInvPair ref root lane src R Base Reach after
      (widthWindowNext ref root lane src R w e) := by
  obtain ⟨hre, hp, hi⟩ := hi
  have hre' := hReach w e hw hre
  have hclk : (widthWindowNext ref root lane src R w e).1.2.clock = w.1.2.clock + 1 := rfl
  have hp' : PairIn ring root src R (widthWindowNext ref root lane src R w e).1.2 := hp
  refine ⟨hre', hp', ?_⟩
  rcases hi with ⟨h0, ha⟩ | ⟨h1, wc, word, hrc, hjc, hweq, hcnt, hord, haft, hpc, hfwd⟩
  · rcases (widthWinInvDStep ref hfix hn root lane src R hR hsrc hend Base w.1 w.2 hw e).2 with
      hs | ⟨hs, -⟩
    · left
      refine ⟨?_, by rw [hclk]; omega⟩
      show (widthWindowGhost ref root lane src R w.1 w.2 e).2 = 0
      rw [hs, h0]
    · right
      have hjc' : WidthJustClosed ref root lane src R Base
          (widthWindowNext ref root lane src R w e) := ⟨w, e, hw, rfl, hs⟩
      obtain ⟨hwd, hst⟩ := widthJustClosedStart ref hfix hn root lane src R hR hsrc hend Base _ hjc'
      refine ⟨?_, widthWindowNext ref root lane src R w e, [], hre', hjc', rfl, rfl,
        ⟨hwd.1, Nat.le_refl _, 0, hst, fun h => by omega⟩, by rw [hclk]; omega, hp', ?_⟩
      · show 1 ≤ (widthWindowGhost ref root lane src R w.1 w.2 e).2
        rw [hs]
        omega
      · show FwdIn ring root src (src + R) lane _
          ((widthWindowGhost ref root lane src R w.1 w.2 e).2 - 1) after _
        rw [hs, h0]
        exact trivial
  · rcases widthOrderInvStep ref hfix hn root lane src R hR hsrc hend w.1 w.2 wc.1.2.clock hord e
      with ⟨hs, hord'⟩ | ⟨hs, hord', hterm⟩
    · right
      refine ⟨?_, wc, word ++ [e], hrc, hjc, ?_, ?_, hord', haft, hpc, ?_⟩
      · show 1 ≤ (widthWindowGhost ref root lane src R w.1 w.2 e).2
        rw [hs]
        exact h1
      · rw [List.foldl_append, ← hweq]
        rfl
      · show wc.2.2 = (widthWindowGhost ref root lane src R w.1 w.2 e).2
        rw [hs, hcnt]
      · show FwdIn ring root src (src + R) lane (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e)
          ((widthWindowGhost ref root lane src R w.1 w.2 e).2 - 1) after wc.1.2.clock
        rw [hs]
        exact fwdInStep ring root src (src + R) lane _ _ _ _ _ _ hfwd
    · right
      have hjc' : WidthJustClosed ref root lane src R Base
          (widthWindowNext ref root lane src R w e) := ⟨w, e, hw, rfl, hs⟩
      obtain ⟨U, hU, hUl, hUs, hUt, hUc⟩ := hterm
      have hcU := hcomp wc word U hrc hjc hpc (by rw [← hweq]; exact hcnt.symm)
        (by rw [← hweq]; exact hord) (by rw [← hweq]; exact hU) hUl hUs hUt
      rw [← hweq] at hcU
      have h01 := hord.2.1
      refine ⟨?_, widthWindowNext ref root lane src R w e, [], hre', hjc', rfl, rfl, hord',
        by show after ≤ w.1.2.clock + 1; omega, hp', ?_⟩
      · show 1 ≤ (widthWindowGhost ref root lane src R w.1 w.2 e).2
        rw [hs]
        omega
      · show FwdIn ring root src (src + R) lane (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e)
          ((widthWindowGhost ref root lane src R w.1 w.2 e).2 - 1) after (w.1.2.clock + 1)
        rw [hs, Nat.add_sub_cancel]
        have hlen : w.2.2 = (w.2.2 - 1) + 1 := by omega
        rw [hlen]
        exact fwdInAppend ring root src (src + R) lane U
          (completionStep ring (piD (ref.phys w.1.1)) w.1.2 e root src (src + R) lane 0 U hcU)
          (w.2.2 - 1) after wc.1.2.clock (w.1.2.clock + 1)
          (fwdInStep ring root src (src + R) lane _ _ _ _ _ _ hfwd) haft hUt (by omega)
          (by omega)

end

-- from BankRepairDigitPairBlock L3.PairBlock.fiveGoodPair
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- When the old cohort of cycle `5` is gone, five chained completions after `after` are
recorded (`FiveReach.fiveGoodOn` with the pair). Consumer: `widthRunPairBlock`. -/
theorem widthFiveGoodPair
    (Reach : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (hcomp : WidthOldCompletionPair ref root lane src R Base Reach)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hi : WidthFiveInvPair ref root lane src R Base Reach after w)
    (hb : WidthCohortLayout ref root src R w.1.1 ∧
      CohortCycOld R 5 (2 * R + 1) (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2) :
    FwdChain ring w.1.2 root src (src + R) lane 5 after := by
  obtain ⟨-, hold⟩ := hb
  obtain ⟨-, -, hi⟩ := hi
  rcases hi with ⟨h0, -⟩ | ⟨-, wc, word, hrc, hjc, hweq, hcnt, hord, haft, hpc, hfwd⟩
  · rcases hold with ⟨o', -, hin⟩ | hst
    · have := hin.1
      omega
    · have := hst.1
      omega
  · rcases hold with ⟨o', ho', hin⟩ | hst
    · have h5 : w.2.2 = 5 := hin.1
      have hle := cohortOldLe hin.2.1.1
      have hoe : o' = 2 * R + 1 := by omega
      subst hoe
      have hord0 := hord
      obtain ⟨-, h01, o, hino, hterm⟩ := hord
      obtain ⟨U, hU, hUl, hUs, hUt, hUc⟩ := hterm (cycPhaseDone hin hino)
      have hcU := hcomp wc word U hrc hjc hpc (by rw [← hweq]; exact hcnt.symm)
        (by rw [← hweq]; exact hord0) (by rw [← hweq]; exact hU) hUl hUs hUt
      rw [← hweq] at hcU
      rw [h5] at hfwd
      exact fwdInChain ring root src (src + R) lane _ 5 after _
        (fwdInAppend ring root src (src + R) lane U hcU 4 after wc.1.2.clock (w.1.2.clock + 1)
          hfwd haft hUt (by omega) (by omega))
    · have h6 : w.2.2 = 6 := hst.1
      rw [h6] at hfwd
      exact fwdInChain ring root src (src + R) lane _ 5 after _ hfwd

end

-- from BankRepairDigitPairBlock L3.PairBlock.runPairBlock
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
   (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
include hfix

include hn hR hsrc hend in
/-- **The per-block clock with no anchor**: `BlockCuts.runCoupledBlock` with the complete pair
`PairIn` in place of `AnchorIn after`. From any coupled start with the strengthened window
invariant, `WidthUseReach`, counter `0`, `after ≤ clock` and the complete pair on the audit start, and
a carried invariant `Carry`, the first state with five chained completions after `after` (seen
with `Carry`) costs `≤ 200 n R` doubled. Consumer: `BankRepairDigitBlockEntry`
(`entryBlockStage`). -/
theorem widthRunPairBlock (after : Nat) (P Q : ref.State → Prop)
    (Carry : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hcarry : ∀ w e, WidthWinInvD ref root lane src R Base w.1 w.2 → Carry w →
      Carry (widthWindowNext ref root lane src R w e))
    (hA : ∀ z, P z → ∃ w : (ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ WidthWinInvD ref root lane src R Base w.1 w.2 ∧
        WidthUseReach ref root lane src R w ∧ w.2.2 = 0 ∧
        after ≤ w.1.2.clock ∧ PairIn ring root src R w.1.2 ∧ Carry w)
    (hB : ∀ w : (ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Carry w → Q w.1.1) :
    WidthCoupledBlock ref P Q (200 * n * R) :=
  widthWindowCoupledBlock ref hfix hn root lane src R hR hsrc hend Base P Q
    (fun w => WidthFiveInvPair ref root lane src R Base (WidthUseReach ref root lane src R)
      after w ∧ Carry w)
    (fun w => FwdChain ring w.1.2 root src (src + R) lane 5 after ∧ Carry w)
    (fun w e hw hi _ => ⟨widthFiveInvPairStep ref hfix hn root lane src R hR hsrc hend Base
        (WidthUseReach ref root lane src R) after
        (fun v e' hv h => widthUseReachStep ref hfix hn root lane src R hR hsrc hend Base v e' hv h)
        (widthOldCompletionPairReach ref hfix hn root lane src R hR hsrc hend Base) w e hw hi.1,
      hcarry w e hw hi.2⟩)
    (fun w _ hi hb => ⟨widthFiveGoodPair ref root lane src R Base
        (WidthUseReach ref root lane src R) after
        (widthOldCompletionPairReach ref hfix hn root lane src R hR hsrc hend Base) w hi.1 hb,
      hi.2⟩)
    (fun z hz => by
      obtain ⟨w, hz, hw, hu, hc, haft, hp, hcar⟩ := hA z hz
      exact ⟨w, hz, hw, ⟨⟨hu, hp, Or.inl ⟨hc, haft⟩⟩, hcar⟩, hc⟩)
    (fun w hg => hB w hg.1 hg.2)

end

-- from BankRepairDigitBlockEntry L3.BlockEntry.pairPinStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z)))
  
include hfix

/-- The lift data of one interior pair is carried by every coupled letter (the ghost advances by
`widthWindowGhost`). Consumer: `widthPairsFromStep`. -/
theorem widthPairPinStep (hn : 5 ≤ n) (root : Fin n) (src : Nat) (hsrc : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) (h : WidthPairPin ref root src x) :
    WidthPairPin ref root src (widthDigitAuditNext ref x e) := by
  have hR := valueSpanTwo hn
  obtain ⟨hp, g, hw, hu⟩ := h
  exact ⟨hp, widthWindowGhost ref root DigitLane.writer src (valueSpan n) x g e,
    (widthWinInvDStep ref hfix hn root DigitLane.writer src (valueSpan n) hR hsrc hend
      (InheritedOk DigitLane.writer) x g hw e).1,
    widthUseReachStep ref hfix hn root DigitLane.writer src (valueSpan n) hR hsrc hend
      (InheritedOk DigitLane.writer) (x, g) e hw hu⟩

end

-- from BankRepairDigitBlockEntry L3.BlockEntry.pairsFromStep
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z)))
  
include hfix

/-- `WidthPairsFrom` is carried by every coupled letter (the audit start does not move). Consumer:
`entryBlockStage` (the pins of the later blocks ride along the run of block `j`). -/
theorem widthPairsFromStep (hn : 5 ≤ n) (j : Nat) (root : Fin n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) (h : WidthPairsFrom ref j root x) :
    WidthPairsFrom ref j root (widthDigitAuditNext ref x e) := by
  intro first hf i hi h1 h2
  exact widthPairPinStep ref hfix hn root _ h1 h2 x e (h first hf i hi h1 h2)

end

-- from BankRepairDigitBlockEntry L3.BlockEntry.pairsFromSucc
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  

/-- Dropping block `j`. Consumer: `entryBlockStage`. -/
theorem widthPairsFromSucc (j : Nat) (root : Fin n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthPairsFrom ref j root x) : WidthPairsFrom ref (j + 1) root x :=
  fun first hf i hi h1 h2 => h first hf i (by omega) h1 h2

end

-- from BankRepairDigitStructuralClean L3.DigitStructuralClean.CleanEntryPiece
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (hn : 5 ≤ n)
  
include hn

/-- The pieces of a clean entry cut: by leader, and by the first delimiter (or its absence).
Consumer: `widthCleanEntryBlockStage`. -/
def WidthCleanEntryPiece (j : Nat) (root : Fin n) : Option Nat → ref.State → Prop
  | none, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthZeroRun (ref) root (z, audit) ∧
      (∀ first, ¬ DigitFirstDelimiter ring root audit.start first) ∧
      (∀ i, i < j → BlockReceipt ring root audit i) ∧ WidthPairsFrom ref j root (z, audit)
  | some first, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthZeroRun (ref) root (z, audit) ∧
      DigitFirstDelimiter ring root audit.start first ∧
      (∀ i, i < j → BlockReceipt ring root audit i) ∧ WidthPairsFrom ref j root (z, audit)

end

-- from BankRepairDigitStructuralClean L3.DigitStructuralClean.cleanEntryBlockStage
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  
include hfix hn

/-- **The clean block stage `P' j → P' (j + 1)` at `200 n R`**: `entryBlockStage` with the
first-zero continuation on the clean start (the continuation is only carried). Consumer:
`widthCleanWaveAfterEntry`. -/
theorem widthCleanEntryBlockStage (j : Nat) :
    WidthCoupledBlock ref (WidthEntryCut (ref) j)
      (WidthEntryCut (ref) (j + 1)) (200 * n * valueSpan n) := by
  have hR := valueSpanTwo hn
  refine widthCoupledBlockSigma ref _ _ _
    (fun p : Fin n × Option Nat => WidthCleanEntryPiece ref j p.1 p.2) ?_ ?_
  · rintro z ⟨root, audit, hrun, hrec, hpf⟩
    rcases Classical.em (∃ first, DigitFirstDelimiter ring root audit.start first) with
      ⟨first, hf⟩ | hno
    · exact ⟨(root, some first), audit, hrun, hf, hrec, hpf⟩
    · exact ⟨(root, none), audit, hrun, fun f hf => hno ⟨f, hf⟩, hrec, hpf⟩
  rintro ⟨root, o⟩
  cases o with
  | none =>
      refine widthCoupledBlockOfImp ref _ _ _ ?_
      rintro z ⟨audit, hrun, hno, -, hpf⟩
      exact ⟨root, audit, hrun, fun i _ first hf => absurd hf (hno first),
        widthPairsFromSucc ref j root _ hpf⟩
  | some first =>
      rcases Classical.em (2 ≤ first + j * valueSpan n ∧
          first + j * valueSpan n + 2 * valueSpan n < n) with ⟨hsrc, hend⟩ | hg
      · refine widthCoupledBlockSigma ref _ _ _
          (fun after z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
            WidthZeroRun (ref) root (z, audit) ∧
            DigitFirstDelimiter ring root audit.start first ∧
            (∀ i, i < j → BlockReceipt ring root audit i) ∧
            WidthPairsFrom ref j root (z, audit) ∧ audit.clock = after) ?_ ?_
        · rintro z ⟨audit, hrun, hf, hrec, hpf⟩
          exact ⟨audit.clock, audit, hrun, hf, hrec, hpf, rfl⟩
        intro after
        refine widthRunPairBlock ref hfix hn root DigitLane.writer (first + j * valueSpan n)
          (valueSpan n) hR hsrc (by omega) (InheritedOk DigitLane.writer) after _ _
          (fun w => WidthZeroRun (ref) root w.1 ∧
            DigitFirstDelimiter ring root w.1.2.start first ∧
            (∀ i, i < j → BlockReceipt ring root w.1.2 i) ∧
            WidthPairsFrom ref (j + 1) root w.1) ?_ ?_ ?_
        · intro w e _ hc
          exact ⟨widthZeroRunStep (ref) root w.1 hc.1 e, hc.2.1,
            fun i hi => receiptStep ring root _ w.1.2 e i (hc.2.2.1 i hi),
            widthPairsFromStep ref hfix hn (j + 1) root w.1 e hc.2.2.2⟩
        · rintro z ⟨audit, hrun, hf, hrec, hpf, haft⟩
          obtain ⟨hp, g, hw, hu⟩ := hpf first hf j (Nat.le_refl j) hsrc hend
          exact ⟨((z, audit), (g.1, 0)), rfl,
            widthWinInvDReset ref root DigitLane.writer _ _ _ (z, audit) g hw 0,
            widthUseReachReset ref root DigitLane.writer _ _ (z, audit) g hu, rfl,
            by show after ≤ audit.clock; omega, hp, hrun, hf, hrec,
            widthPairsFromSucc ref j root _ hpf⟩
        · intro w hfw hc
          refine ⟨root, w.1.2, hc.1, fun i hi => ?_, hc.2.2.2⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact hc.2.2.1 i hij
          · have hie : i = j := by omega
            subst hie
            intro first' hf' _ _
            have he := firstDelimUnique ring root _ hc.2.1 hf'
            subst he
            exact ⟨after, hfw⟩
      · refine widthCoupledBlockOfImp ref _ _ _ ?_
        rintro z ⟨audit, hrun, hf, hrec, hpf⟩
        refine ⟨root, audit, hrun, fun i hi => ?_, widthPairsFromSucc ref j root _ hpf⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact hrec i hij
        · have hie : i = j := by omega
          subst hie
          intro first' hf' h1 h2
          have he := firstDelimUnique ring root _ hf hf'
          subst he
          exact absurd ⟨h1, h2⟩ hg

end

-- from BankRepairDigitStructuralClean L3.DigitStructuralClean.cleanWaveAfterEntry
section
variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  
include hfix hn

/-- **The value wave after the clean entry, to any receipt-closed target**: `K = n / R` clean
block stages of `200 n R` from `P' 0` to `P' K`, then the target `Q`, within `200 n^2`, given
that every first-zero continuation carrying the receipts of all blocks is in `Q` (for `Q` the
values-stable cut this is `WidthReceiptsClose`).  Consumer:
`L3.WriterStage.widthWaveClockOfWriter`, `L3.WriterCore.bankWriterValueWaveOfMoments`. -/
theorem widthCleanWaveAfterEntry (Q : ref.State → Prop)
    (hclose : ∀ (root : Fin n) (z : ref.State)
      (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthZeroRun ref root (z, audit) →
      (∀ i, i < valueBlocks n → BlockReceipt ring root audit i) → Q z) :
    BankRepairDigitChargedStage (ref.next)
      (WidthEntryCut (ref) 0) Q
      (bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (blockFit (valueBlocksFit n))
    (bankRepairDigitChargedWeaken _ (WidthEntryCut (ref) 0)
      (WidthEntryCut (ref) 0)
      (WidthEntryCut (ref) (valueBlocks n)) _ _ (fun _ h => h)
      (fun z ⟨root, audit, hrun, hrec, _⟩ => hclose root z audit hrun hrec)
      (bankRepairDigitChargedChain _ (WidthEntryCut (ref)) _
        (fun j => widthChargedOfCoupledBlock ref _ _ _ (widthCleanEntryBlockStage ref hfix hn j))
        (valueBlocks n)))

end

end L3.WidthWave

#print axioms L3.WidthWave.widthLeadEdge
#print axioms L3.WidthWave.widthRunPairBlock
#print axioms L3.WidthWave.widthCleanWaveAfterEntry
