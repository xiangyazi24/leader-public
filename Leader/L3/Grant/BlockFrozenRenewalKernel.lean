import Leader.L3.Grant.BlockFrozenRenewalTree

/-!
Kernel-generic first-stop layer of the G13 chain, for a stopped kernel
whose terminal states are labelled CLEAN (carrying a local BANK reference)
or GRANT.  Consumer: `GrantBlockFrozenRenewal.lean`.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Local BANK references at the compiled width. -/
abbrev GrantBlockFrozenRef (n : Nat) :=
  GrantBankReference.BankLocalReference (compileAdvice (ceilLogTwo n)).b

/-- Terminal labelling of a stopped state: still live, a CLEAN cut
carrying its local reference, or a GRANT (latched success). -/
inductive GrantBlockFrozenCutKind (n : Nat) where
  | live : GrantBlockFrozenCutKind n
  | clean : GrantBlockFrozenRef n → GrantBlockFrozenCutKind n
  | grant : GrantBlockFrozenCutKind n

/-- A stopped kernel on the original `Fin n` scheduler with CLEAN / GRANT
terminal labels.  No defect label exists. -/
structure GrantBlockFrozenKernel (n : Nat) where
  X : Type
  next : X → Fin n → X
  start : X
  kind : X → GrantBlockFrozenCutKind n

namespace GrantBlockFrozenKernel

variable {n : Nat} (K : GrantBlockFrozenKernel n)

def stop (_pre : List (Fin n)) (z : K.X) : Bool :=
  match K.kind z with
  | .live => false
  | .clean _ => true
  | .grant => true

def Terminal (z : K.X) : Prop := K.kind z ≠ .live

theorem stop_iff (pre : List (Fin n)) (z : K.X) :
    K.stop pre z = true ↔ K.Terminal z := by
  unfold stop Terminal
  generalize K.kind z = k
  cases k <;> simp

theorem terminal_of_mem (T : Nat) (cut : List (Fin n))
    (hmem : cut ∈ Prob.firstStoppedPrefixes K.next K.stop T []
      K.start) :
    K.Terminal (Prob.stoppedTapeRun K.next cut K.start) := by
  have hs := bankTrialSuccessStoppedPrefixesSound K.next K.stop T []
    K.start cut hmem
  exact (K.stop_iff ([] ++ cut) _).mp hs

/-- Every run state labelled CLEAN carries a Clean local reference. -/
def CleanSound : Prop :=
  ∀ (cut : List (Fin n)) (S : GrantBlockFrozenRef n),
    K.kind (Prob.stoppedTapeRun K.next cut K.start) = .clean S →
      BankTrialLocalClean (ceilLogTwo n) S

/-- Early CLEAN first stops, weighted by a function of the cut and of
its local reference. -/
noncomputable def earlyCleanSum (T W : Nat)
    (F : List (Fin n) → GrantBlockFrozenRef n → Nat) : Nat :=
  ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
    (fun cut =>
      if cut.length ≤ W then
        match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
        | .clean S => F cut S
        | .grant => 0
        | .live => 0
      else 0)).sum

noncomputable def earlyGrantMass (T W : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
    (fun cut =>
      if cut.length ≤ W then
        match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
        | .grant => n ^ (T - cut.length)
        | .clean _ => 0
        | .live => 0
      else 0)).sum

noncomputable def lateMass (T W : Nat) : Nat :=
  grantBlockFrozenColdNoStopUnitMass K.next K.Terminal K.start T W

/-- The exact first-stop partition of the original length-`T` tapes. -/
theorem partition (T W : Nat) (hWT : W ≤ T) :
    n ^ T =
      K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)) +
        K.earlyGrantMass T W + K.lateMass T W := by
  have hpart := grantBlockFrozenColdGenericPrefixPartition
    K.next K.stop K.Terminal (fun pre z => K.stop_iff pre z)
    T W [] K.start hWT
  have hstop :
      grantBlockFrozenColdStopUnitMass K.next K.stop T W [] K.start =
        K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)) +
          K.earlyGrantMass T W := by
    have hz : ∀ xs : List (List (Fin n)),
        (xs.map (fun _ => (0 : Nat))).sum = 0 := by
      intro xs
      induction xs with
      | nil => rfl
      | cons a as ih => simp [ih]
    have h := grantBlockFrozenColdSumThree
      (Prob.firstStoppedPrefixes K.next K.stop T [] K.start)
      (fun cut : List (Fin n) =>
        if cut.length ≤ W then
          match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
          | .clean _ => n ^ (T - cut.length)
          | .grant => 0
          | .live => 0
        else 0)
      (fun cut : List (Fin n) =>
        if cut.length ≤ W then
          match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
          | .grant => n ^ (T - cut.length)
          | .clean _ => 0
          | .live => 0
        else 0)
      (fun _ => 0)
      (fun cut : List (Fin n) =>
        if cut.length ≤ W then n ^ (T - cut.length) else 0)
      (by
        intro cut hmem
        have hterm := K.terminal_of_mem T cut hmem
        by_cases hc : cut.length ≤ W
        · cases hk : K.kind (Prob.stoppedTapeRun K.next cut K.start) with
          | live => exact absurd hk hterm
          | clean S => simp [hc, hk]
          | grant => simp [hc, hk]
        · simp [hc])
    rw [hz] at h
    exact h
  rw [← hpart, hstop]
  rfl

/-- Weight of the proxy event at a stopped leaf: a GRANT inside the
window counts one; a CLEAN cut counts the remaining-window renewal
success of its reference. -/
noncomputable def proxyWeight (ring : DirectedRing n)
    (root : Fin n) (W : Nat) (cut : List (Fin n)) (z : K.X)
    (suffix : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match K.kind z with
    | .grant => 1
    | .clean S =>
        Prob.indicator (bankTrialRenewalSuccessBy ring root S
          (W - cut.length) suffix)
    | .live => 0
  else 0

/-- The reward of the indexed renewal patterns at a stopped leaf: one
unit for a GRANT, the indexed pattern indicators for a CLEAN cut. -/
noncomputable def earlyRewardWeight (ring : DirectedRing n)
    (root : Fin n) (W L H : Nat) (cut : List (Fin n)) (z : K.X)
    (suffix : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match K.kind z with
    | .grant => 1
    | .clean S =>
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root S
            L j suffix)) H
    | .live => 0
  else 0

/-- The cost masked by the same successful-index event. -/
noncomputable def maskedCostWeight (ring : DirectedRing n)
    (root : Fin n) (W L H : Nat) (cut : List (Fin n)) (z : K.X)
    (suffix : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match K.kind z with
    | .clean S =>
        bankTrialSuccessStageIndexSum (fun j =>
          cut.length * Prob.indicator (bankTrialRenewalPattern
            ring root S L j suffix) +
          bankTrialRenewalTau ring root S L j suffix) H
    | .grant => 0
    | .live => 0
  else 0

/-- Per-word window inequality at a CLEAN cut. -/
theorem cleanMaskedWord (ring : DirectedRing n) (root : Fin n)
    (S : GrantBlockFrozenRef n) (W L H : Nat)
    (cut suffix : List (Fin n)) (hcut : cut.length ≤ W) :
    W * bankTrialSuccessStageIndexSum (fun j =>
      Prob.indicator (bankTrialRenewalPattern ring root S
        L j suffix)) H ≤
    W * Prob.indicator (bankTrialRenewalSuccessBy ring root S
      (W - cut.length) suffix) +
    bankTrialSuccessStageIndexSum (fun j =>
      cut.length * Prob.indicator (bankTrialRenewalPattern ring root
        S L j suffix) +
      bankTrialRenewalTau ring root S L j suffix) H := by
  have hone := grantBlockFrozenRenewalPatternOneHot ring root S
    L H suffix
  have hcost :
      bankTrialSuccessStageIndexSum (fun j =>
        cut.length * Prob.indicator (bankTrialRenewalPattern ring root
          S L j suffix) +
        bankTrialRenewalTau ring root S L j suffix) H =
      cut.length * bankTrialSuccessStageIndexSum (fun j =>
        Prob.indicator (bankTrialRenewalPattern ring root
          S L j suffix)) H +
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalTau ring root S L j suffix) H :=
    grantBlockFrozenColdMaskedStageSum cut.length _ _ H
  have hwindow :
      (W - cut.length) *
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            S L j suffix)) H ≤
      (W - cut.length) *
        Prob.indicator (bankTrialRenewalSuccessBy ring root S
          (W - cut.length) suffix) +
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalTau ring root S L j suffix) H :=
    bankTrialRenewalWordWindow ring root S L (W - cut.length) H suffix
  have hsplit :
      W * bankTrialSuccessStageIndexSum (fun j =>
        Prob.indicator (bankTrialRenewalPattern ring root
          S L j suffix)) H =
      (W - cut.length) *
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            S L j suffix)) H +
      cut.length *
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            S L j suffix)) H := by
    calc
      _ = ((W - cut.length) + cut.length) *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                S L j suffix)) H := by
          rw [Nat.sub_add_cancel hcut]
      _ = _ := Nat.add_mul _ _ _
  have hprefixCharge :
      cut.length *
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            S L j suffix)) H ≤ cut.length := by
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left cut.length hone)
  have hsuccessScale :
      (W - cut.length) *
        Prob.indicator (bankTrialRenewalSuccessBy ring root S
          (W - cut.length) suffix) ≤
      W *
        Prob.indicator (bankTrialRenewalSuccessBy ring root S
          (W - cut.length) suffix) :=
    Nat.mul_le_mul_right _ (Nat.sub_le W cut.length)
  rw [hsplit, hcost]
  omega

/-- Pointwise early first-stop window: a GRANT is paid once by the
proxy, only a CLEAN cut pays an index-dependent cost. -/
theorem earlyRewardCutWindow (ring : DirectedRing n) (root : Fin n)
    (W L H : Nat) (cut : List (Fin n)) (z : K.X)
    (suffix : List (Fin n)) :
    W * K.earlyRewardWeight ring root W L H cut z suffix ≤
    W * K.proxyWeight ring root W cut z suffix +
      K.maskedCostWeight ring root W L H cut z suffix := by
  by_cases hcut : cut.length ≤ W
  · cases hk : K.kind z with
    | live =>
        simp [earlyRewardWeight, maskedCostWeight, proxyWeight,
          hcut, hk]
    | grant =>
        simp [earlyRewardWeight, maskedCostWeight, proxyWeight,
          hcut, hk]
    | clean S =>
        simpa [earlyRewardWeight, maskedCostWeight, proxyWeight,
          hcut, hk] using
          (cleanMaskedWord ring root S W L H cut suffix hcut)
  · simp [earlyRewardWeight, maskedCostWeight, proxyWeight, hcut]

noncomputable def proxyMass (ring : DirectedRing n) (root : Fin n)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord K.next K.stop
      (fun cut z _ suffix => K.proxyWeight ring root W cut z suffix)
      T [] K.start word)

noncomputable def rewardMass (ring : DirectedRing n) (root : Fin n)
    (T W L H : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord K.next K.stop
      (fun cut z _ suffix =>
        K.earlyRewardWeight ring root W L H cut z suffix)
      T [] K.start word)

noncomputable def maskedCostMass (ring : DirectedRing n)
    (root : Fin n) (T W L H : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord K.next K.stop
      (fun cut z _ suffix =>
        K.maskedCostWeight ring root W L H cut z suffix)
      T [] K.start word)

/-- Global first-stop masked-window inequality on the original tapes. -/
theorem globalMaskedWindow (ring : DirectedRing n) (root : Fin n)
    (T W L H : Nat) :
    W * K.rewardMass ring root T W L H ≤
      W * K.proxyMass ring root T W +
        K.maskedCostMass ring root T W L H := by
  unfold rewardMass proxyMass maskedCostMass
  exact grantBlockFrozenRenewalColdStoppedWeightedSchedule
    K.next K.stop
    (fun cut z suffix => K.earlyRewardWeight ring root W L H cut z suffix)
    (fun cut z suffix => K.proxyWeight ring root W cut z suffix)
    (fun cut z suffix => K.maskedCostWeight ring root W L H cut z suffix)
    W T K.start
    (fun cut z suffix =>
      K.earlyRewardCutWindow ring root W L H cut z suffix)


/-! ### Cut-level decompositions and the first-stop bridges -/

noncomputable def cleanPatternCut (ring : DirectedRing n)
    (root : Fin n) (T W L j : Nat) (cut : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | .clean S =>
        bankTrialRenewalPatternMass ring root S (T - cut.length) L j
    | .grant => 0
    | .live => 0
  else 0

noncomputable def cleanMaskedCostCut (ring : DirectedRing n)
    (root : Fin n) (T W L j : Nat) (cut : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | .clean S =>
        cut.length * bankTrialRenewalPatternMass ring root S
          (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root S (T - cut.length) L j
    | .grant => 0
    | .live => 0
  else 0

noncomputable def grantCut (T W : Nat) (cut : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | .grant => n ^ (T - cut.length)
    | .clean _ => 0
    | .live => 0
  else 0

theorem scheduleMaskedIndex
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBlockFrozenRef n) (cut : List (Fin n))
    (T L H : Nat) :
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
      bankTrialSuccessStageIndexSum (fun j =>
        cut.length * Prob.indicator (bankTrialRenewalPattern
          ring root
          S
          L j suffix) +
        bankTrialRenewalTau ring root
          S
          L j suffix) H) =
    bankTrialSuccessStageIndexSum (fun j =>
      cut.length * bankTrialRenewalPatternMass ring root
        S
        (T - cut.length) L j +
      bankTrialRenewalPatternCost ring root
        S
        (T - cut.length) L j) H := by
  calc
    _ = bankTrialSuccessStageIndexSum (fun j =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            cut.length * Prob.indicator (bankTrialRenewalPattern
              ring root
              S
              L j suffix) +
            bankTrialRenewalTau ring root
              S
              L j suffix)) H :=
          (bankTrialSuccessStageIndexSumSchedule
            n (T - cut.length) H _).symm
    _ = _ := by
      apply grantBlockFrozenColdStageIndexCongr
      intro j _
      rw [bankTrialC5ScheduleSumAdd,
        bankTrialSuccessScheduleSumScale]
      rfl

theorem rewardCutDecomposition (ring : DirectedRing n) (root : Fin n)
    (T W L H : Nat) (cut : List (Fin n)) :
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
      K.earlyRewardWeight ring root W L H cut
        (Prob.stoppedTapeRun K.next cut K.start) suffix) =
    bankTrialSuccessStageIndexSum (fun j =>
      K.cleanPatternCut ring root T W L j cut) H +
    K.grantCut T W cut := by
  by_cases hc : cut.length ≤ W
  · cases hk : K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | live =>
        simp [earlyRewardWeight, cleanPatternCut, grantCut, hc, hk,
          grantBlockFrozenColdScheduleZero,
          bankTrialSuccessStageIndexSumZero]
    | grant =>
        simp [earlyRewardWeight, cleanPatternCut, grantCut, hc, hk,
          grantBlockFrozenColdScheduleOne,
          bankTrialSuccessStageIndexSumZero]
    | clean S =>
        simp [earlyRewardWeight, cleanPatternCut, grantCut, hc, hk,
          bankTrialRenewalPatternMass,
          bankTrialSuccessStageIndexSumSchedule]
  · simp [earlyRewardWeight, cleanPatternCut, grantCut, hc,
      grantBlockFrozenColdScheduleZero,
      bankTrialSuccessStageIndexSumZero]

theorem maskedCostCutDecomposition (ring : DirectedRing n)
    (root : Fin n) (T W L H : Nat) (cut : List (Fin n)) :
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
      K.maskedCostWeight ring root W L H cut
        (Prob.stoppedTapeRun K.next cut K.start) suffix) =
    bankTrialSuccessStageIndexSum (fun j =>
      K.cleanMaskedCostCut ring root T W L j cut) H := by
  by_cases hc : cut.length ≤ W
  · cases hk : K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | live =>
        simp [maskedCostWeight, cleanMaskedCostCut, hc, hk,
          grantBlockFrozenColdScheduleZero,
          bankTrialSuccessStageIndexSumZero]
    | grant =>
        simp [maskedCostWeight, cleanMaskedCostCut, hc, hk,
          grantBlockFrozenColdScheduleZero,
          bankTrialSuccessStageIndexSumZero]
    | clean S =>
        simpa only [maskedCostWeight, cleanMaskedCostCut, if_pos hc,
          hk] using (scheduleMaskedIndex ring root S cut T L H)
  · simp [maskedCostWeight, cleanMaskedCostCut, hc,
      grantBlockFrozenColdScheduleZero,
      bankTrialSuccessStageIndexSumZero]

/-- The exact reward bridge on the first-stop cut list. -/
theorem rewardMassBridge (ring : DirectedRing n) (root : Fin n)
    (T W L H : Nat) :
    K.rewardMass ring root T W L H =
      bankTrialSuccessStageIndexSum (fun j =>
        K.earlyCleanSum T W (fun cut S =>
          bankTrialRenewalPatternMass ring root S
            (T - cut.length) L j)) H +
      K.earlyGrantMass T W := by
  have hf := bankTrialSuccessNatStoppedFactorization K.next K.stop
    (fun cut z _ suffix => K.earlyRewardWeight ring root W L H cut z
      suffix) K.start T
  unfold rewardMass
  rw [hf]
  change
    ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
      (fun cut => Prob.scheduleSum n (T - cut.length) (fun suffix =>
        K.earlyRewardWeight ring root W L H cut
          (Prob.stoppedTapeRun K.next cut K.start) suffix))).sum =
    bankTrialSuccessStageIndexSum (fun j =>
      ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
        (K.cleanPatternCut ring root T W L j)).sum) H +
    ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
      (K.grantCut T W)).sum
  apply grantBlockFrozenColdListRewardConvolution
  intro cut _
  exact K.rewardCutDecomposition ring root T W L H cut

/-- The exact masked-cost bridge on the first-stop cut list. -/
theorem maskedCostMassBridge (ring : DirectedRing n) (root : Fin n)
    (T W L H : Nat) :
    K.maskedCostMass ring root T W L H =
      bankTrialSuccessStageIndexSum (fun j =>
        K.earlyCleanSum T W (fun cut S =>
          cut.length * bankTrialRenewalPatternMass ring root S
            (T - cut.length) L j +
          bankTrialRenewalPatternCost ring root S
            (T - cut.length) L j)) H := by
  have hf := bankTrialSuccessNatStoppedFactorization K.next K.stop
    (fun cut z _ suffix => K.maskedCostWeight ring root W L H cut z
      suffix) K.start T
  unfold maskedCostMass
  rw [hf]
  change
    ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
      (fun cut => Prob.scheduleSum n (T - cut.length) (fun suffix =>
        K.maskedCostWeight ring root W L H cut
          (Prob.stoppedTapeRun K.next cut K.start) suffix))).sum =
    bankTrialSuccessStageIndexSum (fun j =>
      ((Prob.firstStoppedPrefixes K.next K.stop T [] K.start).map
        (K.cleanMaskedCostCut ring root T W L j)).sum) H
  apply grantBlockFrozenColdListMaskedConvolution
  intro cut _
  exact K.maskedCostCutDecomposition ring root T W L H cut


/-! ### Per-cut index bounds and their sums over the first stops -/

/-- Specialization to the genuine sound physical CLEAN terminal.
No new Clean assumption: it follows from its recorded terminal
soundness. The compiler's K and width conditions are derived as
in the proof rather than added as independent premises. -/
theorem soundIndexCutBounds
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (S : GrantBlockFrozenRef n)
    (hclean : BankTrialLocalClean (ceilLogTwo n) S)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (cut : List (Fin n)) (hcut : cut.length ≤ W)
    (hj : j < H) :
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
      (1023 * L) * n ^ (T - cut.length) ≤
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ (j + 1) *
      bankTrialRenewalPatternMass ring root
        S
        (T - cut.length) L j ∧
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      (cut.length * bankTrialRenewalPatternMass ring root
        S
        (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root
          S
          (T - cut.length) L j) ≤
    n ^ (T - cut.length) *
      (cut.length + n *
        (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
          j * bankTrialRenewalIndexStepCharge
            (ceilLogTwo n))) := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hspec := (ceilLogTwo_spec n (by omega)).2
    by_cases hc : ceilLogTwo n ≤ 2
    · have hp := Nat.pow_le_pow_right
        (by decide : 0 < (2 : Nat)) hc
      have hfour : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  have hpositive :
      0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n +
      productionKappa (ceilLogTwo n)
    omega
  have hK :
      (compileAdvice (ceilLogTwo n)).K <
        2 ^ (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_trans (Nat.lt_succ_self _)
      (compileAdvice_K_lt_two_pow_b (ceilLogTwo n) hq)
  exact bankTrialRenewalColdCleanIndexCutBounds
    ring root (by omega) hsp hw hlarge hpositive hK
    S hclean
    L W H T j hL hbudgetCold cut hcut hj

theorem earlyCleanSum_mono (hsound : K.CleanSound) (T W : Nat)
    (A B : List (Fin n) → GrantBlockFrozenRef n → Nat) (p q : Nat)
    (hrow : ∀ (cut : List (Fin n)) (S : GrantBlockFrozenRef n),
      cut.length ≤ W → BankTrialLocalClean (ceilLogTwo n) S →
        p * A cut S ≤ q * B cut S) :
    p * K.earlyCleanSum T W A ≤ q * K.earlyCleanSum T W B := by
  unfold earlyCleanSum
  apply grantBlockFrozenRenewalColdListMulSum
  intro cut _
  by_cases hcut : cut.length ≤ W
  · cases hk : K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | live => simp [hcut, hk]
    | grant => simp [hcut, hk]
    | clean S =>
        simpa [hcut, hk] using hrow cut S hcut (hsound cut S hk)
  · simp [hcut]

theorem earlyCleanIndexMassBound (ring : DirectedRing n)
    (root : Fin n) (hsound : K.CleanSound) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T) (hj : j < H) :
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
      (1023 * L) *
      K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)) ≤
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ (j + 1) *
      K.earlyCleanSum T W (fun cut S =>
        bankTrialRenewalPatternMass ring root S
          (T - cut.length) L j) := by
  apply K.earlyCleanSum_mono hsound
  intro cut S hcut hS
  exact (soundIndexCutBounds ring root hn hsp hw hlarge S hS
    L W H T j hL hbudgetCold cut hcut hj).1

theorem earlyCleanIndexChargeBound (ring : DirectedRing n)
    (root : Fin n) (hsound : K.CleanSound) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T) (hj : j < H) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      K.earlyCleanSum T W (fun cut S =>
        cut.length * bankTrialRenewalPatternMass ring root S
          (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root S
          (T - cut.length) L j) ≤
    K.earlyCleanSum T W (fun cut _ =>
      n ^ (T - cut.length) *
        (cut.length + n *
          (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))) := by
  have hs := K.earlyCleanSum_mono hsound T W
    (fun cut S =>
      cut.length * bankTrialRenewalPatternMass ring root S
        (T - cut.length) L j +
      bankTrialRenewalPatternCost ring root S (T - cut.length) L j)
    (fun cut _ =>
      n ^ (T - cut.length) *
        (cut.length + n *
          (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))))
    (2 ^ (compileAdvice (ceilLogTwo n)).K) 1
    (by
      intro cut S hcut hS
      simpa only [Nat.one_mul] using
        (soundIndexCutBounds ring root hn hsp hw hlarge S hS
          L W H T j hL hbudgetCold cut hcut hj).2)
  simpa only [Nat.one_mul] using hs

/-! ### Mass convolution -/

theorem massConvolution (ring : DirectedRing n) (root : Fin n)
    (hsound : K.CleanSound) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (L W H T : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T) :
    K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)) *
      bankTrialSuccessStageIndexSum
        (grantBlockFrozenColdCoefficient n (ceilLogTwo n) L H) H ≤
    (grantBlockFrozenColdDenominatorBase (ceilLogTwo n) L) ^ H *
      bankTrialSuccessStageIndexSum (fun j =>
        K.earlyCleanSum T W (fun cut S =>
          bankTrialRenewalPatternMass ring root S
            (T - cut.length) L j)) H := by
  have hindex := grantBlockFrozenRenewalStageIndexMonoBelow
    (fun j =>
      K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)) *
      grantBlockFrozenColdCoefficient n (ceilLogTwo n) L H j)
    (fun j =>
      (grantBlockFrozenColdDenominatorBase (ceilLogTwo n) L) ^ H *
      K.earlyCleanSum T W (fun cut S =>
        bankTrialRenewalPatternMass ring root S
          (T - cut.length) L j))
    H (by
      intro j hj
      have hle : j + 1 ≤ H := by omega
      have hrow := K.earlyCleanIndexMassBound ring root hsound hn hsp
        hw hlarge L W H T j hL hbudgetCold hj
      have hscaled := grantBlockFrozenRenewalCommonPowerLift
        (grantBlockFrozenColdDenominatorBase (ceilLogTwo n) L)
        (grantBlockFrozenColdLowerBase n (ceilLogTwo n) L)
        (1023 * L)
        (K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)))
        H j
        (K.earlyCleanSum T W (fun cut S =>
          bankTrialRenewalPatternMass ring root S
            (T - cut.length) L j))
        hle (by
          simpa only [grantBlockFrozenColdDenominatorBase,
            grantBlockFrozenColdLowerBase] using hrow)
      simpa only [grantBlockFrozenColdCoefficient] using hscaled)
  simpa only [bankTrialSuccessStageIndexSumScale] using hindex


/-! ### Joint first-stop cost -/

theorem stopUnitWithin (T W : Nat) (hWT : W ≤ T) :
    grantBlockFrozenColdStopUnitMass K.next K.stop T W [] K.start ≤
      n ^ T := by
  have hpart := grantBlockFrozenColdGenericPrefixPartition
    K.next K.stop K.Terminal (fun pre z => K.stop_iff pre z)
    T W [] K.start hWT
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hpart)

theorem earlyCleanBudget (T W g : Nat) :
    K.earlyCleanSum T W (fun cut _ =>
      n ^ (T - cut.length) * (cut.length + g)) ≤
    grantBlockFrozenColdEarlyLengthMass K.next K.stop T W [] K.start +
      g * grantBlockFrozenColdStopUnitMass K.next K.stop T W []
        K.start := by
  unfold earlyCleanSum grantBlockFrozenColdEarlyLengthMass
    grantBlockFrozenColdStopUnitMass
  apply grantBlockFrozenColdListBudget
  intro cut _
  by_cases hcut : cut.length ≤ W
  · cases hk : K.kind (Prob.stoppedTapeRun K.next cut K.start) with
    | live => simp [hcut, hk]
    | grant => simp [hcut, hk]
    | clean S =>
        simp only [if_pos hcut, hk]
        exact Nat.le_of_eq (by
          rw [Nat.mul_add, Nat.mul_comm (n ^ (T - cut.length))
            cut.length, Nat.mul_comm (n ^ (T - cut.length)) g])
  · simp [hcut]

theorem jointFirstStopReserve (T W : Nat) (hWT : W ≤ T)
    (hcost : costNumerator K.next K.Terminal K.start T ≤
      n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)) :
    grantBlockFrozenColdEarlyLengthMass K.next K.stop T W [] K.start +
      W * K.lateMass T W ≤
    n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) := by
  have h := grantBlockFrozenColdJointFirstHitCost K.next K.stop
    K.Terminal (fun pre z => K.stop_iff pre z) T W [] K.start hWT
  exact Nat.le_trans h hcost

theorem jointIndexCharge (ring : DirectedRing n) (root : Fin n)
    (hsound : K.CleanSound) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T) (hj : j < H)
    (hcost : costNumerator K.next K.Terminal K.start T ≤
      n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      K.earlyCleanSum T W (fun cut S =>
        cut.length * bankTrialRenewalPatternMass ring root S
          (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root S
          (T - cut.length) L j) +
      W * K.lateMass T W ≤
    n ^ T * (n *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
        j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) := by
  have hwindow : W ≤ T :=
    Nat.le_trans (Nat.le_add_right W (H * L)) hbudgetCold
  have hsource := K.earlyCleanIndexChargeBound ring root hsound hn hsp
    hw hlarge L W H T j hL hbudgetCold hj
  have hbudget := K.earlyCleanBudget T W
    (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
      j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
  have hunit := K.stopUnitWithin T W hwindow
  have hunitScaled := Nat.mul_le_mul_left
    (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
      j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) hunit
  have hclean :
      2 ^ (compileAdvice (ceilLogTwo n)).K *
        K.earlyCleanSum T W (fun cut S =>
          cut.length * bankTrialRenewalPatternMass ring root S
            (T - cut.length) L j +
          bankTrialRenewalPatternCost ring root S
            (T - cut.length) L j) ≤
      grantBlockFrozenColdEarlyLengthMass K.next K.stop T W []
          K.start +
        n ^ T * (n *
          (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) := by
    calc
      _ ≤ K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length) *
            (cut.length + n *
              (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
                j * bankTrialRenewalIndexStepCharge
                  (ceilLogTwo n)))) := hsource
      _ ≤ grantBlockFrozenColdEarlyLengthMass K.next K.stop T W []
            K.start +
          (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) *
          grantBlockFrozenColdStopUnitMass K.next K.stop T W []
            K.start := hbudget
      _ ≤ grantBlockFrozenColdEarlyLengthMass K.next K.stop T W []
            K.start +
          (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) *
              n ^ T := Nat.add_le_add_left hunitScaled _
      _ = _ := by
            rw [Nat.mul_comm
              (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
                j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
              (n ^ T)]
  have hjoint := K.jointFirstStopReserve T W hwindow hcost
  have hpaid := grantBlockFrozenColdJointIndexArithmetic
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (K.earlyCleanSum T W (fun cut S =>
      cut.length * bankTrialRenewalPatternMass ring root S
        (T - cut.length) L j +
      bankTrialRenewalPatternCost ring root S (T - cut.length) L j))
    (grantBlockFrozenColdEarlyLengthMass K.next K.stop T W []
      K.start)
    (n ^ T)
    (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
      j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
    W (K.lateMass T W)
    ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)
    hclean hjoint
  simpa only [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using hpaid


/-! ### Cost convolution and the cleared window -/

theorem maskedCostConvolution (ring : DirectedRing n) (root : Fin n)
    (hsound : K.CleanSound) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (L W H T : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (hcost : costNumerator K.next K.Terminal K.start T ≤
      n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
        K.maskedCostMass ring root T W L H +
      H * (W * K.lateMass T W) ≤
    n ^ T * bankTrialSuccessStageIndexSum (fun j =>
      n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
        j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H := by
  have hindex := grantBlockFrozenRenewalStageIndexMonoBelow
    (fun j =>
      2 ^ (compileAdvice (ceilLogTwo n)).K *
        K.earlyCleanSum T W (fun cut S =>
          cut.length * bankTrialRenewalPatternMass ring root S
            (T - cut.length) L j +
          bankTrialRenewalPatternCost ring root S
            (T - cut.length) L j) +
      W * K.lateMass T W)
    (fun j =>
      n ^ T * (n *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
          j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))))
    H (by
      intro j hj
      exact K.jointIndexCharge ring root hsound hn hsp hw hlarge
        L W H T j hL hbudgetCold hj hcost)
  calc
    2 ^ (compileAdvice (ceilLogTwo n)).K *
        K.maskedCostMass ring root T W L H +
      H * (W * K.lateMass T W) =
      bankTrialSuccessStageIndexSum (fun j =>
        2 ^ (compileAdvice (ceilLogTwo n)).K *
          K.earlyCleanSum T W (fun cut S =>
            cut.length * bankTrialRenewalPatternMass ring root S
              (T - cut.length) L j +
            bankTrialRenewalPatternCost ring root S
              (T - cut.length) L j) +
        W * K.lateMass T W) H := by
          rw [grantBlockFrozenColdStageAdd,
            bankTrialSuccessStageIndexSumScale,
            bankTrialSuccessStageIndexSumConstant,
            K.maskedCostMassBridge]
    _ ≤ bankTrialSuccessStageIndexSum (fun j =>
        n ^ T * (n *
          ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
              5 * (compileAdvice (ceilLogTwo n)).b + 13) +
            bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))) H :=
            hindex
    _ = _ := bankTrialSuccessStageIndexSumScale _ _ H

/-- The cleared-window inequality for the proxy mass of a CLEAN / GRANT
kernel: the exact analogue of `bankTrialRenewalColdClearedWindowAnyH`
with no defect term. -/
theorem clearedWindow (ring : DirectedRing n) (root : Fin n)
    (hsound : K.CleanSound) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (L H T W : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T) (hbudgetCold : W + H * L ≤ T)
    (hcost : costNumerator K.next K.Terminal K.start T ≤
      n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)) :
    W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * n ^ T *
      bankTrialSuccessStageIndexSum (fun j =>
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
          L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
            ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
        (1023 * L) *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
          (H - (j + 1))) H ≤
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ H *
      (W * (2 ^ (compileAdvice (ceilLogTwo n)).K) *
        K.proxyMass ring root T W +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            5 * (compileAdvice (ceilLogTwo n)).b + 13) +
            bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H) := by
  have hpartition := K.partition T W hwindow
  have hmass := K.massConvolution ring root hsound hn hsp hw hlarge
    L W H T hL hbudgetCold
  have hgeo :
      bankTrialSuccessStageIndexSum
        (grantBlockFrozenColdCoefficient n (ceilLogTwo n) L H) H ≤
      (grantBlockFrozenColdDenominatorBase (ceilLogTwo n) L) ^ H :=
    bankTrialRenewalColdGeometricCoefficientSumBound
      n (ceilLogTwo n) L H
  have hlate := bankTrialColdLateConvolution n (ceilLogTwo n) L H
  have hwindowMass := K.globalMaskedWindow ring root T W L H
  rw [K.rewardMassBridge] at hwindowMass
  have hcostConv := K.maskedCostConvolution ring root hsound hn hsp hw
    hlarge L W H T hL hbudgetCold hcost
  have hcombined := grantBlockFrozenColdWindowCompositionArithmetic
    W
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (n ^ T)
    ((grantBlockFrozenColdDenominatorBase (ceilLogTwo n) L) ^ H)
    (bankTrialSuccessStageIndexSum
      (grantBlockFrozenColdCoefficient n (ceilLogTwo n) L H) H)
    (K.earlyCleanSum T W (fun cut _ => n ^ (T - cut.length)))
    (K.earlyGrantMass T W)
    0
    (K.lateMass T W)
    (bankTrialSuccessStageIndexSum (fun j =>
      K.earlyCleanSum T W (fun cut S =>
        bankTrialRenewalPatternMass ring root S
          (T - cut.length) L j)) H)
    (K.proxyMass ring root T W)
    (K.maskedCostMass ring root T W L H)
    (bankTrialSuccessStageIndexSum (fun j =>
      n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
        j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H)
    H (by omega) hmass hgeo hlate hwindowMass hcostConv
  change
    W * 2 ^ (compileAdvice (ceilLogTwo n)).K * n ^ T *
      bankTrialSuccessStageIndexSum
        (grantBlockFrozenColdCoefficient n (ceilLogTwo n) L H) H ≤
    (grantBlockFrozenColdDenominatorBase (ceilLogTwo n) L) ^ H *
      (W * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        (K.proxyMass ring root T W + 0) +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
             5 * (compileAdvice (ceilLogTwo n)).b + 13) +
           bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
           j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H)
  simpa only [Nat.add_zero] using hcombined

end GrantBlockFrozenKernel

end L3
#print axioms L3.GrantBlockFrozenKernel.partition
#print axioms L3.GrantBlockFrozenKernel.globalMaskedWindow
#print axioms L3.GrantBlockFrozenKernel.massConvolution
#print axioms L3.GrantBlockFrozenKernel.maskedCostConvolution
#print axioms L3.GrantBlockFrozenKernel.clearedWindow
