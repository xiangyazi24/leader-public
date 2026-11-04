import Leader.L3.Grant.BlockFamilyRate
import Leader.L3.Grant.Cutoffs

/-!
# G16: C.18 and C.19, the block bound on the actual family

From the family rate on the C.9--C.10 family (`grantBlockFamilyRateOnSelection`)
to a lower bound on the mass of the G18 first-hit event in one window.

* A frozen hit is a G18 hit or a defect crossing.  The residual case of
  `GrantBlockSuccess.lean` (a root BANK success whose POST cut has neither
  leader nor grant) is itself a G18 hit: on a path with no earlier G18 cut the
  prefix is rootless and grant-free, and the BANK success mints a grant
  (`grantClockPrivateBankSuccessMintsPhysicalGrant`).
* Hence the family-or-G18 mass is at most the G18 mass plus the crossing mass
  of the members, and C.11 pays the crossing mass.
* The sparse-defect term `Density.N (badSet ring C)` is the defect count
  `defects ring C` (`defects_eq_N`), at most `4 n` from the density hypothesis;
  with the radius cutoff this makes the crossing term negligible.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Physical words compose by append.

Consumer: `grantBlockFirstBankFailureG18Hit`. -/
private theorem famBlockWordAppend
    {n q : Nat} (ring : DirectedRing n) :
    ∀ (pre suffix : List (Fin n))
      (C : Counter.Config q n),
      Counter.Word ring (pre ++ suffix) C =
        Counter.Word ring suffix (Counter.Word ring pre C) := by
  intro pre
  induction pre with
  | nil =>
      intro suffix C
      rfl
  | cons edge rest ih =>
      intro suffix C
      change Counter.Word ring (rest ++ suffix)
          ((protocol q).step ring C edge) =
        Counter.Word ring suffix
          (Counter.Word ring rest
            ((protocol q).step ring C edge))
      exact ih suffix _

/-- The residual case of `GrantBlockSuccess.lean` closes: a first root BANK
success on a path with no earlier G18 cut mints a physical grant, so it is a
G18 hit.

Consumer: `grantBlockFrozenHitG18OrCrossing`. -/
theorem grantBlockFirstBankFailureG18Hit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (root : Fin n) (W : Nat) (word : List (Fin n))
    (hbank : GrantBlockFirstBankFailure ring root C
      (word.take W)) :
    GrantBlockSurrogateG18HitWithin ring C W word := by
  obtain ⟨pre, edge, suffix, hword, _, hsucc⟩ := hbank
  by_cases hready :
      headlineGrantReady ring (Counter.Word ring pre C) ∨
        headlineGeneratedTarget ring (Counter.Word ring pre C)
  · exact ⟨pre, edge :: suffix, hword, hready⟩
  · have hpre := grantBlockMarginalPurifiedWord ring hn pre C hp
    obtain ⟨hroot, hzero⟩ :=
      grantBlockG18PendingRootlessGrantless ring _ hpre hready
    have hedge : edge = root := by
      by_cases he : edge = root
      · exact he
      · exfalso
        unfold GrantBankReference.bankLocalReferenceRealSuccessEvent
          at hsucc
        rw [if_neg he] at hsucc
        exact Bool.false_ne_true hsucc
    have hsuccess :
        Counter.resetColdPrivateSuccessAt ring edge
          (Counter.Word ring pre C) edge := by
      refine ⟨rfl, ?_⟩
      unfold GrantBankReference.bankLocalReferenceRealSuccessEvent
        at hsucc
      rw [if_pos hedge] at hsucc
      exact hsucc
    have hgrant :=
      grantClockPrivateBankSuccessMintsPhysicalGrant ring
        (Counter.Word ring pre C) edge hsp hroot hzero hsuccess
    have hpost := headlineStagesPurifiedStep ring hn
      (Counter.Word ring pre C) edge hpre
    have hready' :
        headlineGrantReady ring
          (headlinePhysicalNext ring (Counter.Word ring pre C)
            edge) :=
      Or.inr ⟨hpost, edge, hgrant⟩
    refine ⟨pre ++ [edge], suffix, ?_, Or.inl ?_⟩
    · rw [hword]
      simp only [List.append_assoc, List.singleton_append]
    · have hstate :
          Counter.Word ring (pre ++ [edge]) C =
            headlinePhysicalNext ring
              (Counter.Word ring pre C) edge := by
        rw [famBlockWordAppend ring pre [edge] C]
        rfl
      rw [hstate]
      exact hready'

/-- A frozen hit in the `W`-prefix is a G18 hit or a defect crossing of the
member's own root.  There is no third case.

Consumer: `grantBlockFamilyOrG18MassLeCrossing`. -/
theorem grantBlockFrozenHitG18OrCrossing
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
    (W : Nat) (word : List (Fin n))
    (hhit : grantBlockFrozenProxyHit ring member
      (word.take W) = true) :
    GrantBlockSurrogateG18HitWithin ring member.2.val W word ∨
      DefectCrossingEntryWithin ring member.2.val member.1
        (word.take W) := by
  rcases grantBlockRenewalFrozenHitClassification
      ring hn hsp member hp W word hhit with hg | hd | hb
  · exact Or.inl hg
  · exact Or.inr (grantBlockFirstDefectFailureCrossing
      ring member.1 member.2.val (word.take W) hd)
  · exact Or.inl (grantBlockFirstBankFailureG18Hit
      ring hn hsp member.2.val hp member.1 W word hb)

/-- A family hit whose members all cross contributes one crossing.

Consumer: `grantBlockFamilyOrG18MassLeCrossing`. -/
private theorem famBlockAnyLe {α : Type}
    (hit : α → Bool) (cr : α → Prop) :
    ∀ xs : List α,
      (∀ x, x ∈ xs → hit x = true → cr x) →
      grantBlockFamilyAny hit xs = true →
      1 ≤ (xs.map (fun x => if cr x then 1 else 0)).sum := by
  intro xs
  induction xs with
  | nil =>
      intro _ hh
      simp [grantBlockFamilyAny] at hh
  | cons x rest ih =>
      intro hcr hh
      simp only [grantBlockFamilyAny, Bool.or_eq_true] at hh
      simp only [List.map_cons, List.sum_cons]
      rcases hh with hx | hr
      · have hc := hcr x List.mem_cons_self hx
        rw [if_pos hc]
        omega
      · have hrest := ih
          (fun y hy hhy => hcr y (List.mem_cons_of_mem x hy) hhy) hr
        omega

/-- A scheduler sum commutes with a finite list sum.

Consumer: `grantBlockFamilyOrG18MassLeCrossing`. -/
private theorem famBlockScheduleSumList {α : Type} (n T : Nat)
    (xs : List α) (f : α → List (Fin n) → Nat) :
    Prob.scheduleSum n T
        (fun w => (xs.map (fun x => f x w)).sum) =
      (xs.map (fun x => Prob.scheduleSum n T (f x))).sum := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact (Density.schedule_sum_const T 0).trans (Nat.mul_zero _)
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (Density.schedule_sum_add T (f x)
        (fun w => (rest.map (fun y => f y w)).sum)).trans
        (congrArg (fun z => Prob.scheduleSum n T (f x) + z) ih)

/-- The family-or-G18 mass is at most the G18 mass plus the crossing masses
of the members.

Consumer: `grantBlockFamilyOrG18CrossingBound`. -/
theorem grantBlockFamilyOrG18MassLeCrossing
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (family : List (GrantBlockFamilyMember ring))
    (hcommon : ∀ member, member ∈ family → member.2.val = C)
    (T W : Nat) :
    grantBlockFamilyFrozenOrG18Mass ring C family T W ≤
      grantBlockSurrogateG18HitMass ring C T W +
        (family.map (fun member =>
          Prob.scheduleSum n T (fun word =>
            if DefectCrossingEntryWithin ring C member.1
                (word.take W) then 1 else 0))).sum := by
  have hpoint : ∀ word : List (Fin n),
      (if (grantBlockFamilyAny
            (fun member => grantBlockFrozenProxyHit
              ring member (word.take W)) family ||
          decide (GrantBlockSurrogateG18HitWithin ring C W word))
          = true then 1 else 0) ≤
      (if GrantBlockSurrogateG18HitWithin ring C W word
        then 1 else 0) +
      (family.map (fun member =>
        if DefectCrossingEntryWithin ring C member.1
            (word.take W) then 1 else 0)).sum := by
    intro word
    by_cases hG : GrantBlockSurrogateG18HitWithin ring C W word
    · have h1 : (grantBlockFamilyAny
            (fun member => grantBlockFrozenProxyHit
              ring member (word.take W)) family ||
          decide (GrantBlockSurrogateG18HitWithin ring C W word))
          = true := by simp [hG]
      rw [if_pos h1, if_pos hG]
      omega
    · by_cases hany : grantBlockFamilyAny
          (fun member => grantBlockFrozenProxyHit
            ring member (word.take W)) family = true
      · have h1 : (grantBlockFamilyAny
              (fun member => grantBlockFrozenProxyHit
                ring member (word.take W)) family ||
            decide (GrantBlockSurrogateG18HitWithin ring C W word))
            = true := by simp [hany]
        have hsum := famBlockAnyLe
          (fun member => grantBlockFrozenProxyHit
            ring member (word.take W))
          (fun member => DefectCrossingEntryWithin ring C member.1
            (word.take W)) family
          (by
            intro member hm hhit
            have hC := hcommon member hm
            have hpm : headlinePurified ring member.2.val := by
              rw [hC]
              exact hp
            rcases grantBlockFrozenHitG18OrCrossing ring hn hsp
                member hpm W word hhit with hg | hc
            · rw [hC] at hg
              exact False.elim (hG hg)
            · rw [hC] at hc
              exact hc) hany
        rw [if_pos h1]
        omega
      · have h1 : ¬ ((grantBlockFamilyAny
              (fun member => grantBlockFrozenProxyHit
                ring member (word.take W)) family ||
            decide (GrantBlockSurrogateG18HitWithin ring C W word))
            = true) := by simp [hany, hG]
        rw [if_neg h1]
        omega
  unfold grantBlockFamilyFrozenOrG18Mass
    grantBlockSurrogateG18HitMass
  calc
    _ ≤ Prob.scheduleSum n T (fun word =>
        (if GrantBlockSurrogateG18HitWithin ring C W word
          then 1 else 0) +
        (family.map (fun member =>
          if DefectCrossingEntryWithin ring C member.1
              (word.take W) then 1 else 0)).sum) :=
      Density.schedule_sum_mono T _ _ hpoint
    _ = _ := by
      rw [Density.schedule_sum_add]
      exact congrArg
        (fun z => Prob.scheduleSum n T (fun word =>
          if GrantBlockSurrogateG18HitWithin ring C W word
            then 1 else 0) + z)
        (famBlockScheduleSumList n T family
          (fun member word =>
            if DefectCrossingEntryWithin ring C member.1
                (word.take W) then 1 else 0))

/-- C.11 pays the summed crossing masses of a buffered family.

Consumer: `grantBlockFamilyOrG18CrossingBound`. -/
theorem grantBlockFamilyCrossingMassBound
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (R T W : Nat) :
    ∀ family : List (GrantBlockFamilyMember ring),
      (∀ member, member ∈ family →
        HeadlineGrantBufferedCounter ring C R member.1) →
      W ≤ T → W ≤ R * n / 8 →
      8 ^ R * (family.map (fun member =>
          Prob.scheduleSum n T (fun word =>
            if DefectCrossingEntryWithin ring C member.1
                (word.take W) then 1 else 0))).sum ≤
        family.length *
          (Density.N (badSet ring C) * 3 ^ R * n ^ T) := by
  intro family
  induction family with
  | nil =>
      intro _ _ _
      simp
  | cons member rest ih =>
      intro hbuf hWT hwin
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.succ_mul]
      have h1 := defectCrossingMass (by omega : 2 ≤ n) ring C
        member.1 R W T (hbuf member List.mem_cons_self) hWT hwin
      have h2 := ih
        (fun x hx => hbuf x (List.mem_cons_of_mem member hx))
        hWT hwin
      omega

/-- The family-or-G18 mass against the G18 mass, with the crossing term in
the scaled form `|family| N 3^R n^T`.

Consumer: `grantBlockFamilyBlockMassLower`. -/
theorem grantBlockFamilyOrG18CrossingBound
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (family : List (GrantBlockFamilyMember ring))
    (hcommon : ∀ member, member ∈ family → member.2.val = C)
    (R T W : Nat)
    (hbuf : ∀ member, member ∈ family →
      HeadlineGrantBufferedCounter ring C R member.1)
    (hWT : W ≤ T) (hwin : W ≤ R * n / 8) :
    8 ^ R * grantBlockFamilyFrozenOrG18Mass ring C family T W ≤
      8 ^ R * grantBlockSurrogateG18HitMass ring C T W +
        family.length *
          (Density.N (badSet ring C) * 3 ^ R * n ^ T) := by
  have hle := grantBlockFamilyOrG18MassLeCrossing ring hn hsp C hp
    family hcommon T W
  have hcross := grantBlockFamilyCrossingMassBound ring hn C R T W
    family hbuf hWT hwin
  calc
    8 ^ R * grantBlockFamilyFrozenOrG18Mass ring C family T W ≤
        8 ^ R * (grantBlockSurrogateG18HitMass ring C T W +
          (family.map (fun member =>
            Prob.scheduleSum n T (fun word =>
              if DefectCrossingEntryWithin ring C member.1
                  (word.take W) then 1 else 0))).sum) :=
      Nat.mul_le_mul_left _ hle
    _ = 8 ^ R * grantBlockSurrogateG18HitMass ring C T W +
        8 ^ R * (family.map (fun member =>
            Prob.scheduleSum n T (fun word =>
              if DefectCrossingEntryWithin ring C member.1
                  (word.take W) then 1 else 0))).sum :=
      Nat.mul_add _ _ _
    _ ≤ _ := Nat.add_le_add_left hcross _

/-! ### Arithmetic over opaque naturals -/

/-- Linear step of the case `min = S E`.

Consumer: `famBlockCoreArith`. -/
private theorem famBlockLinSmallCase (a g c : Nat)
    (h1 : a ≤ 4 * g + 4 * c) (h2 : 8 * c ≤ a) :
    a ≤ 8 * g := by
  omega

/-- Linear step of the case `min = 2 M (E P - 2 S X)`.

Consumer: `famBlockCoreArith`. -/
private theorem famBlockLinLargeCase (m1 m2 m3 g : Nat)
    (h1 : 2 * m1 ≤ 4 * g + 4 * m2) (h2 : m1 + 2 * m2 = m3)
    (h3 : 512 * m2 ≤ m3) :
    127 * m3 ≤ 256 * g := by
  omega

/-- The two ways the C.17 minimum can fall, against the crossing term.

Consumer: `grantBlockFamilyBlockMassLower`. -/
private theorem famBlockCoreArith
    (S E P X M Nt G Or : Nat)
    (hS : 0 < S) (hE : 0 < E)
    (hrate : min (S * E) (2 * (M * (E * P - 2 * S * X))) * Nt ≤
      4 * (S * E) * Or)
    (hcross : E * Or ≤ E * G + M * (X * Nt))
    (s1 : 512 * (S * X) ≤ E * P)
    (s2 : 8 * (M * X) ≤ E) :
    127 * (M * P) * Nt ≤ 256 * (S * G) ∨ Nt ≤ 8 * G := by
  have hscaled := Nat.mul_le_mul_left (4 * S) hcross
  have hrate' : min (S * E) (2 * (M * (E * P - 2 * S * X))) * Nt ≤
      4 * (S * (E * G)) + 4 * (M * (S * X) * Nt) := by
    have hEq : 4 * (S * E) * Or = 4 * S * (E * Or) := by ac_rfl
    have hEq2 : 4 * S * (E * G + M * (X * Nt)) =
        4 * (S * (E * G)) + 4 * (M * (S * X) * Nt) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    calc
      _ ≤ 4 * (S * E) * Or := hrate
      _ = 4 * S * (E * Or) := hEq
      _ ≤ 4 * S * (E * G + M * (X * Nt)) := hscaled
      _ = _ := hEq2
  rcases Nat.le_total (S * E)
      (2 * (M * (E * P - 2 * S * X))) with hcase | hcase
  · right
    rw [Nat.min_eq_left hcase] at hrate'
    have hc : 8 * (M * (S * X) * Nt) ≤ S * E * Nt := by
      have hm := Nat.mul_le_mul_right (S * Nt) s2
      have e1 : 8 * (M * (S * X) * Nt) = 8 * (M * X) * (S * Nt) := by
        ac_rfl
      have e2 : S * E * Nt = E * (S * Nt) := by ac_rfl
      rw [e1, e2]
      exact hm
    have ha := famBlockLinSmallCase (S * E * Nt) (S * (E * G))
      (M * (S * X) * Nt) hrate' hc
    have hpos : 0 < S * E := Nat.mul_pos hS hE
    have e3 : 8 * (S * (E * G)) = S * E * (8 * G) := by ac_rfl
    rw [e3] at ha
    exact Nat.le_of_mul_le_mul_left ha hpos
  · left
    rw [Nat.min_eq_right hcase] at hrate'
    have hq : 2 * S * X ≤ E * P := by
      have e : 2 * S * X = 2 * (S * X) := Nat.mul_assoc _ _ _
      omega
    have hD : (E * P - 2 * S * X) + 2 * (S * X) = E * P := by
      have e : 2 * S * X = 2 * (S * X) := Nat.mul_assoc _ _ _
      rw [← e]
      exact Nat.sub_add_cancel hq
    have hident : M * (E * P - 2 * S * X) * Nt +
        2 * (M * (S * X) * Nt) = M * (E * P) * Nt := by
      have := congrArg (fun z => M * z * Nt) hD
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] at this ⊢
      exact this
    have hbig : 512 * (M * (S * X) * Nt) ≤ M * (E * P) * Nt := by
      have hm := Nat.mul_le_mul_right (M * Nt) s1
      have e1 : 512 * (M * (S * X) * Nt) = 512 * (S * X) * (M * Nt) := by
        ac_rfl
      have e2 : M * (E * P) * Nt = E * P * (M * Nt) := by ac_rfl
      rw [e1, e2]
      exact hm
    have hlin := famBlockLinLargeCase
      (M * (E * P - 2 * S * X) * Nt)
      (M * (S * X) * Nt) (M * (E * P) * Nt) (S * (E * G))
      (by
        have e : 2 * (M * (E * P - 2 * S * X)) * Nt =
            2 * (M * (E * P - 2 * S * X) * Nt) := by ac_rfl
        rw [e] at hrate'
        exact hrate')
      hident hbig
    have e4 : 127 * (M * (E * P) * Nt) = E * (127 * (M * P) * Nt) := by
      ac_rfl
    have e5 : 256 * (S * (E * G)) = E * (256 * (S * G)) := by ac_rfl
    rw [e4, e5] at hlin
    exact Nat.le_of_mul_le_mul_left hlin hE

/-- From the density bound `489 n < 1000 M w` and the first case to the
displayed constants `2/17`.

Consumer: `grantBlockFamilyBlockMassLower`. -/
private theorem famBlockConstantsArith
    (M n w f K2 W Nt G : Nat) (hn : 0 < n)
    (hM : 489 * n < 1000 * M * w)
    (h : 127 * (M * (51279921 * W)) * Nt ≤
      256 * (104857600 * f * n * K2 * G)) :
    2 * W * Nt ≤ 17 * (w * f * K2) * G := by
  have h1 : (127 * 51279921 * W * Nt) * (489 * n) ≤
      (127 * 51279921 * W * Nt) * (1000 * M * w) :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hM)
  have h2 : (127 * 51279921 * W * Nt) * (1000 * M * w) =
      1000 * w * (127 * (M * (51279921 * W)) * Nt) := by ac_rfl
  have h3 : 1000 * w * (127 * (M * (51279921 * W)) * Nt) ≤
      1000 * w * (256 * (104857600 * f * n * K2 * G)) :=
    Nat.mul_le_mul_left _ h
  have h4 : n * (127 * 489 * 51279921 * (W * Nt)) ≤
      n * (1000 * 256 * 104857600 * (w * f * K2 * G)) := by
    have e1 : n * (127 * 489 * 51279921 * (W * Nt)) =
        (127 * 51279921 * W * Nt) * (489 * n) := by ac_rfl
    have e2 : n * (1000 * 256 * 104857600 * (w * f * K2 * G)) =
        1000 * w * (256 * (104857600 * f * n * K2 * G)) := by ac_rfl
    rw [e1, e2]
    exact Nat.le_trans h1 (h2 ▸ h3)
  have h5 := Nat.le_of_mul_le_mul_left h4 hn
  have e6 : 2 * W * Nt = 2 * (W * Nt) := Nat.mul_assoc _ _ _
  have e7 : 17 * (w * f * K2) * G = 17 * (w * f * K2 * G) :=
    Nat.mul_assoc _ _ _
  rw [e6, e7]
  omega

/-- `Y <= 2^R` gives `Y 3^R <= 8^R`.

Consumer: `grantBlockFamilyBlockMassLower`. -/
private theorem famBlockPowSmall (R Y : Nat) (hY : Y ≤ 2 ^ R) :
    Y * 3 ^ R ≤ 8 ^ R :=
  calc
    Y * 3 ^ R ≤ 2 ^ R * 3 ^ R := Nat.mul_le_mul_right _ hY
    _ = (2 * 3) ^ R := (Nat.mul_pow 2 3 R).symm
    _ ≤ 8 ^ R := Nat.pow_le_pow_left (by decide) R

/-- The scale times the defect count is below `2^R`.

Consumer: `grantBlockFamilyBlockMassLower`. -/
private theorem famBlockSmallScale
    (b K R n N : Nat) (hsq : n * n ≤ 2 ^ K) (hN : N ≤ 4 * n)
    (hR : 38 + (8 * b + 13) + K + K ≤ R) :
    512 * (104857600 * (8 * b + 13) * n * 2 ^ K) * N ≤ 2 ^ R := by
  have hf : 8 * b + 13 ≤ 2 ^ (8 * b + 13) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  have hc : 512 * 104857600 * 4 ≤ 2 ^ 38 := by decide
  calc
    512 * (104857600 * (8 * b + 13) * n * 2 ^ K) * N ≤
        512 * (104857600 * (8 * b + 13) * n * 2 ^ K) * (4 * n) :=
      Nat.mul_le_mul_left _ hN
    _ = (512 * 104857600 * 4) * (8 * b + 13) * (n * n) * 2 ^ K := by
      ac_rfl
    _ ≤ 2 ^ 38 * 2 ^ (8 * b + 13) * 2 ^ K * 2 ^ K :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hc hf) hsq) (Nat.le_refl _)
    _ = 2 ^ (38 + (8 * b + 13) + K + K) := by
      rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    _ ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) hR

/-- The family size times the defect count is below `2^R`.

Consumer: `grantBlockFamilyBlockMassLower`. -/
private theorem famBlockSmallRoots
    (K R n : Nat) (hsq : n * n ≤ 2 ^ K) (hR : K + 5 ≤ R) :
    32 * (n * n) ≤ 2 ^ R :=
  calc
    32 * (n * n) ≤ 32 * 2 ^ K := Nat.mul_le_mul_left _ hsq
    _ = 2 ^ (5 + K) := by
      rw [Nat.pow_add]
    _ ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) (by omega)

/-- **C.18--C.19 on the actual family.**  At every density-good,
grant-not-ready, purified entrance, the mass of the G18 first-hit event in
the first `W` letters of a length-`T` scheduler word satisfies

`2 W n^T ≤ 17 (b+2) (8b+13) 2^K * mass`,

that is, the block success probability is at least
`(2/17) W / ((b+2)(8b+13) 2^K)`.

The sparse-defect term is paid by the density bound `defects ≤ 4 n` (through
`defects_eq_N`) and the radius cutoff of `grantCutoffsCompiledRadiusReserves`;
no smallness hypothesis is assumed.  The constant is one half of the paper's
C.19 (`0.2387`) because the Lean C.17 union is `min(N, 2S) ≤ 4U`, not
`1-(1-z)^M`; the proved ratio is `0.1186 ≥ 2/17 = 0.1176`, and `2/17` is the
constant that gives `34 f w V n^2` against the ledger's `34`.

Consumer: `grantBlockEntranceBlockFailure` (the block renewal). -/
theorem grantBlockFamilyBlockMassLower
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (C : HeadlineConfiguration n)
    (hpurified : headlinePurified ring C)
    (hnotready : ¬ headlineGrantReady ring C)
    (hdensity : defects ring C * defects ring C ≤ 4 * n)
    (R L T W : Nat)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T) :
    2 * W * n ^ T ≤
      17 * (((compileAdvice (ceilLogTwo n)).b + 2) *
        (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        2 ^ (compileAdvice (ceilLogTwo n)).K) *
      grantBlockSurrogateG18HitMass ring C T W := by
  obtain ⟨family, _, hmem, hcount, hlen, hrate⟩ :=
    grantBlockFamilyRateOnSelection ring hn hsp hw hlarge C
      hpurified hnotready hdensity R L T W hsize hradius hW hL
      hWT hbudget
  have hcross := grantBlockFamilyOrG18CrossingBound ring hn hsp C
    hpurified family (fun m hm => (hmem m hm).1) R T W
    (fun m hm => (hmem m hm).2) hWT (Nat.le_of_eq hW)
  obtain ⟨hres, _, hRn⟩ :=
    grantCutoffsCompiledRadiusReserves n R hn hsp hradius
  have hsq := grantCutoffsPopulationSquareFitsHeads n hn
  have hn0 : 0 < n := by omega
  have hN : Density.N (badSet ring C) ≤ 4 * n :=
    Nat.le_trans (Nat.le_mul_self (defects ring C)) hdensity
  have hRle : R ≤ n := by
    have h1 : R ≤ 256 * R := by omega
    have h2 : 256 * R ≤ (256 * R) * (256 * R) :=
      Nat.le_mul_self _
    have h3 : (256 * R) ^ 2 = (256 * R) * (256 * R) := Nat.pow_two _
    omega
  have hWpos : 256 ≤ W := by
    rw [hW]
    generalize R * n = z at hRn ⊢
    omega
  have hWle : W ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
    have h1 : W ≤ R * n := by
      rw [hW]
      exact Nat.div_le_self _ _
    have h2 : R * n ≤ n * n := Nat.mul_le_mul_right n hRle
    omega
  -- exponent budget from the radius reserves
  have hexp : 38 + (8 * (compileAdvice (ceilLogTwo n)).b + 13) +
      (compileAdvice (ceilLogTwo n)).K +
      (compileAdvice (ceilLogTwo n)).K ≤ R := by
    have hQ : 32 * ((compileAdvice (ceilLogTwo n)).K + 2) ≤
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hexp2 : (compileAdvice (ceilLogTwo n)).K + 5 ≤ R := by
    omega
  have hSmallScale := famBlockSmallScale
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).K R n
    (Density.N (badSet ring C)) hsq hN hexp
  have hSmallRoots := famBlockSmallRoots
    (compileAdvice (ceilLogTwo n)).K R n hsq hexp2
  -- the two smallness facts s1, s2 of the core arithmetic
  have hE : 0 < 8 ^ R := Nat.pow_pos (by decide : 0 < 8)
  have hS : 0 < grantBlockFamilyScale n := by
    unfold grantBlockFamilyScale
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
      (by omega)) hn0) (Nat.two_pow_pos _)
  have s1 : 512 * (grantBlockFamilyScale n *
      (Density.N (badSet ring C) * 3 ^ R)) ≤
      8 ^ R * (51279921 * W) := by
    have h1 := famBlockPowSmall R _ hSmallScale
    have e : 512 * (grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ R)) =
        512 * (104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)
          * n * 2 ^ (compileAdvice (ceilLogTwo n)).K) *
          Density.N (badSet ring C) * 3 ^ R := by
      unfold grantBlockFamilyScale
      ac_rfl
    rw [e]
    have hP : 8 ^ R ≤ 8 ^ R * (51279921 * W) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact Nat.le_trans h1 hP
  have s2 : 8 * (family.length *
      (Density.N (badSet ring C) * 3 ^ R)) ≤ 8 ^ R := by
    have h1 : 8 * family.length * Density.N (badSet ring C) ≤
        32 * (n * n) := by
      have e1 : 8 * family.length * Density.N (badSet ring C) ≤
          8 * n * (4 * n) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 8 hlen) hN
      have e2 : 8 * n * (4 * n) = 32 * (n * n) := by ac_rfl
      omega
    have h2 := famBlockPowSmall R _ (Nat.le_trans h1 hSmallRoots)
    have e : 8 * (family.length *
        (Density.N (badSet ring C) * 3 ^ R)) =
        8 * family.length * Density.N (badSet ring C) * 3 ^ R := by
      ac_rfl
    rw [e]
    exact h2
  -- the core arithmetic
  unfold grantBlockFrozenDirectRateNumerator
    grantBlockFrozenDirectRateDenominator at hrate
  have hcore := famBlockCoreArith (grantBlockFamilyScale n) (8 ^ R)
    (51279921 * W) (Density.N (badSet ring C) * 3 ^ R)
    family.length (n ^ T) (grantBlockSurrogateG18HitMass ring C T W)
    (grantBlockFamilyFrozenOrG18Mass ring C family T W)
    hS hE hrate hcross s1 s2
  rcases hcore with hA | hB
  · apply famBlockConstantsArith family.length n
      ((compileAdvice (ceilLogTwo n)).b + 2)
      (8 * (compileAdvice (ceilLogTwo n)).b + 13)
      (2 ^ (compileAdvice (ceilLogTwo n)).K) W (n ^ T)
      (grantBlockSurrogateG18HitMass ring C T W) hn0
    · exact hcount
    · unfold grantBlockFamilyScale at hA
      exact hA
  · have hwf : 1 ≤ ((compileAdvice (ceilLogTwo n)).b + 2) *
        (8 * (compileAdvice (ceilLogTwo n)).b + 13) :=
      Nat.mul_pos (by omega) (by omega)
    have h1 : 2 * W * n ^ T ≤ 2 * W * (8 * grantBlockSurrogateG18HitMass
        ring C T W) := Nat.mul_le_mul_left _ hB
    have h2 : 16 * W ≤ 17 * (((compileAdvice (ceilLogTwo n)).b + 2) *
        (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        2 ^ (compileAdvice (ceilLogTwo n)).K) := by
      have h3 : 1 * 2 ^ (compileAdvice (ceilLogTwo n)).K ≤
          ((compileAdvice (ceilLogTwo n)).b + 2) *
            (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
            2 ^ (compileAdvice (ceilLogTwo n)).K :=
        Nat.mul_le_mul_right _ hwf
      omega
    calc
      2 * W * n ^ T ≤ 2 * W *
          (8 * grantBlockSurrogateG18HitMass ring C T W) := h1
      _ = (2 * 8) * (W * grantBlockSurrogateG18HitMass ring C T W) := by
          ac_rfl
      _ = (16 * W) * grantBlockSurrogateG18HitMass ring C T W :=
          (Nat.mul_assoc 16 W _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ h2

end L3

#print axioms L3.grantBlockFirstBankFailureG18Hit
#print axioms L3.grantBlockFrozenHitG18OrCrossing
#print axioms L3.grantBlockFamilyOrG18MassLeCrossing
#print axioms L3.grantBlockFamilyCrossingMassBound
#print axioms L3.grantBlockFamilyOrG18CrossingBound
#print axioms L3.grantBlockFamilyBlockMassLower
