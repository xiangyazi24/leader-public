import Leader.L3.Grant.BlockPrefixNegCorr

/-!
G16 C.17: prefix-only negative correlation, on one IID Fin n
scheduler. The proof is a first-letter induction on two local
histories. The three masked categories are a finite-sum identity,
not an independence hypothesis or a shuffle assumption.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The third of three disjoint categories of scheduler letters. -/
def grantBlockPairOtherSupport
    {n : Nat} (s t : Fin n → Bool) (e : Fin n) : Bool :=
  !(s e || t e)

/-- A masked Fin n sum, always over the *original* scheduler. -/
def grantBlockPairMaskedSum
    {n : Nat} (mask : Fin n → Bool) (f : Fin n → Nat) : Nat :=
  (List.ofFn (fun e : Fin n => if mask e then f e else 0)).sum

/-- Arbitrary finite sum is partitioned into s, t and the
complementary third category; disjointness is the sole input. -/
theorem grantBlockPairMaskedPartition
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (f : Fin n → Nat) :
    (List.ofFn f).sum =
      grantBlockPairMaskedSum s f +
        (grantBlockPairMaskedSum t f +
         grantBlockPairMaskedSum
           (grantBlockPairOtherSupport s t) f) := by
  change (List.ofFn f).sum =
    (List.ofFn (fun e : Fin n =>
      if s e then f e else 0)).sum +
    ((List.ofFn (fun e : Fin n =>
      if t e then f e else 0)).sum +
     (List.ofFn (fun e : Fin n =>
       if grantBlockPairOtherSupport s t e
       then f e else 0)).sum)
  calc
    (List.ofFn f).sum =
      (List.ofFn (fun e : Fin n =>
        (if s e then f e else 0) +
          ((if t e then f e else 0) +
           (if grantBlockPairOtherSupport s t e
            then f e else 0)))).sum := by
          apply ofFn_sum_eq
          intro e
          cases hs : s e with
          | false =>
              cases ht : t e <;>
                simp [grantBlockPairOtherSupport, hs, ht]
          | true =>
              have ht : t e = false := by
                cases he : t e with
                | false => rfl
                | true =>
                    exact False.elim (hdisjoint e ⟨hs, he⟩)
              simp [grantBlockPairOtherSupport, hs, ht]
    _ = _ := by
      rw [ofFn_sum_add, ofFn_sum_add]

/-- Mask replacement requires equality only on the active
category, not on the unused Agent alphabet. -/
theorem grantBlockPairMaskedCongr
    {n : Nat} (mask : Fin n → Bool)
    (f g : Fin n → Nat)
    (h : ∀ e : Fin n, mask e = true → f e = g e) :
    grantBlockPairMaskedSum mask f =
      grantBlockPairMaskedSum mask g := by
  unfold grantBlockPairMaskedSum
  apply ofFn_sum_eq
  intro e
  cases hm : mask e with
  | false => simp [hm]
  | true => simp [hm, h e hm]

/-- Masked constant factors out; this is the only scalar
summation rule needed for all three categories. -/
theorem grantBlockPairMaskedConstant
    {n : Nat} (mask : Fin n → Bool)
    (K : Nat) :
    grantBlockPairMaskedSum mask (fun _ => K) =
      K * grantBlockPairMaskedSum mask (fun _ => 1) := by
  unfold grantBlockPairMaskedSum
  calc
    (List.ofFn (fun e : Fin n =>
      if mask e then K else 0)).sum =
      (List.ofFn (fun e : Fin n =>
        K * (if mask e then 1 else 0))).sum := by
          apply ofFn_sum_eq
          intro e
          cases hm : mask e <;> simp [hm]
    _ = _ := ofFn_sum_mul_left K _

/-- A scalar can be pulled out of an arbitrary masked sum. -/
theorem grantBlockPairMaskedMulRight
    {n : Nat} (mask : Fin n → Bool)
    (f : Fin n → Nat) (K : Nat) :
    grantBlockPairMaskedSum mask (fun e => f e * K) =
      grantBlockPairMaskedSum mask f * K := by
  unfold grantBlockPairMaskedSum
  calc
    (List.ofFn (fun e : Fin n =>
      if mask e then f e * K else 0)).sum =
      (List.ofFn (fun e : Fin n =>
        K * (if mask e then f e else 0))).sum := by
          apply ofFn_sum_eq
          intro e
          cases hm : mask e <;> simp [hm, Nat.mul_comm]
    _ = K * (List.ofFn (fun e : Fin n =>
        if mask e then f e else 0)).sum :=
      ofFn_sum_mul_left K _
    _ = _ := Nat.mul_comm _ _

def grantBlockPairCategorySize
    {n : Nat} (mask : Fin n → Bool) : Nat :=
  grantBlockPairMaskedSum mask (fun _ => 1)

/-- Count all scheduler letters once, by their three categories. -/
theorem grantBlockPairCategoryCount
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true)) :
    grantBlockPairCategorySize s +
      (grantBlockPairCategorySize t +
       grantBlockPairCategorySize
         (grantBlockPairOtherSupport s t)) = n := by
  have h := grantBlockPairMaskedPartition s t hdisjoint
    (fun _ : Fin n => (1 : Nat))
  change (List.ofFn (fun _ : Fin n => (1 : Nat))).sum =
    grantBlockPairCategorySize s +
      (grantBlockPairCategorySize t +
       grantBlockPairCategorySize
         (grantBlockPairOtherSupport s t)) at h
  simp only [ofFn_sum_const, Nat.mul_one] at h
  exact h.symm

/-- Disjointness makes every t-letter an s-outside letter. -/
theorem grantBlockPairOutsideLeft
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (e : Fin n) (ht : t e = true) :
    s e = false := by
  cases hs : s e with
  | false => rfl
  | true => exact False.elim (hdisjoint e ⟨hs, ht⟩)

/-- And every s-letter is t-outside. -/
theorem grantBlockPairOutsideRight
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (e : Fin n) (hs : s e = true) :
    t e = false := by
  cases ht : t e with
  | false => rfl
  | true => exact False.elim (hdisjoint e ⟨hs, ht⟩)

theorem grantBlockPairOtherOutsideLeft
    {n : Nat} (s t : Fin n → Bool)
    (e : Fin n)
    (ho : grantBlockPairOtherSupport s t e = true) :
    s e = false := by
  cases hs : s e with
  | false => rfl
  | true =>
      have hh : grantBlockPairOtherSupport s t e = false := by
        simp [grantBlockPairOtherSupport, hs]
      rw [hh] at ho
      cases ho

theorem grantBlockPairOtherOutsideRight
    {n : Nat} (s t : Fin n → Bool)
    (e : Fin n)
    (ho : grantBlockPairOtherSupport s t e = true) :
    t e = false := by
  cases ht : t e with
  | false => rfl
  | true =>
      have hh : grantBlockPairOtherSupport s t e = false := by
        simp [grantBlockPairOtherSupport, ht]
      rw [hh] at ho
      cases ho

/-- First marginal category sum, with s-absent values constant. -/
theorem grantBlockPairCategorySumLeft
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (A : Fin n → Nat) (A0 : Nat)
    (hA : ∀ e : Fin n, s e = false → A e = A0) :
    (List.ofFn A).sum =
      grantBlockPairMaskedSum s A +
        (grantBlockPairCategorySize t +
         grantBlockPairCategorySize
           (grantBlockPairOtherSupport s t)) * A0 := by
  have hpart := grantBlockPairMaskedPartition s t hdisjoint A
  have ht :
      grantBlockPairMaskedSum t A =
        grantBlockPairCategorySize t * A0 := by
    calc
      grantBlockPairMaskedSum t A =
        grantBlockPairMaskedSum t (fun _ => A0) := by
          apply grantBlockPairMaskedCongr
          intro e he
          exact hA e (grantBlockPairOutsideLeft s t hdisjoint e he)
      _ = A0 * grantBlockPairCategorySize t :=
        grantBlockPairMaskedConstant t A0
      _ = _ := Nat.mul_comm _ _
  have ho :
      grantBlockPairMaskedSum
        (grantBlockPairOtherSupport s t) A =
        grantBlockPairCategorySize
          (grantBlockPairOtherSupport s t) * A0 := by
    calc
      grantBlockPairMaskedSum
          (grantBlockPairOtherSupport s t) A =
        grantBlockPairMaskedSum
          (grantBlockPairOtherSupport s t) (fun _ => A0) := by
            apply grantBlockPairMaskedCongr
            intro e he
            exact hA e (grantBlockPairOtherOutsideLeft s t e he)
      _ = A0 *
          grantBlockPairCategorySize
            (grantBlockPairOtherSupport s t) :=
        grantBlockPairMaskedConstant _ A0
      _ = _ := Nat.mul_comm _ _
  rw [ht, ho] at hpart
  calc
    (List.ofFn A).sum =
      grantBlockPairMaskedSum s A +
        (grantBlockPairCategorySize t * A0 +
         grantBlockPairCategorySize
           (grantBlockPairOtherSupport s t) * A0) := hpart
    _ = _ := by rw [Nat.add_mul]

/-- Second marginal, symmetric with the first. -/
theorem grantBlockPairCategorySumRight
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (B : Fin n → Nat) (B0 : Nat)
    (hB : ∀ e : Fin n, t e = false → B e = B0) :
    (List.ofFn B).sum =
      grantBlockPairMaskedSum t B +
        (grantBlockPairCategorySize s +
         grantBlockPairCategorySize
           (grantBlockPairOtherSupport s t)) * B0 := by
  have hpart := grantBlockPairMaskedPartition s t hdisjoint B
  have hs :
      grantBlockPairMaskedSum s B =
        grantBlockPairCategorySize s * B0 := by
    calc
      grantBlockPairMaskedSum s B =
        grantBlockPairMaskedSum s (fun _ => B0) := by
          apply grantBlockPairMaskedCongr
          intro e he
          exact hB e (grantBlockPairOutsideRight s t hdisjoint e he)
      _ = B0 * grantBlockPairCategorySize s :=
        grantBlockPairMaskedConstant s B0
      _ = _ := Nat.mul_comm _ _
  have ho :
      grantBlockPairMaskedSum
        (grantBlockPairOtherSupport s t) B =
        grantBlockPairCategorySize
          (grantBlockPairOtherSupport s t) * B0 := by
    calc
      grantBlockPairMaskedSum
          (grantBlockPairOtherSupport s t) B =
        grantBlockPairMaskedSum
          (grantBlockPairOtherSupport s t) (fun _ => B0) := by
            apply grantBlockPairMaskedCongr
            intro e he
            exact hB e (grantBlockPairOtherOutsideRight s t e he)
      _ = B0 * grantBlockPairCategorySize
          (grantBlockPairOtherSupport s t) :=
        grantBlockPairMaskedConstant _ B0
      _ = _ := Nat.mul_comm _ _
  rw [hs, ho] at hpart
  calc
    (List.ofFn B).sum =
      grantBlockPairCategorySize s * B0 +
        (grantBlockPairMaskedSum t B +
          grantBlockPairCategorySize
            (grantBlockPairOtherSupport s t) * B0) := hpart
    _ = grantBlockPairMaskedSum t B +
        (grantBlockPairCategorySize s +
         grantBlockPairCategorySize
           (grantBlockPairOtherSupport s t)) * B0 := by
          rw [Nat.add_mul]
          omega


/-- Third identity: the three-category numerator of pair
intersection is determined by only the s- and t-masked sums. -/
theorem grantBlockPairCategorySumProduct
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (A B : Fin n → Nat) (A0 B0 : Nat)
    (hA : ∀ e : Fin n, s e = false → A e = A0)
    (hB : ∀ e : Fin n, t e = false → B e = B0) :
    (List.ofFn (fun e : Fin n => A e * B e)).sum =
      grantBlockPairMaskedSum s A * B0 +
      grantBlockPairMaskedSum t B * A0 +
      grantBlockPairCategorySize
        (grantBlockPairOtherSupport s t) * A0 * B0 := by
  have hpart := grantBlockPairMaskedPartition s t hdisjoint
    (fun e : Fin n => A e * B e)
  have hs :
      grantBlockPairMaskedSum s (fun e => A e * B e) =
        grantBlockPairMaskedSum s A * B0 := by
    calc
      grantBlockPairMaskedSum s (fun e => A e * B e) =
        grantBlockPairMaskedSum s (fun e => A e * B0) := by
          apply grantBlockPairMaskedCongr
          intro e he
          rw [hB e (grantBlockPairOutsideRight s t hdisjoint e he)]
      _ = _ := grantBlockPairMaskedMulRight s A B0
  have ht :
      grantBlockPairMaskedSum t (fun e => A e * B e) =
        grantBlockPairMaskedSum t B * A0 := by
    calc
      grantBlockPairMaskedSum t (fun e => A e * B e) =
        grantBlockPairMaskedSum t (fun e => B e * A0) := by
          apply grantBlockPairMaskedCongr
          intro e he
          rw [hA e (grantBlockPairOutsideLeft s t hdisjoint e he)]
          exact Nat.mul_comm _ _
      _ = _ := grantBlockPairMaskedMulRight t B A0
  have ho :
      grantBlockPairMaskedSum
        (grantBlockPairOtherSupport s t)
          (fun e => A e * B e) =
        grantBlockPairCategorySize
          (grantBlockPairOtherSupport s t) * A0 * B0 := by
    calc
      grantBlockPairMaskedSum
          (grantBlockPairOtherSupport s t)
          (fun e => A e * B e) =
        grantBlockPairMaskedSum
          (grantBlockPairOtherSupport s t)
          (fun _ => A0 * B0) := by
          apply grantBlockPairMaskedCongr
          intro e he
          rw [hA e (grantBlockPairOtherOutsideLeft s t e he),
            hB e (grantBlockPairOtherOutsideRight s t e he)]
      _ = (A0 * B0) *
          grantBlockPairCategorySize
            (grantBlockPairOtherSupport s t) :=
        grantBlockPairMaskedConstant _ _
      _ = _ := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hs, ht, ho] at hpart
  simpa only [Nat.add_assoc] using hpart

/-- Public restatement of the opaque-Nat arithmetic bridge. -/
theorem grantBlockPairCovarianceArithmetic
    (n A0 B0 gainA gainB : Nat) :
    n * (n * A0 * B0 + gainA * B0 + gainB * A0) ≤
      (n * A0 + gainA) * (n * B0 + gainB) := by
  have heq :
      (n * A0 + gainA) * (n * B0 + gainB) =
        n * (n * A0 * B0 + gainA * B0 + gainB * A0) +
          gainA * gainB := by
    simp only [Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [heq]
  exact Nat.le_add_right _ _

/-- Public restatement of the earlier three-category covariance,
with the supported and unsupported counts still opaque. -/
theorem grantBlockPairThreeCategoryCovariance
    (sizeS sizeT sizeOther A0 B0 gainS gainT : Nat) :
    (sizeS + sizeT + sizeOther) *
      ((sizeS * A0 + gainS) * B0 +
       (sizeT * B0 + gainT) * A0 +
       sizeOther * A0 * B0) ≤
    ((sizeS * A0 + gainS) +
      (sizeT + sizeOther) * A0) *
    ((sizeT * B0 + gainT) +
      (sizeS + sizeOther) * B0) := by
  have heq :
    ((sizeS * A0 + gainS) +
        (sizeT + sizeOther) * A0) *
      ((sizeT * B0 + gainT) +
        (sizeS + sizeOther) * B0) =
    (sizeS + sizeT + sizeOther) *
      ((sizeS * A0 + gainS) * B0 +
       (sizeT * B0 + gainT) * A0 +
       sizeOther * A0 * B0) +
    gainS * gainT := by
    simp only [Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [heq]
  exact Nat.le_add_right _ _

/-- The exact covariance inequality for one fixed first-letter
array. The hypotheses say each observable is unchanged outside
its own support and the supported-letter *average*, not each
individual supported letter, is nondecreasing. -/
theorem grantBlockPairMaskedCovariance
    {n : Nat} (s t : Fin n → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (A B : Fin n → Nat) (A0 B0 : Nat)
    (hA : ∀ e : Fin n, s e = false → A e = A0)
    (hB : ∀ e : Fin n, t e = false → B e = B0)
    (hGainA :
      grantBlockPairCategorySize s * A0 ≤
        grantBlockPairMaskedSum s A)
    (hGainB :
      grantBlockPairCategorySize t * B0 ≤
        grantBlockPairMaskedSum t B) :
    n * (List.ofFn (fun e : Fin n => A e * B e)).sum ≤
      (List.ofFn A).sum * (List.ofFn B).sum := by
  have hcount := grantBlockPairCategoryCount s t hdisjoint
  have hfirst := grantBlockPairCategorySumLeft s t hdisjoint
    A A0 hA
  have hsecond := grantBlockPairCategorySumRight s t hdisjoint
    B B0 hB
  have hpair := grantBlockPairCategorySumProduct s t
    hdisjoint A B A0 B0 hA hB
  have hS :
      grantBlockPairCategorySize s * A0 +
        (grantBlockPairMaskedSum s A -
          grantBlockPairCategorySize s * A0) =
      grantBlockPairMaskedSum s A :=
    Nat.add_sub_of_le hGainA
  have hT :
      grantBlockPairCategorySize t * B0 +
        (grantBlockPairMaskedSum t B -
          grantBlockPairCategorySize t * B0) =
      grantBlockPairMaskedSum t B :=
    Nat.add_sub_of_le hGainB
  have hthree := grantBlockPairThreeCategoryCovariance
    (grantBlockPairCategorySize s)
    (grantBlockPairCategorySize t)
    (grantBlockPairCategorySize
      (grantBlockPairOtherSupport s t))
    A0 B0
    (grantBlockPairMaskedSum s A -
      grantBlockPairCategorySize s * A0)
    (grantBlockPairMaskedSum t B -
      grantBlockPairCategorySize t * B0)
  calc
    n * (List.ofFn (fun e : Fin n => A e * B e)).sum =
      (grantBlockPairCategorySize s +
        grantBlockPairCategorySize t +
        grantBlockPairCategorySize
          (grantBlockPairOtherSupport s t)) *
      ((grantBlockPairCategorySize s * A0 +
          (grantBlockPairMaskedSum s A -
            grantBlockPairCategorySize s * A0)) * B0 +
       (grantBlockPairCategorySize t * B0 +
          (grantBlockPairMaskedSum t B -
            grantBlockPairCategorySize t * B0)) * A0 +
       grantBlockPairCategorySize
          (grantBlockPairOtherSupport s t) * A0 * B0) := by
            rw [hS, hT, hpair]
            exact congrArg (fun m : Nat => m *
              (grantBlockPairMaskedSum s A * B0 +
                grantBlockPairMaskedSum t B * A0 +
                grantBlockPairCategorySize
                  (grantBlockPairOtherSupport s t) * A0 * B0))
              ((Nat.add_assoc _ _ _).trans hcount).symm
    _ ≤
      ((grantBlockPairCategorySize s * A0 +
          (grantBlockPairMaskedSum s A -
            grantBlockPairCategorySize s * A0)) +
        (grantBlockPairCategorySize t +
          grantBlockPairCategorySize
            (grantBlockPairOtherSupport s t)) * A0) *
      ((grantBlockPairCategorySize t * B0 +
          (grantBlockPairMaskedSum t B -
            grantBlockPairCategorySize t * B0)) +
        (grantBlockPairCategorySize s +
          grantBlockPairCategorySize
            (grantBlockPairOtherSupport s t)) * B0) :=
        hthree
    _ = (List.ofFn A).sum * (List.ofFn B).sum := by
      rw [hS, hT, hfirst, hsecond]


/-- Local mass after processing the first global scheduler letter. -/
noncomputable def grantBlockPairFirstLeft
    {n : Nat} (s : Fin n → Bool)
    (a : List (Fin n) → Bool)
    (left : List (Fin n)) (T : Nat) (e : Fin n) : Nat :=
  grantBlockPrefixHistoryMass s a
    (left ++ (if s e then [e] else [])) T

noncomputable def grantBlockPairFirstRight
    {n : Nat} (t : Fin n → Bool)
    (b : List (Fin n) → Bool)
    (right : List (Fin n)) (T : Nat) (e : Fin n) : Nat :=
  grantBlockPrefixHistoryMass t b
    (right ++ (if t e then [e] else [])) T

/-- The average-gain inequality is precisely the category gain
hypothesis for the left first-letter array. -/
theorem grantBlockPairFirstLeftGain
    {n : Nat} (s : Fin n → Bool)
    (a : List (Fin n) → Bool)
    (ha : GrantBlockPrefixMonotone a)
    (left : List (Fin n)) (T : Nat) :
    grantBlockPairCategorySize s *
      grantBlockPrefixHistoryMass s a left T ≤
    grantBlockPairMaskedSum s
      (grantBlockPairFirstLeft s a left T) := by
  have hg := (grantBlockPrefixAggregateGainProved s a ha) left T
  change
    grantBlockPairCategorySize s *
      grantBlockPrefixHistoryMass s a left T ≤
    (List.ofFn (fun e : Fin n =>
      if s e then
        grantBlockPrefixHistoryMass s a (left ++ [e]) T
      else 0)).sum at hg
  have heq :
      grantBlockPairMaskedSum s
        (grantBlockPairFirstLeft s a left T) =
      (List.ofFn (fun e : Fin n =>
        if s e then
          grantBlockPrefixHistoryMass s a (left ++ [e]) T
        else 0)).sum := by
    unfold grantBlockPairMaskedSum
    apply ofFn_sum_eq
    intro e
    cases hs : s e <;>
      simp [grantBlockPairFirstLeft, hs]
  rw [← heq] at hg
  exact hg

theorem grantBlockPairFirstRightGain
    {n : Nat} (t : Fin n → Bool)
    (b : List (Fin n) → Bool)
    (hb : GrantBlockPrefixMonotone b)
    (right : List (Fin n)) (T : Nat) :
    grantBlockPairCategorySize t *
      grantBlockPrefixHistoryMass t b right T ≤
    grantBlockPairMaskedSum t
      (grantBlockPairFirstRight t b right T) := by
  have hg := (grantBlockPrefixAggregateGainProved t b hb) right T
  change
    grantBlockPairCategorySize t *
      grantBlockPrefixHistoryMass t b right T ≤
    (List.ofFn (fun e : Fin n =>
      if t e then
        grantBlockPrefixHistoryMass t b (right ++ [e]) T
      else 0)).sum at hg
  have heq :
      grantBlockPairMaskedSum t
        (grantBlockPairFirstRight t b right T) =
      (List.ofFn (fun e : Fin n =>
        if t e then
          grantBlockPrefixHistoryMass t b (right ++ [e]) T
        else 0)).sum := by
    unfold grantBlockPairMaskedSum
    apply ofFn_sum_eq
    intro e
    cases ht : t e <;>
      simp [grantBlockPairFirstRight, ht]
  rw [← heq] at hg
  exact hg

/-- Prefix-only negative correlation, now with arbitrary local
histories and ONE global scheduler. No support-letter insertion
monotonicity, product scheduler, or shuffle identity is assumed. -/
theorem grantBlockPrefixHistoryPairNegCorr
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (ha : GrantBlockPrefixMonotone a)
    (hb : GrantBlockPrefixMonotone b) :
    ∀ T : Nat, ∀ left right : List (Fin n),
      grantBlockPrefixHistoryPairMass
        s t a b left right T * n ^ T ≤
      grantBlockPrefixHistoryMass s a left T *
        grantBlockPrefixHistoryMass t b right T := by
  intro T
  induction T with
  | zero =>
      intro left right
      simp [grantBlockPrefixHistoryPairMass,
        grantBlockPrefixHistoryMass, Prob.scheduleSum,
        FixedSpanRenewalPayload.wordSum,
        allSchedules, grantBlockSupportSubword]
      cases hx : a left <;> cases hy : b right <;>
        simp [hx, hy]
  | succ T ih =>
      intro left right
      have hsum :
          (List.ofFn (fun e : Fin n =>
            grantBlockPrefixHistoryPairMass s t a b
              (left ++ (if s e then [e] else []))
              (right ++ (if t e then [e] else [])) T)).sum *
            n ^ T ≤
          (List.ofFn (fun e : Fin n =>
            grantBlockPairFirstLeft s a left T e *
              grantBlockPairFirstRight t b right T e)).sum := by
        calc
          (List.ofFn (fun e : Fin n =>
              grantBlockPrefixHistoryPairMass s t a b
                (left ++ (if s e then [e] else []))
                (right ++ (if t e then [e] else [])) T)).sum *
              n ^ T =
          (List.ofFn (fun e : Fin n =>
              n ^ T *
                grantBlockPrefixHistoryPairMass s t a b
                  (left ++ (if s e then [e] else []))
                  (right ++ (if t e then [e] else [])) T)).sum := by
                rw [Nat.mul_comm
                  (List.ofFn (fun e : Fin n =>
                    grantBlockPrefixHistoryPairMass s t a b
                      (left ++ (if s e then [e] else []))
                      (right ++ (if t e then [e] else [])) T)).sum
                  (n ^ T)]
                exact (ofFn_sum_mul_left (n ^ T) _).symm
          _ ≤ _ := by
            apply ofFn_sum_le
            intro e
            rw [Nat.mul_comm (n ^ T)
              (grantBlockPrefixHistoryPairMass s t a b
                (left ++ (if s e then [e] else []))
                (right ++ (if t e then [e] else [])) T)]
            exact ih
              (left ++ (if s e then [e] else []))
              (right ++ (if t e then [e] else []))
      have hcov :
          n *
            (List.ofFn (fun e : Fin n =>
              grantBlockPairFirstLeft s a left T e *
                grantBlockPairFirstRight t b right T e)).sum ≤
          (List.ofFn (grantBlockPairFirstLeft s a left T)).sum *
            (List.ofFn (grantBlockPairFirstRight t b right T)).sum := by
        apply grantBlockPairMaskedCovariance s t hdisjoint
          (grantBlockPairFirstLeft s a left T)
          (grantBlockPairFirstRight t b right T)
          (grantBlockPrefixHistoryMass s a left T)
          (grantBlockPrefixHistoryMass t b right T)
        · intro e he
          simp [grantBlockPairFirstLeft, he]
        · intro e he
          simp [grantBlockPairFirstRight, he]
        · exact grantBlockPairFirstLeftGain s a ha left T
        · exact grantBlockPairFirstRightGain t b hb right T
      calc
        grantBlockPrefixHistoryPairMass
            s t a b left right (T + 1) * n ^ (T + 1) =
          n * ((List.ofFn (fun e : Fin n =>
            grantBlockPrefixHistoryPairMass s t a b
              (left ++ (if s e then [e] else []))
              (right ++ (if t e then [e] else [])) T)).sum *
            n ^ T) := by
              rw [grantBlockPrefixHistoryPairMassSucc,
                Nat.pow_succ]
              simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ n *
            (List.ofFn (fun e : Fin n =>
              grantBlockPairFirstLeft s a left T e *
                grantBlockPairFirstRight t b right T e)).sum :=
          Nat.mul_le_mul_left n hsum
        _ ≤
          (List.ofFn (grantBlockPairFirstLeft s a left T)).sum *
            (List.ofFn (grantBlockPairFirstRight t b right T)).sum :=
          hcov
        _ = grantBlockPrefixHistoryMass s a left (T + 1) *
            grantBlockPrefixHistoryMass t b right (T + 1) := by
          rw [grantBlockPrefixHistoryMassSucc,
            grantBlockPrefixHistoryMassSucc]
          rfl

/-- Unconditional prefix-event version of the original
grantBlockPairNegativeCorrelation, with its exact mass shape. -/
theorem grantBlockPairNegativeCorrelationOfPrefix
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (ha : GrantBlockPrefixMonotone a)
    (hb : GrantBlockPrefixMonotone b)
    (T : Nat) :
    grantBlockLocalPairMass s t a b T * n ^ T ≤
      grantBlockLocalMass s a T *
        grantBlockLocalMass t b T := by
  have hh := grantBlockPrefixHistoryPairNegCorr
    s t a b hdisjoint ha hb T [] []
  rw [grantBlockPrefixHistoryPairMassEmpty,
    grantBlockPrefixHistoryMassEmpty,
    grantBlockPrefixHistoryMassEmpty] at hh
  exact hh

/-- Word-level specialization under actual support-subword
locality; no normalization of the full physical Agent history. -/
theorem grantBlockPairNegativeCorrelationOfLocalWords
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (ha : GrantBlockPrefixMonotone a)
    (hb : GrantBlockPrefixMonotone b)
    (hlocalA : ∀ w, a (grantBlockSupportSubword s w) = a w)
    (hlocalB : ∀ w, b (grantBlockSupportSubword t w) = b w)
    (T : Nat) :
    grantBlockEventIntersection n T
      (fun side : Bool => if side then a else b) true false *
      n ^ T ≤
    grantBlockEventMass n T
      (fun side : Bool => if side then a else b) true *
    grantBlockEventMass n T
      (fun side : Bool => if side then a else b) false := by
  have hp := grantBlockPairNegativeCorrelationOfPrefix
    s t a b hdisjoint ha hb T
  unfold grantBlockEventIntersection grantBlockEventMass
  change
    Prob.scheduleSum n T (fun w =>
      if a w && b w then 1 else 0) * n ^ T ≤
    Prob.scheduleSum n T (fun w => if a w then 1 else 0) *
      Prob.scheduleSum n T (fun w => if b w then 1 else 0)
  change
    Prob.scheduleSum n T (fun w =>
      if grantBlockLocalHit s a w &&
         grantBlockLocalHit t b w then 1 else 0) * n ^ T ≤
    Prob.scheduleSum n T (fun w =>
      if grantBlockLocalHit s a w then 1 else 0) *
    Prob.scheduleSum n T (fun w =>
      if grantBlockLocalHit t b w then 1 else 0) at hp
  have hA :
      (fun w : List (Fin n) =>
        if grantBlockLocalHit s a w then 1 else 0) =
      (fun w : List (Fin n) => if a w then 1 else 0) := by
    funext w
    simp only [grantBlockLocalHit, hlocalA w]
  have hB :
      (fun w : List (Fin n) =>
        if grantBlockLocalHit t b w then 1 else 0) =
      (fun w : List (Fin n) => if b w then 1 else 0) := by
    funext w
    simp only [grantBlockLocalHit, hlocalB w]
  have hAB :
      (fun w : List (Fin n) =>
        if grantBlockLocalHit s a w &&
          grantBlockLocalHit t b w then 1 else 0) =
      (fun w : List (Fin n) => if a w && b w then 1 else 0) := by
    funext w
    simp only [grantBlockLocalHit, hlocalA w, hlocalB w]
  rw [hA, hB, hAB] at hp
  exact hp


/-- A raw finite scheduler word of horizon T contains exactly
T letters, so a prefix-W event has n^(T-W) extensions.
This proof does NOT claim that a prefix-W event is support-local
on the full T-word. -/
private theorem grantBlockPairScheduleZero
    (n : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n 0 f = f [] := by
  simp [Prob.scheduleSum,
    FixedSpanRenewalPayload.wordSum, allSchedules]

private theorem grantBlockPairScheduleConst
    (n T K : Nat) :
    Prob.scheduleSum n T (fun _ : List (Fin n) => K) =
      n ^ T * K := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun _ : List (Fin n) => K) = n ^ T * K
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  simp only [ofFn_sum_const]

private theorem grantBlockPairScheduleSucc
    (n T : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n T (fun w => f (e :: w)))).sum := by
  change FixedSpanRenewalPayload.wordSum n (T + 1) f = _
  rw [FixedSpanRenewalPayload.wordSum_succ]

/-- One original-scheduler prefix-count identity, derived
by W induction and the merged wordSum_succ equation. -/
theorem grantBlockPairScheduleTakeMass
    {n : Nat} :
    ∀ (W extra : Nat) (f : List (Fin n) → Nat),
      Prob.scheduleSum n (W + extra)
        (fun word => f (word.take W)) =
      n ^ extra * Prob.scheduleSum n W f := by
  intro W
  induction W with
  | zero =>
      intro extra f
      simp only [Nat.zero_add, List.take_zero]
      rw [grantBlockPairScheduleZero]
      exact grantBlockPairScheduleConst n extra (f [])
  | succ W ih =>
      intro extra f
      have htotal : W + 1 + extra = (W + extra) + 1 := by omega
      calc
        Prob.scheduleSum n (W + 1 + extra)
          (fun word => f (word.take (W + 1))) =
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n (W + extra)
            (fun word => f (e :: word.take W)))).sum := by
              rw [htotal, grantBlockPairScheduleSucc]
              apply ofFn_sum_eq
              intro e
              apply congrArg (Prob.scheduleSum n (W + extra))
              funext word
              rfl
        _ = (List.ofFn (fun e : Fin n =>
              n ^ extra *
                Prob.scheduleSum n W (fun word => f (e :: word)))).sum := by
              apply ofFn_sum_eq
              intro e
              exact ih extra (fun word => f (e :: word))
        _ = n ^ extra *
            (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n W (fun word => f (e :: word)))).sum :=
            ofFn_sum_mul_left (n ^ extra)
              (fun e : Fin n =>
                Prob.scheduleSum n W (fun word => f (e :: word)))
        _ = n ^ extra * Prob.scheduleSum n (W + 1) f := by
            rw [grantBlockPairScheduleSucc]

/-- Exact single-event prefix-lift for arbitrary roots and W≤T. -/
theorem grantBlockPairEventMassPrefix
    {α : Type} {n : Nat} (T W : Nat) (hWT : W ≤ T)
    (hit : α → List (Fin n) → Bool) (x : α) :
    grantBlockEventMass n T
      (fun y word => hit y (word.take W)) x =
    n ^ (T - W) * grantBlockEventMass n W hit x := by
  have htotal : W + (T - W) = T := Nat.add_sub_of_le hWT
  unfold grantBlockEventMass
  calc
    Prob.scheduleSum n T
        (fun word => if hit x (word.take W) then 1 else 0) =
      Prob.scheduleSum n (W + (T - W))
        (fun word => if hit x (word.take W) then 1 else 0) := by
          rw [htotal]
    _ = n ^ (T - W) *
        Prob.scheduleSum n W
          (fun word => if hit x word then 1 else 0) :=
      grantBlockPairScheduleTakeMass W (T - W)
        (fun word => if hit x word then 1 else 0)

/-- Exact pair-intersection prefix-lift, *before* taking products
of different roots' finite masses. -/
theorem grantBlockPairEventIntersectionPrefix
    {α : Type} {n : Nat} (T W : Nat) (hWT : W ≤ T)
    (hit : α → List (Fin n) → Bool) (x y : α) :
    grantBlockEventIntersection n T
      (fun z word => hit z (word.take W)) x y =
    n ^ (T - W) * grantBlockEventIntersection n W hit x y := by
  have htotal : W + (T - W) = T := Nat.add_sub_of_le hWT
  unfold grantBlockEventIntersection
  calc
    Prob.scheduleSum n T
        (fun word =>
          if hit x (word.take W) && hit y (word.take W)
          then 1 else 0) =
      Prob.scheduleSum n (W + (T - W))
        (fun word =>
          if hit x (word.take W) && hit y (word.take W)
          then 1 else 0) := by
          rw [htotal]
    _ = n ^ (T - W) *
        Prob.scheduleSum n W
          (fun word =>
            if hit x word && hit y word then 1 else 0) :=
      grantBlockPairScheduleTakeMass W (T - W)
        (fun word =>
          if hit x word && hit y word then 1 else 0)

/-- Lift the prefix-horizon covariance to the original T-tape
without pretending that word.take W preserves support locality. -/
private theorem grantBlockPairScaleCovariance
    (M N P A B : Nat)
    (h : N * P ≤ A * B) :
    (M * N) * (M * P) ≤ (M * A) * (M * B) := by
  have hh := Nat.mul_le_mul_left (M * M) h
  calc
    (M * N) * (M * P) =
      (M * M) * (N * P) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (M * M) * (A * B) := hh
    _ = (M * A) * (M * B) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem grantBlockPairNegativeCorrelationOnPrefix
    {α : Type} {n : Nat}
    (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (ha : GrantBlockPrefixMonotone a)
    (hb : GrantBlockPrefixMonotone b)
    (hlocalA : ∀ w, a (grantBlockSupportSubword s w) = a w)
    (hlocalB : ∀ w, b (grantBlockSupportSubword t w) = b w)
    (x y : α)
    (hit : α → List (Fin n) → Bool)
    (hx : ∀ w, hit x w = a w)
    (hy : ∀ w, hit y w = b w)
    (T W : Nat) (hWT : W ≤ T) :
    n ^ T * grantBlockEventIntersection n T
      (fun z word => hit z (word.take W)) x y ≤
    grantBlockEventMass n T
      (fun z word => hit z (word.take W)) x *
    grantBlockEventMass n T
      (fun z word => hit z (word.take W)) y := by
  have hword :
      n ^ W * grantBlockEventIntersection n W hit x y ≤
        grantBlockEventMass n W hit x *
          grantBlockEventMass n W hit y := by
    have hbase := grantBlockPairNegativeCorrelationOfLocalWords
      s t a b hdisjoint ha hb hlocalA hlocalB W
    have heqA :
        grantBlockEventMass n W hit x =
          grantBlockEventMass n W
            (fun side : Bool => if side then a else b) true := by
      unfold grantBlockEventMass
      apply congrArg (Prob.scheduleSum n W)
      funext word
      rw [hx]
      rfl
    have heqB :
        grantBlockEventMass n W hit y =
          grantBlockEventMass n W
            (fun side : Bool => if side then a else b) false := by
      unfold grantBlockEventMass
      apply congrArg (Prob.scheduleSum n W)
      funext word
      rw [hy]
      rfl
    have heqAB :
        grantBlockEventIntersection n W hit x y =
          grantBlockEventIntersection n W
            (fun side : Bool => if side then a else b)
              true false := by
      unfold grantBlockEventIntersection
      apply congrArg (Prob.scheduleSum n W)
      funext word
      rw [hx, hy]
      rfl
    rw [heqA, heqB, heqAB]
    rw [Nat.mul_comm]
    exact hbase
  have hpow : n ^ T = n ^ (T - W) * n ^ W := by
    calc
      n ^ T = n ^ ((T - W) + W) := by
        rw [Nat.sub_add_cancel hWT]
      _ = n ^ (T - W) * n ^ W := Nat.pow_add _ _ _
  have hscaled := grantBlockPairScaleCovariance
    (n ^ (T - W)) (n ^ W)
    (grantBlockEventIntersection n W hit x y)
    (grantBlockEventMass n W hit x)
    (grantBlockEventMass n W hit y) hword
  rw [← hpow,
    ← grantBlockPairEventIntersectionPrefix T W hWT hit x y,
    ← grantBlockPairEventMassPrefix T W hWT hit x,
    ← grantBlockPairEventMassPrefix T W hWT hit y] at hscaled
  exact hscaled


/-- Pairwise negative correlation of two geometrically separated
frozen roots, evaluated at the FIRST W global scheduler letters
of a length-T tape. The only geometric assumption is the
certified C.9--C.10 selected-root disjointness. -/
theorem grantBlockFrozenPairNegativeCorrelation
    {n : Nat} (ring : DirectedRing n)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
           Counter.Support (ceilLogTwo n) ring other e))
    (left right : GrantBlockFamilyMember ring)
    (hl : left.1 ∈ selected) (hr : right.1 ∈ selected)
    (hne : left.1 ≠ right.1)
    (T W : Nat) (hWT : W ≤ T) :
    n ^ T * grantBlockEventIntersection n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      left right ≤
    grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      left *
    grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      right := by
  have hdisjoint := grantBlockFrozenPairDisjointOfSelected
    ring selected hselected left right hl hr hne
  exact grantBlockPairNegativeCorrelationOnPrefix
    (grantBlockFrozenEdgeSupport ring left)
    (grantBlockFrozenEdgeSupport ring right)
    (grantBlockFrozenProxyHit ring left)
    (grantBlockFrozenProxyHit ring right)
    hdisjoint
    (grantBlockFrozenPrefixProperty ring left)
    (grantBlockFrozenPrefixProperty ring right)
    (grantBlockFrozenLocalOfSupport ring left)
    (grantBlockFrozenLocalOfSupport ring right)
    left right (grantBlockFrozenProxyHit ring)
    (fun _ => rfl) (fun _ => rfl)
    T W hWT

/-- G16 C.17 first union lower bound, using the exact
support-only frozen events and *not* physical cold-proxy hits.
Distinct Sigma members are insufficient; the family needs
pairwise distinct SELECTED roots. -/
theorem grantBlockFamilyFrozenUnionLower
    {n : Nat} (ring : DirectedRing n)
    (hn : 0 < n)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
           Counter.Support (ceilLogTwo n) ring other e))
    (family : List (GrantBlockFamilyMember ring))
    (hnodup : family.Nodup)
    (hfamily : ∀ member, member ∈ family →
      member.1 ∈ selected)
    (hrootDistinct : ∀ left, left ∈ family →
      ∀ right, right ∈ family → left ≠ right →
      left.1 ≠ right.1)
    (T W : Nat) (hWT : W ≤ T) :
    min (n ^ T)
      (2 * (family.map (grantBlockEventMass n T
        (fun member word =>
          grantBlockFrozenProxyHit ring member
            (word.take W)))).sum) ≤
    4 * grantBlockEventUnion n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      family := by
  apply grantBlockFamilyUnionLower n T hn family
    (fun member word =>
      grantBlockFrozenProxyHit ring member (word.take W))
    hnodup
  intro left hl right hr hne
  exact grantBlockFrozenPairNegativeCorrelation
    ring selected hselected left right
    (hfamily left hl) (hfamily right hr)
    (hrootDistinct left hl right hr hne) T W hWT

/-- The marginal under the event-mass interface is definitionally
the merged frozen success numerator on the original word. -/
theorem grantBlockFrozenEventMassEq
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) :
    grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      member =
    grantBlockFrozenProxyMass ring member T W := by
  rfl

/-- Exact G18 first-hit OR frozen-family-union event.
G18 is a single GLOBAL event and is not inserted into the
pairwise negative-correlation assumptions. -/
noncomputable def grantBlockFamilyFrozenOrG18Mass
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (family : List (GrantBlockFamilyMember ring))
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if grantBlockFamilyAny
        (fun member => grantBlockFrozenProxyHit
          ring member (word.take W)) family ||
       decide (GrantBlockSurrogateG18HitWithin ring C W word)
    then 1 else 0)

/-- The union of frozen hits is contained pointwise in the
OR target, independently of any correlation or C.11 estimate. -/
theorem grantBlockFamilyFrozenUnionLeG18Target
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (family : List (GrantBlockFamilyMember ring))
    (T W : Nat) :
    grantBlockEventUnion n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      family ≤
    grantBlockFamilyFrozenOrG18Mass ring C family T W := by
  unfold grantBlockEventUnion grantBlockFamilyFrozenOrG18Mass
  apply Density.schedule_sum_mono T
  intro word
  cases hh : grantBlockFamilyAny
    (fun member =>
      grantBlockFrozenProxyHit ring member (word.take W))
    family <;>
      simp [hh]

/-- The single G18 first-hit event is independently included
in the same OR union. It is never asserted to be support-local. -/
theorem grantBlockG18HitMassLeFrozenTarget
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (family : List (GrantBlockFamilyMember ring))
    (T W : Nat) :
    grantBlockSurrogateG18HitMass ring C T W ≤
    grantBlockFamilyFrozenOrG18Mass ring C family T W := by
  unfold grantBlockSurrogateG18HitMass
    grantBlockFamilyFrozenOrG18Mass
  apply Density.schedule_sum_mono T
  intro word
  by_cases h : GrantBlockSurrogateG18HitWithin ring C W word
  · simp [h]
  · simp [h]


/-- Exchange the family sum with a common G18 first-hit credit.
All arithmetic is on opaque Nat masses, not compiler powers. -/
private theorem grantBlockPairFamilyScaledSum
    {α : Type} (family : List α)
    (f : α → Nat) (A B G : Nat)
    (h : ∀ member, member ∈ family →
      A ≤ B * (f member + G)) :
    family.length * A ≤
      B * ((family.map f).sum + family.length * G) := by
  induction family with
  | nil =>
      simp
  | cons x rest ih =>
      have hx : A ≤ B * (f x + G) :=
        h x List.mem_cons_self
      have hrest :
          rest.length * A ≤
            B * ((rest.map f).sum + rest.length * G) :=
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul, Nat.mul_add, Nat.add_mul] at *
      omega

/-- Abstract combination of the summed G13 marginal and
the second-order frozen Bonferroni lower estimate. The G18
credit is kept as one independent global event. -/
theorem grantBlockPairUnionArithmetic
    (N B A S U G : Nat)
    (hmarginal : A ≤ B * (S + G))
    (hunion : min N (2 * S) ≤ 4 * U) :
    min (B * N) (2 * A) ≤
      4 * B * U + 2 * B * G := by
  have hdouble :
      2 * A ≤ B * (2 * S + 2 * G) := by
    calc
      2 * A ≤ 2 * (B * (S + G)) :=
        Nat.mul_le_mul_left 2 hmarginal
      _ = B * (2 * S + 2 * G) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
  by_cases hsmall : N ≤ 2 * S
  · have hupper : N ≤ 4 * U := by
      rw [Nat.min_eq_left hsmall] at hunion
      exact hunion
    have hscaled := Nat.mul_le_mul_left B hupper
    calc
      min (B * N) (2 * A) ≤ B * N :=
        Nat.min_le_left _ _
      _ ≤ B * (4 * U) := hscaled
      _ = 4 * B * U := by
          simp only [Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 4 * B * U + 2 * B * G :=
        Nat.le_add_right _ _
  · have hlarge : 2 * S ≤ N := by omega
    have hupper : 2 * S ≤ 4 * U := by
      rw [Nat.min_eq_right hlarge] at hunion
      exact hunion
    have hplus := Nat.add_le_add_right hupper (2 * G)
    have hscaled := Nat.mul_le_mul_left B hplus
    calc
      min (B * N) (2 * A) ≤ 2 * A :=
        Nat.min_le_right _ _
      _ ≤ B * (2 * S + 2 * G) := hdouble
      _ ≤ B * (4 * U + 2 * G) := hscaled
      _ = 4 * B * U + 2 * B * G := by
          simp only [Nat.mul_add, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]

/-- A quantitative C.17 block lower bound on one original
uniform scheduler. It credits the G18 target separately
from the frozen family, with no assertion of correlation
for the physical G18 first-hit event.

Each cold carrier represents the SAME initial configuration C,
as provided by the C.9--C.10 selected-root construction.
-/
theorem grantBlockFamilyFrozenBlockLower
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (C : HeadlineConfiguration n)
    (hpurified : headlinePurified ring C)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
           Counter.Support (ceilLogTwo n) ring other e))
    (family : List (GrantBlockFamilyMember ring))
    (hnodup : family.Nodup)
    (hfamily : ∀ member, member ∈ family →
      member.1 ∈ selected)
    (hrootDistinct : ∀ left, left ∈ family →
      ∀ right, right ∈ family → left ≠ right →
      left.1 ≠ right.1)
    (hCommon : ∀ member, member ∈ family →
      member.2.val = C)
    (R L T W radius : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hBuffered :
      ∀ member, member ∈ family →
        HeadlineGrantBufferedCounter
          ring C radius member.1)
    (hcrossWindow : W ≤ radius * n / 8) :
    min
      ((grantBlockFamilyScale n * 8 ^ radius) * n ^ T)
      (2 * (family.length *
        (((8 ^ radius) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ radius)) *
          n ^ T))) ≤
    4 * (grantBlockFamilyScale n * 8 ^ radius) *
      grantBlockFamilyFrozenOrG18Mass
        ring C family T W +
    2 * (grantBlockFamilyScale n * 8 ^ radius) *
      (family.length *
        grantBlockFamilyFrozenOrG18Mass ring C family T W) := by
  have hone :
      ∀ member, member ∈ family →
        (((8 ^ radius) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ radius)) *
          n ^ T) ≤
        (grantBlockFamilyScale n * 8 ^ radius) *
          (grantBlockEventMass n T
            (fun x word => grantBlockFrozenProxyHit
              ring x (word.take W)) member +
           grantBlockSurrogateG18HitMass ring C T W) := by
    intro member hm
    have hC : member.2.val = C := hCommon member hm
    have hp : headlinePurified ring member.2.val := by
      rw [hC]
      exact hpurified
    have hbuf :
        HeadlineGrantBufferedCounter
          ring member.2.val radius member.1 := by
      rw [hC]
      exact hBuffered member hm
    have hh := grantBlockFrozenProxyMassLowerClean
      ring hn hsp hw hlarge member hp
      R L T W radius hradius hW hL hWT hbudget
      hbuf hcrossWindow
    rw [hC] at hh
    rw [← grantBlockFrozenEventMassEq ring member T W] at hh
    exact hh
  have hsum := grantBlockPairFamilyScaledSum family
    (grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W)))
    (((8 ^ radius) * (51279921 * W) -
      2 * grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ radius)) *
      n ^ T)
    (grantBlockFamilyScale n * 8 ^ radius)
    (grantBlockSurrogateG18HitMass ring C T W) hone
  have hunion := grantBlockFamilyFrozenUnionLower
    ring (by omega : 0 < n)
    selected hselected family hnodup
    hfamily hrootDistinct T W hWT
  have hcombined := grantBlockPairUnionArithmetic
    (n ^ T)
    (grantBlockFamilyScale n * 8 ^ radius)
    (family.length *
      (((8 ^ radius) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ radius)) *
        n ^ T))
    ((family.map (grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member
          (word.take W)))).sum)
    (grantBlockEventUnion n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      family)
    (family.length *
      grantBlockSurrogateG18HitMass ring C T W)
    hsum hunion
  have hunionLe := grantBlockFamilyFrozenUnionLeG18Target
    ring C family T W
  have hgrantLe := grantBlockG18HitMassLeFrozenTarget
    ring C family T W
  have hright :
      4 * (grantBlockFamilyScale n * 8 ^ radius) *
        grantBlockEventUnion n T
          (fun member word =>
            grantBlockFrozenProxyHit ring member (word.take W))
          family +
      2 * (grantBlockFamilyScale n * 8 ^ radius) *
        (family.length *
          grantBlockSurrogateG18HitMass ring C T W) ≤
      4 * (grantBlockFamilyScale n * 8 ^ radius) *
        grantBlockFamilyFrozenOrG18Mass
          ring C family T W +
      2 * (grantBlockFamilyScale n * 8 ^ radius) *
        (family.length *
          grantBlockFamilyFrozenOrG18Mass
            ring C family T W) := by
    exact Nat.add_le_add
      (Nat.mul_le_mul_left
        (4 * (grantBlockFamilyScale n * 8 ^ radius))
        hunionLe)
      (Nat.mul_le_mul_left
        (2 * (grantBlockFamilyScale n * 8 ^ radius))
        (Nat.mul_le_mul_left family.length hgrantLe))
  exact Nat.le_trans hcombined hright


end L3

#print axioms L3.grantBlockPairMaskedPartition
#print axioms L3.grantBlockPairCategorySumProduct
#print axioms L3.grantBlockPairMaskedCovariance
#print axioms L3.grantBlockPrefixHistoryPairNegCorr
#print axioms L3.grantBlockPairNegativeCorrelationOfPrefix
#print axioms L3.grantBlockFrozenPairNegativeCorrelation
#print axioms L3.grantBlockFamilyFrozenUnionLower
#print axioms L3.grantBlockFamilyFrozenBlockLower
