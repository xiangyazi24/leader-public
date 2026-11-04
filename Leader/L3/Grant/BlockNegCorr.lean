import Leader.L3.Grant.BlockFamily

/-!
G16 finite-word negative dependence.

The existing cold proxy is
not local in supported-letter time: it checks cut.length <= W and
runs bankTrialRenewalSuccessBy on (W - cut.length) units of the
global word. Consequently this file does NOT assert that the
actual grantBlockFamilyProxyHit factors through the supported
subsequence.

The negative-correlation theorem below proves the special case
of insertion-monotone local events. This hypothesis is stronger
than prefix-extension monotonicity. The latter needs a finite
multinomial shuffle / weighted Chebyshev decomposition and is
not silently identified with the stronger hypothesis.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The support subsequence, with order preserved. -/
def grantBlockSupportSubword {n : Nat}
    (support : Fin n → Bool) (w : List (Fin n)) :
    List (Fin n) :=
  w.filter support

theorem grantBlockSupportSubwordOutside
    {n : Nat} (support : Fin n → Bool)
    (before after : List (Fin n)) (e : Fin n)
    (hout : support e = false) :
    grantBlockSupportSubword support
      (before ++ e :: after) =
    grantBlockSupportSubword support
      (before ++ after) := by
  simp [grantBlockSupportSubword, List.filter_append, hout]

def grantBlockLocalHit {n : Nat}
    (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (w : List (Fin n)) : Bool :=
  success (grantBlockSupportSubword support w)

theorem grantBlockLocalHitOutside
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (before after : List (Fin n)) (e : Fin n)
    (hout : support e = false) :
    grantBlockLocalHit support success (before ++ e :: after) =
      grantBlockLocalHit support success (before ++ after) := by
  exact congrArg success
    (grantBlockSupportSubwordOutside support before after e hout)

/-- The user's prefix-extension assumption. -/
def GrantBlockPrefixMonotone {n : Nat}
    (success : List (Fin n) → Bool) : Prop :=
  ∀ u v : List (Fin n),
    success u = true → success (u ++ v) = true

/-- A stronger assumption useful for first-letter induction:
inserting any supported letter anywhere preserves success. -/
def GrantBlockInsertionMonotone {n : Nat}
    (support : Fin n → Bool)
    (success : List (Fin n) → Bool) : Prop :=
  ∀ before after : List (Fin n), ∀ e : Fin n,
    support e = true →
      success (before ++ after) = true →
      success (before ++ e :: after) = true

theorem grantBlockInsertionImpliesPrefix
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (h : GrantBlockInsertionMonotone support success)
    (u v : List (Fin n))
    (hs : success u = true)
    (hv : ∀ e : Fin n, e ∈ v → support e = true) :
    success (u ++ v) = true := by
  induction v with
  | nil =>
      simpa only [List.append_nil] using hs
  | cons e es ih =>
      have he : support e = true :=
        hv e List.mem_cons_self
      have ht : ∀ x : Fin n, x ∈ es → support x = true := by
        intro x hx
        exact hv x (List.mem_cons_of_mem _ hx)
      exact h u es e he (ih ht)

noncomputable def grantBlockLocalMass
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool) (T : Nat) : Nat :=
  Prob.scheduleSum n T
    (fun w => if grantBlockLocalHit support success w then 1 else 0)

noncomputable def grantBlockLocalPairMass
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool) (T : Nat) : Nat :=
  Prob.scheduleSum n T
    (fun w =>
      if grantBlockLocalHit s a w &&
          grantBlockLocalHit t b w then 1 else 0)

def grantBlockFront {n : Nat}
    (support : Fin n → Bool)
    (success : List (Fin n) → Bool) (e : Fin n) :
    List (Fin n) → Bool :=
  fun w => if support e then success (e :: w) else success w

private theorem grantBlockFrontInsertion
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (h : GrantBlockInsertionMonotone support success)
    (e : Fin n) :
    GrantBlockInsertionMonotone support
      (grantBlockFront support success e) := by
  intro before after f hf hsuccess
  by_cases he : support e = true
  · have hOld : success ((e :: before) ++ after) = true := by
      simpa [grantBlockFront, he] using hsuccess
    have hNew := h (e :: before) after f hf hOld
    simpa [grantBlockFront, he] using hNew
  · have hOld : success (before ++ after) = true := by
      simpa [grantBlockFront, he] using hsuccess
    have hNew := h before after f hf hOld
    simpa [grantBlockFront, he] using hNew

private theorem grantBlockFrontMassMono
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (h : GrantBlockInsertionMonotone support success)
    (e : Fin n) (T : Nat) :
    grantBlockLocalMass support success T ≤
      grantBlockLocalMass support
        (grantBlockFront support success e) T := by
  unfold grantBlockLocalMass
  apply Density.schedule_sum_mono T
  intro w
  by_cases hs : success (grantBlockSupportSubword support w) = true
  · by_cases he : support e = true
    · have hval :
          success (e :: grantBlockSupportSubword support w) = true := by
        have hh := h [] (grantBlockSupportSubword support w) e he hs
        simpa only [List.nil_append] using hh
      simp [grantBlockLocalHit, grantBlockFront, hs, he, hval]
    · have hf : support e = false := by
        cases hc : support e with
        | false => rfl
        | true => exact False.elim (he hc)
      simp [grantBlockLocalHit, grantBlockFront, hs, hf]
  · have hf : success (grantBlockSupportSubword support w) = false := by
      cases hc : success (grantBlockSupportSubword support w) with
      | false => rfl
      | true => exact False.elim (hs hc)
    simp [grantBlockLocalHit, grantBlockFront, hf]

private theorem grantBlockFrontMassOutside
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (e : Fin n) (T : Nat)
    (hout : support e = false) :
    grantBlockLocalMass support
      (grantBlockFront support success e) T =
        grantBlockLocalMass support success T := by
  unfold grantBlockLocalMass
  apply congrArg (Prob.scheduleSum n T)
  funext w
  simp only [grantBlockLocalHit, grantBlockFront, hout,
    Bool.false_eq_true, if_false] <;> rfl

private theorem grantBlockOppositeProducts
    (a c b d : Nat) (ha : a ≤ c) (hd : d ≤ b) :
    a * b + c * d ≤ a * d + c * b := by
  have hsplit : d + (b - d) = b :=
    Nat.add_sub_of_le hd
  have hmult : a * (b - d) ≤ c * (b - d) :=
    Nat.mul_le_mul_right (b - d) ha
  have hleft : a * b = a * d + a * (b - d) := by
    calc
      a * b = a * (d + (b - d)) := by rw [hsplit]
      _ = a * d + a * (b - d) := by rw [Nat.mul_add]
  have hright : c * b = c * d + c * (b - d) := by
    calc
      c * b = c * (d + (b - d)) := by rw [hsplit]
      _ = c * d + c * (b - d) := by rw [Nat.mul_add]
  calc
    a * b + c * d =
        (a * d + c * d) + a * (b - d) := by
          rw [hleft]
          omega
    _ ≤ (a * d + c * d) + c * (b - d) :=
      Nat.add_le_add_left hmult _
    _ = a * d + c * b := by
      rw [hright]
      omega

private theorem grantBlockDisjointCross
    (a b x y u v : Nat)
    (hxa : a ≤ x) (hyb : b ≤ y)
    (hua : a ≤ u) (hvb : b ≤ v)
    (hx : x = a ∨ y = b)
    (hu : u = a ∨ v = b) :
    x * y + u * v ≤ x * v + u * y := by
  rcases hx with he | he
  · rcases hu with hf | hf
    · rw [he, hf]
      omega
    · rw [he, hf]
      exact grantBlockOppositeProducts a u y b hua hyb
  · rcases hu with hf | hf
    · rw [he, hf]
      have hh := grantBlockOppositeProducts a x v b hxa hvb
      omega
    · rw [he, hf]
      omega

private theorem grantBlockOppositeCrossList
    {α : Type} (f g : α → Nat) (x : α) :
    ∀ xs : List α,
      (∀ y, y ∈ xs →
        f x * g x + f y * g y ≤
          f x * g y + f y * g x) →
      xs.length * (f x * g x) +
        (xs.map (fun y => f y * g y)).sum ≤
        f x * (xs.map g).sum + g x * (xs.map f).sum := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons y ys ih =>
      intro h
      have hy := h y List.mem_cons_self
      have ht := ih (fun z hz =>
        h z (List.mem_cons_of_mem _ hz))
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul, Nat.mul_add] at *
      have hcomm : f y * g x = g x * f y := Nat.mul_comm _ _
      rw [hcomm] at hy
      omega

theorem grantBlockOppositeChebyshev
    {α : Type} (xs : List α)
    (f g : α → Nat)
    (h : ∀ x, x ∈ xs → ∀ y, y ∈ xs →
      f x * g x + f y * g y ≤
        f x * g y + f y * g x) :
    xs.length * (xs.map (fun x => f x * g x)).sum ≤
      (xs.map f).sum * (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail :
          xs.length * (xs.map (fun x => f x * g x)).sum ≤
            (xs.map f).sum * (xs.map g).sum := by
        apply ih
        intro a ha b hb
        exact h a (List.mem_cons_of_mem _ ha)
          b (List.mem_cons_of_mem _ hb)
      have hcross := grantBlockOppositeCrossList f g x xs
        (fun y hy =>
          h x List.mem_cons_self y
            (List.mem_cons_of_mem _ hy))
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul, Nat.mul_add, Nat.add_mul] at *
      have hcomm : g x * (xs.map f).sum =
          (xs.map f).sum * g x := Nat.mul_comm _ _
      rw [hcomm] at hcross
      omega

private theorem grantBlockLocalMassSucc
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool) (T : Nat) :
    grantBlockLocalMass support success (T + 1) =
      (List.ofFn (fun e : Fin n =>
        grantBlockLocalMass support
          (grantBlockFront support success e) T)).sum := by
  unfold grantBlockLocalMass
  change FixedSpanRenewalPayload.wordSum n (T + 1)
      (fun w => if grantBlockLocalHit support success w then 1 else 0) = _
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  apply congrArg (Prob.scheduleSum n T)
  funext w
  cases he : support e <;>
    simp [grantBlockLocalHit, grantBlockSupportSubword,
      grantBlockFront, he]

private theorem grantBlockLocalPairMassSucc
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool) (T : Nat) :
    grantBlockLocalPairMass s t a b (T + 1) =
      (List.ofFn (fun e : Fin n =>
        grantBlockLocalPairMass s t
          (grantBlockFront s a e)
          (grantBlockFront t b e) T)).sum := by
  unfold grantBlockLocalPairMass
  change FixedSpanRenewalPayload.wordSum n (T + 1)
      (fun w => if grantBlockLocalHit s a w &&
        grantBlockLocalHit t b w then 1 else 0) = _
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  apply congrArg (Prob.scheduleSum n T)
  funext w
  cases he : s e <;> cases hf : t e <;>
    simp [grantBlockLocalHit, grantBlockSupportSubword,
      grantBlockFront, he, hf]

theorem grantBlockPairNegativeCorrelation
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (hdisjoint : ∀ e : Fin n,
      ¬ (s e = true ∧ t e = true))
    (hInsertA : GrantBlockInsertionMonotone s a)
    (hInsertB : GrantBlockInsertionMonotone t b) :
    ∀ T : Nat,
      grantBlockLocalPairMass s t a b T * n ^ T ≤
        grantBlockLocalMass s a T *
          grantBlockLocalMass t b T := by
  intro T
  induction T generalizing a b with
  | zero =>
      simp [grantBlockLocalPairMass, grantBlockLocalMass,
        grantBlockLocalHit, grantBlockSupportSubword,
        Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
        allSchedules]
      by_cases ha : a [] = true
      · by_cases hb : b [] = true
        · simp [ha, hb]
        · simp [ha, hb]
      · simp [ha]
  | succ T ih =>
      have hrow (e : Fin n) :
          grantBlockLocalPairMass s t
              (grantBlockFront s a e)
              (grantBlockFront t b e) T * n ^ T ≤
            grantBlockLocalMass s
              (grantBlockFront s a e) T *
            grantBlockLocalMass t
              (grantBlockFront t b e) T :=
        ih (grantBlockFront s a e)
          (grantBlockFront t b e)
          (grantBlockFrontInsertion s a hInsertA e)
          (grantBlockFrontInsertion t b hInsertB e)
      have hsum :
          (List.ofFn (fun e : Fin n =>
            grantBlockLocalPairMass s t
              (grantBlockFront s a e)
              (grantBlockFront t b e) T)).sum * n ^ T ≤
          (List.ofFn (fun e : Fin n =>
            grantBlockLocalMass s
              (grantBlockFront s a e) T *
            grantBlockLocalMass t
              (grantBlockFront t b e) T)).sum := by
        calc
          (List.ofFn (fun e : Fin n =>
            grantBlockLocalPairMass s t
              (grantBlockFront s a e)
              (grantBlockFront t b e) T)).sum * n ^ T =
          (List.ofFn (fun e : Fin n =>
            n ^ T * grantBlockLocalPairMass s t
              (grantBlockFront s a e)
              (grantBlockFront t b e) T)).sum := by
                rw [Nat.mul_comm
                  (List.ofFn (fun e : Fin n =>
                    grantBlockLocalPairMass s t
                      (grantBlockFront s a e)
                      (grantBlockFront t b e) T)).sum (n ^ T)]
                exact (ofFn_sum_mul_left (n ^ T)
                  (fun e : Fin n =>
                    grantBlockLocalPairMass s t
                      (grantBlockFront s a e)
                      (grantBlockFront t b e) T)).symm
          _ ≤ _ := by
            apply ofFn_sum_le _ _
            intro e
            rw [Nat.mul_comm (n ^ T)
              (grantBlockLocalPairMass s t
                (grantBlockFront s a e)
                (grantBlockFront t b e) T)]
            exact hrow e
      have hcheb :
          n * (List.ofFn (fun e : Fin n =>
            grantBlockLocalMass s (grantBlockFront s a e) T *
              grantBlockLocalMass t (grantBlockFront t b e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            grantBlockLocalMass s (grantBlockFront s a e) T)).sum *
          (List.ofFn (fun e : Fin n =>
            grantBlockLocalMass t (grantBlockFront t b e) T)).sum := by
        have hpair (e d : Fin n) :
            grantBlockLocalMass s (grantBlockFront s a e) T *
              grantBlockLocalMass t (grantBlockFront t b e) T +
            grantBlockLocalMass s (grantBlockFront s a d) T *
              grantBlockLocalMass t (grantBlockFront t b d) T ≤
            grantBlockLocalMass s (grantBlockFront s a e) T *
              grantBlockLocalMass t (grantBlockFront t b d) T +
            grantBlockLocalMass s (grantBlockFront s a d) T *
              grantBlockLocalMass t (grantBlockFront t b e) T := by
          apply grantBlockDisjointCross
            (grantBlockLocalMass s a T)
            (grantBlockLocalMass t b T)
          · exact grantBlockFrontMassMono s a hInsertA e T
          · exact grantBlockFrontMassMono t b hInsertB e T
          · exact grantBlockFrontMassMono s a hInsertA d T
          · exact grantBlockFrontMassMono t b hInsertB d T
          · by_cases he : s e = true
            · have ht : t e = false := by
                cases hh : t e with
                | false => rfl
                | true => exact False.elim (hdisjoint e ⟨he, hh⟩)
              exact Or.inr
                (grantBlockFrontMassOutside t b e T ht)
            · have hs : s e = false := by
                cases hh : s e with
                | false => rfl
                | true => exact False.elim (he hh)
              exact Or.inl
                (grantBlockFrontMassOutside s a e T hs)
          · by_cases he : s d = true
            · have ht : t d = false := by
                cases hh : t d with
                | false => rfl
                | true => exact False.elim (hdisjoint d ⟨he, hh⟩)
              exact Or.inr
                (grantBlockFrontMassOutside t b d T ht)
            · have hs : s d = false := by
                cases hh : s d with
                | false => rfl
                | true => exact False.elim (he hh)
              exact Or.inl
                (grantBlockFrontMassOutside s a d T hs)
        have hlist := grantBlockOppositeChebyshev
          (List.ofFn (fun e : Fin n => e))
          (fun e => grantBlockLocalMass s (grantBlockFront s a e) T)
          (fun e => grantBlockLocalMass t (grantBlockFront t b e) T)
          (fun e _ d _ => hpair e d)
        simpa only [List.length_ofFn, List.map_ofFn,
          Function.comp_def] using hlist
      calc
        grantBlockLocalPairMass s t a b (T + 1) * n ^ (T + 1) =
          n * ((List.ofFn (fun e : Fin n =>
            grantBlockLocalPairMass s t
              (grantBlockFront s a e)
              (grantBlockFront t b e) T)).sum * n ^ T) := by
                rw [grantBlockLocalPairMassSucc, Nat.pow_succ]
                simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ n * (List.ofFn (fun e : Fin n =>
            grantBlockLocalMass s (grantBlockFront s a e) T *
              grantBlockLocalMass t (grantBlockFront t b e) T)).sum :=
          Nat.mul_le_mul_left _ hsum
        _ ≤ (List.ofFn (fun e : Fin n =>
              grantBlockLocalMass s (grantBlockFront s a e) T)).sum *
            (List.ofFn (fun e : Fin n =>
              grantBlockLocalMass t (grantBlockFront t b e) T)).sum :=
          hcheb
        _ = grantBlockLocalMass s a (T + 1) *
            grantBlockLocalMass t b (T + 1) := by
          rw [grantBlockLocalMassSucc, grantBlockLocalMassSucc]

/-! ## Generic Bonferroni and subfamily selection -/

/-- The sum of products over unordered positions of a list. -/
def grantBlockPairProducts {α : Type}
    (mass : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs =>
      mass x * (xs.map mass).sum +
        grantBlockPairProducts mass xs

theorem grantBlockPairProductsSquare
    {α : Type} (mass : α → Nat) :
    ∀ xs : List α,
      2 * grantBlockPairProducts mass xs ≤
        (xs.map mass).sum * (xs.map mass).sum := by
  intro xs
  induction xs with
  | nil =>
      simp [grantBlockPairProducts]
  | cons x xs ih =>
      change 2 * (mass x * (xs.map mass).sum +
          grantBlockPairProducts mass xs) ≤
        (mass x + (xs.map mass).sum) *
          (mass x + (xs.map mass).sum)
      have hbase :
          2 * (mass x * (xs.map mass).sum +
            grantBlockPairProducts mass xs) ≤
          2 * (mass x * (xs.map mass).sum) +
            (xs.map mass).sum * (xs.map mass).sum := by
        omega
      have hquad :
          2 * (mass x * (xs.map mass).sum) +
            (xs.map mass).sum * (xs.map mass).sum ≤
          (mass x + (xs.map mass).sum) *
            (mass x + (xs.map mass).sum) := by
        simp only [Nat.mul_add, Nat.add_mul]
        rw [Nat.mul_comm (xs.map mass).sum (mass x)]
        omega
      exact Nat.le_trans hbase hquad

/-- Exact integer form of the small-subfamily lower bound.
No division, rational normalization or noninteger limit is used. -/
private theorem grantBlockSmallMassArithmetic
    (N sumMass unionMass pairMass pairProducts : Nat)
    (hN : 0 < N)
    (hSmall : sumMass ≤ N)
    (hBonf : sumMass ≤ unionMass + pairMass)
    (hPair : N * pairMass ≤ pairProducts)
    (hProducts : 2 * pairProducts ≤ sumMass * sumMass) :
    sumMass ≤ 2 * unionMass := by
  have hFirst : N * sumMass ≤
      N * unionMass + pairProducts := by
    have hScaled := Nat.mul_le_mul_left N hBonf
    rw [Nat.mul_add] at hScaled
    omega
  have hSquare : sumMass * sumMass ≤
      N * sumMass := Nat.mul_le_mul_right sumMass hSmall
  have hTwice : 2 * (N * sumMass) ≤
      2 * (N * unionMass) + 2 * pairProducts := by
    have h := Nat.mul_le_mul_left 2 hFirst
    rw [Nat.mul_add] at h
    exact h
  have hScaled : N * sumMass ≤ N * (2 * unionMass) := by
    have hright : N * (2 * unionMass) =
        2 * (N * unionMass) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hright]
    omega
  exact Nat.le_of_mul_le_mul_left hScaled hN

private theorem grantBlockHalfPrefixWalk
    {α : Type} (mass : α → Nat) (N : Nat) :
    ∀ (xs : List α) (acc : Nat),
      2 * acc < N →
      N ≤ 2 * (acc + (xs.map mass).sum) →
      (∀ x : α, x ∈ xs → 2 * mass x < N) →
      ∃ pre rest : List α,
        xs = pre ++ rest ∧
        N ≤ 2 * (acc + (pre.map mass).sum) ∧
        acc + (pre.map mass).sum ≤ N := by
  intro xs
  induction xs with
  | nil =>
      intro acc hBefore hTotal _
      simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hTotal
      omega
  | cons x xs ih =>
      intro acc hBefore hTotal hEach
      have hx : 2 * mass x < N :=
        hEach x List.mem_cons_self
      by_cases hCross : N ≤ 2 * (acc + mass x)
      · refine ⟨[x], xs, rfl, ?_, ?_⟩
        · simpa using hCross
        · simp only [List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Nat.add_zero]
          omega
      · have hNextBefore : 2 * (acc + mass x) < N := by omega
        have hNextTotal :
            N ≤ 2 * ((acc + mass x) + (xs.map mass).sum) := by
          simp only [List.map_cons, List.sum_cons] at hTotal
          omega
        have hTail : ∀ y : α, y ∈ xs →
            2 * mass y < N := by
          intro y hy
          exact hEach y (List.mem_cons_of_mem _ hy)
        obtain ⟨pre, rest, hSplit, hLower, hUpper⟩ :=
          ih (acc + mass x) hNextBefore hNextTotal hTail
        refine ⟨x :: pre, rest, ?_, ?_, ?_⟩
        · rw [hSplit]
          rfl
        · simp only [List.map_cons, List.sum_cons]
          omega
        · simp only [List.map_cons, List.sum_cons]
          omega

private theorem grantBlockHalfPrefix
    {α : Type} (mass : α → Nat)
    (N : Nat) (xs : List α)
    (hN : 0 < N)
    (hLarge : N ≤ 2 * (xs.map mass).sum)
    (hEach : ∀ x : α, x ∈ xs → 2 * mass x < N) :
    ∃ pre rest : List α,
      xs = pre ++ rest ∧
      N ≤ 2 * (pre.map mass).sum ∧
      (pre.map mass).sum ≤ N := by
  have h := grantBlockHalfPrefixWalk
    mass N xs 0 (by omega)
    (by simpa using hLarge) hEach
  simpa only [Nat.zero_add] using h

/-- Pure finite-family subfamily selection. Here N denotes the
number of equally likely scheduler words, U a union numerator,
and P the exact pair numerator. Valid for arbitrary lists,
including a root with probability larger than one half. -/
theorem grantBlockFamilyUnionLowerArithmetic
    {α : Type} (N : Nat) (mass : α → Nat)
    (unionMass pairMass : List α → Nat)
    (family : List α)
    (hN : 0 < N)
    (hBonf : ∀ xs : List α,
      (xs.map mass).sum ≤ unionMass xs + pairMass xs)
    (hPair : ∀ pre rest : List α,
      family = pre ++ rest →
      N * pairMass pre ≤ grantBlockPairProducts mass pre)
    (hPrefix : ∀ pre rest : List α,
      unionMass pre ≤ unionMass (pre ++ rest))
    (hMember : ∀ x : α, x ∈ family →
      mass x ≤ unionMass family) :
    min N (2 * (family.map mass).sum) ≤
      4 * unionMass family := by
  have hSmallLaw (xs rest : List α)
      (hPiece : family = xs ++ rest)
      (hSmall : (xs.map mass).sum ≤ N) :
      (xs.map mass).sum ≤ 2 * unionMass xs :=
    grantBlockSmallMassArithmetic N
      (xs.map mass).sum
      (unionMass xs) (pairMass xs)
      (grantBlockPairProducts mass xs)
      hN hSmall (hBonf xs) (hPair xs rest hPiece)
      (grantBlockPairProductsSquare mass xs)
  by_cases hShort :
      2 * (family.map mass).sum < N
  · have hBound : (family.map mass).sum ≤ N := by omega
    have hHalf := hSmallLaw family [] (by simp) hBound
    have hMin :
        min N (2 * (family.map mass).sum) =
          2 * (family.map mass).sum :=
      Nat.min_eq_right (by omega)
    rw [hMin]
    omega
  · have hLarge :
        N ≤ 2 * (family.map mass).sum := by omega
    by_cases hSingle :
        ∃ x : α, x ∈ family ∧ N ≤ 2 * mass x
    · obtain ⟨x, hx, hbig⟩ := hSingle
      have hOne := hMember x hx
      have hMin :
          min N (2 * (family.map mass).sum) = N :=
        Nat.min_eq_left hLarge
      rw [hMin]
      omega
    · have hEach :
          ∀ x : α, x ∈ family → 2 * mass x < N := by
        intro x hx
        have hn : ¬ N ≤ 2 * mass x := by
          intro hh
          exact hSingle ⟨x, hx, hh⟩
        omega
      obtain ⟨pre, rest, hSplit, hCut, hCap⟩ :=
        grantBlockHalfPrefix mass N family hN hLarge hEach
      have hSmall := hSmallLaw pre rest hSplit hCap
      have hMon := hPrefix pre rest
      have hCurrent : unionMass pre ≤ unionMass family := by
        rw [hSplit]
        exact hMon
      have hMin :
          min N (2 * (family.map mass).sum) = N :=
        Nat.min_eq_left hLarge
      rw [hMin]
      omega

/-! ## Literal Boolean-event mass specialization -/

noncomputable def grantBlockEventMass
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool) (x : α) : Nat :=
  Prob.scheduleSum n T
    (fun w => if hit x w then 1 else 0)

noncomputable def grantBlockEventIntersection
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool)
    (x y : α) : Nat :=
  Prob.scheduleSum n T
    (fun w => if hit x w && hit y w then 1 else 0)

noncomputable def grantBlockEventUnion
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool)
    (xs : List α) : Nat :=
  Prob.scheduleSum n T
    (fun w =>
      if grantBlockFamilyAny (fun x => hit x w) xs
      then 1 else 0)

noncomputable def grantBlockEventPairs
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool)
    (xs : List α) : Nat :=
  Prob.scheduleSum n T
    (fun w => grantBlockFamilyPairs (fun x => hit x w) xs)

private theorem grantBlockAnyAppend
    {α : Type} (hit : α → Bool)
    (xs ys : List α) :
    grantBlockFamilyAny hit (xs ++ ys) =
      (grantBlockFamilyAny hit xs ||
        grantBlockFamilyAny hit ys) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [grantBlockFamilyAny, ih, Bool.or_assoc]

private theorem grantBlockEventUnionPrefix
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool)
    (xs ys : List α) :
    grantBlockEventUnion n T hit xs ≤
      grantBlockEventUnion n T hit (xs ++ ys) := by
  unfold grantBlockEventUnion
  apply Density.schedule_sum_mono T
  intro w
  rw [grantBlockAnyAppend]
  cases hh : grantBlockFamilyAny (fun x => hit x w) xs <;>
    simp [hh]

private theorem grantBlockAnyOfMem
    {α : Type} (hit : α → Bool)
    (xs : List α) (x : α)
    (hx : x ∈ xs) (hh : hit x = true) :
    grantBlockFamilyAny hit xs = true := by
  induction xs with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with he | he
      · subst y
        simp [grantBlockFamilyAny, hh]
      · by_cases hy : hit y = true
        · simp [grantBlockFamilyAny, hy]
        · have hrest := ih he
          simpa [grantBlockFamilyAny, hy] using hrest

private theorem grantBlockEventMemberMassLe
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool)
    (xs : List α) (x : α) (hx : x ∈ xs) :
    grantBlockEventMass n T hit x ≤
      grantBlockEventUnion n T hit xs := by
  unfold grantBlockEventMass grantBlockEventUnion
  apply Density.schedule_sum_mono T
  intro w
  by_cases h : hit x w = true
  · have hh := grantBlockAnyOfMem
      (fun y => hit y w) xs x hx h
    simp [h, hh]
  · simp [h]

private theorem grantBlockScheduleConstZero
    (n T : Nat) :
    Prob.scheduleSum n T
      (fun _ : List (Fin n) => 0) = 0 := by
  change FixedSpanRenewalPayload.wordSum n T
    (fun _ : List (Fin n) => 0) = 0
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  simp only [ofFn_sum_const, Nat.mul_zero]

private theorem grantBlockScheduleAdd
    (n T : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => f w + g w) =
      Prob.scheduleSum n T f +
        Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum,
    ← FixedSpanRenewalPayload.rawWord_sum,
    ← FixedSpanRenewalPayload.rawWord_sum]
  exact ofFn_sum_add _ _

private theorem grantBlockScheduleMapSum
    {α : Type} (n T : Nat)
    (xs : List α)
    (f : α → List (Fin n) → Nat) :
    Prob.scheduleSum n T
      (fun w => (xs.map (fun x => f x w)).sum) =
      (xs.map (fun x => Prob.scheduleSum n T (f x))).sum := by
  induction xs with
  | nil =>
      exact grantBlockScheduleConstZero n T
  | cons x xs ih =>
      change Prob.scheduleSum n T
          (fun w => f x w +
            (xs.map (fun y => f y w)).sum) =
        Prob.scheduleSum n T (f x) +
          (xs.map (fun y =>
            Prob.scheduleSum n T (f y))).sum
      rw [grantBlockScheduleAdd, ih]

private theorem grantBlockIntersectionWord
    {α : Type} (hit : α → Bool) (x : α) :
    ∀ xs : List α,
      (if hit x then grantBlockFamilyHits hit xs else 0) =
      (xs.map (fun y => if hit x && hit y then 1 else 0)).sum := by
  intro xs
  induction xs with
  | nil =>
      cases hh : hit x <;> rfl
  | cons y ys ih =>
      cases hh : hit x with
      | false =>
          simpa only [hh, Bool.false_and, Bool.false_eq_true,
            if_false, List.map_cons, List.sum_cons, Nat.zero_add]
            using ih
      | true =>
          have htail : grantBlockFamilyHits hit ys =
              (ys.map (fun z => if hit z then 1 else 0)).sum := by
            simpa only [hh, if_true, Bool.true_and] using ih
          simp only [hh, if_true, Bool.true_and,
            grantBlockFamilyHits, List.map_cons, List.sum_cons]
          exact congrArg (fun z => (if hit y then 1 else 0) + z)
            htail

private theorem grantBlockEventPairsCons
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool)
    (x : α) (xs : List α) :
    grantBlockEventPairs n T hit (x :: xs) =
      (xs.map (fun y =>
        grantBlockEventIntersection n T hit x y)).sum +
      grantBlockEventPairs n T hit xs := by
  unfold grantBlockEventPairs
  change Prob.scheduleSum n T
      (fun w =>
        (if hit x w then
          grantBlockFamilyHits (fun y => hit y w) xs else 0) +
        grantBlockFamilyPairs (fun y => hit y w) xs) = _
  rw [grantBlockScheduleAdd]
  have hfirst :
      Prob.scheduleSum n T
        (fun w => if hit x w then
          grantBlockFamilyHits (fun y => hit y w) xs else 0) =
      (xs.map (fun y =>
        grantBlockEventIntersection n T hit x y)).sum := by
    calc
      _ = Prob.scheduleSum n T
          (fun w => (xs.map (fun y =>
            if hit x w && hit y w then 1 else 0)).sum) := by
              apply congrArg (Prob.scheduleSum n T)
              funext w
              exact grantBlockIntersectionWord
                (fun y => hit y w) x xs
      _ = _ := grantBlockScheduleMapSum n T xs _
  rw [hfirst]

private theorem grantBlockMappedProductBound
    {α : Type} (N a : Nat)
    (f g : α → Nat) :
    ∀ xs : List α,
      (∀ x : α, x ∈ xs → N * f x ≤ a * g x) →
      N * (xs.map f).sum ≤ a * (xs.map g).sum := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hh := h x List.mem_cons_self
      have ht := ih (fun y hy =>
        h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add] at *
      omega

/-- A prefix of a duplicate-free family has no repeated root. -/
private theorem grantBlockNodupPrefix
    {α : Type} :
    ∀ (pre rest : List α),
      (pre ++ rest).Nodup → pre.Nodup := by
  intro pre
  induction pre with
  | nil =>
      intro rest _
      simp
  | cons x xs ih =>
      intro rest h
      rw [List.cons_append, List.nodup_cons] at h
      rw [List.nodup_cons]
      constructor
      · intro hx
        exact h.1 (List.mem_append_left _ hx)
      · exact ih rest h.2

private theorem grantBlockEventPairsProductBound
    {α : Type} (n T : Nat)
    (hit : α → List (Fin n) → Bool) :
    ∀ xs : List α,
      xs.Nodup →
      (∀ x : α, x ∈ xs →
        ∀ y : α, y ∈ xs → x ≠ y →
          n ^ T * grantBlockEventIntersection n T hit x y ≤
            grantBlockEventMass n T hit x *
              grantBlockEventMass n T hit y) →
      n ^ T * grantBlockEventPairs n T hit xs ≤
        grantBlockPairProducts
          (grantBlockEventMass n T hit) xs := by
  intro xs
  induction xs with
  | nil =>
      intro _ _
      change n ^ T * Prob.scheduleSum n T
        (fun _ : List (Fin n) => 0) ≤ 0
      rw [grantBlockScheduleConstZero]
      omega
  | cons x xs ih =>
      intro hNodup hNeg
      have hSplit := List.nodup_cons.mp hNodup
      have hfirst :
          n ^ T * (xs.map (fun y =>
            grantBlockEventIntersection n T hit x y)).sum ≤
          grantBlockEventMass n T hit x *
            (xs.map (grantBlockEventMass n T hit)).sum := by
        apply grantBlockMappedProductBound (n ^ T)
          (grantBlockEventMass n T hit x)
          (fun y => grantBlockEventIntersection n T hit x y)
          (grantBlockEventMass n T hit) xs
        intro y hy
        have hDifferent : x ≠ y := by
          intro he
          apply hSplit.1
          rw [he]
          exact hy
        exact hNeg x List.mem_cons_self
          y (List.mem_cons_of_mem _ hy) hDifferent
      have htail :
          n ^ T * grantBlockEventPairs n T hit xs ≤
          grantBlockPairProducts
            (grantBlockEventMass n T hit) xs := by
        apply ih hSplit.2
        intro y hy z hz hne
        exact hNeg y (List.mem_cons_of_mem _ hy)
          z (List.mem_cons_of_mem _ hz) hne
      rw [grantBlockEventPairsCons]
      change n ^ T *
        ((xs.map (fun y =>
          grantBlockEventIntersection n T hit x y)).sum +
          grantBlockEventPairs n T hit xs) ≤
        grantBlockEventMass n T hit x *
          (xs.map (grantBlockEventMass n T hit)).sum +
          grantBlockPairProducts (grantBlockEventMass n T hit) xs
      rw [Nat.mul_add]
      omega

/-- This is part (iii), with NO per-root upper bound.
It is conditional ONLY on the desired pairwise product estimate,
which is explicitly part (ii) and is not proved for the literal
cold proxy above. If some single probability >= 1/2, that
single event wins; otherwise a shortest-prefix subfamily is used. -/
theorem grantBlockFamilyUnionLower
    {α : Type} (n T : Nat) (hn : 0 < n)
    (family : List α)
    (hit : α → List (Fin n) → Bool)
    (hNoDup : family.Nodup)
    (hNeg : ∀ x : α, x ∈ family →
      ∀ y : α, y ∈ family → x ≠ y →
      n ^ T * grantBlockEventIntersection n T hit x y ≤
        grantBlockEventMass n T hit x *
          grantBlockEventMass n T hit y) :
    min (n ^ T)
        (2 * (family.map (grantBlockEventMass n T hit)).sum) ≤
      4 * grantBlockEventUnion n T hit family := by
  apply grantBlockFamilyUnionLowerArithmetic
    (n ^ T) (grantBlockEventMass n T hit)
    (grantBlockEventUnion n T hit)
    (grantBlockEventPairs n T hit)
    family (Nat.pow_pos hn)
  · intro xs
    exact grantBlockFamilyBonferroniMass n T xs hit
  · intro pre rest hPiece
    have hPrefixNodup : pre.Nodup := by
      have hAll : (pre ++ rest).Nodup := by
        rw [← hPiece]
        exact hNoDup
      exact grantBlockNodupPrefix pre rest hAll
    apply grantBlockEventPairsProductBound
      n T hit pre hPrefixNodup
    intro x hx y hy hne
    have hxf : x ∈ family := by
      rw [hPiece]
      exact List.mem_append_left _ hx
    have hyf : y ∈ family := by
      rw [hPiece]
      exact List.mem_append_left _ hy
    exact hNeg x hxf y hyf hne
  · intro pre rest
    exact grantBlockEventUnionPrefix n T hit pre rest
  · intro x hx
    exact grantBlockEventMemberMassLe n T hit family x hx

/-!
The full prefix-only negative-correlation theorem is not
established above. It requires the finite shuffle identity
conditioning on the number of letters in one support; after
conditioning, the supported subsequences are independent,
and the success probabilities are oppositely monotone in
the conditioned support count. Insertion monotonicity is
a strictly stronger route and does not prove that identity
for merely prefix-monotone observers.

For the actual cold proxy there is a more basic obstruction:
the event uses cut.length <= W and the remaining GLOBAL time
W-cut.length. Even if an outsideSupportedBankFrame step leaves
all support agents unchanged, it consumes a unit of wall time.
To use grantBlockFamilyUnionLower for C.17 one must first
construct a genuinely support-subsequence-local observer and
prove a comparison of its probability with the existing
global-clock proxy numerator. No such comparison is assumed.
-/

private theorem grantBlockTakeAppendLength {α : Type}
    (front back : List α) :
    (front ++ back).take front.length = front := by
  induction front with
  | nil =>
      rfl
  | cons e rest ih =>
      change e :: ((rest ++ back).take rest.length) = e :: rest
      rw [ih]

private theorem grantBlockTakeLengthSelf {α : Type}
    (word : List α) :
    word.take word.length = word := by
  simpa only [List.append_nil] using
    grantBlockTakeAppendLength word ([] : List α)

private theorem grantBlockTakeOfLengthLe {α : Type} :
    ∀ (word : List α) (W : Nat),
      word.length ≤ W → word.take W = word := by
  intro word
  induction word with
  | nil =>
      intro W _
      cases W <;> rfl
  | cons e rest ih =>
      intro W h
      cases W with
      | zero =>
          simp only [List.length_cons] at h
          omega
      | succ k =>
          have ht : rest.length ≤ k := by
            simp only [List.length_cons] at h
            omega
          change e :: rest.take k = e :: rest
          rw [ih k ht]

private theorem grantBlockTakeLength {α : Type} :
    ∀ (word : List α) (W : Nat),
      W ≤ word.length → (word.take W).length = W := by
  intro word W
  induction W generalizing word with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      cases word with
      | nil =>
          intro h
          simp only [List.length_nil] at h
          omega
      | cons e rest =>
          intro h
          have ht : k ≤ rest.length := by
            simp only [List.length_cons] at h
            omega
          change (rest.take k).length + 1 = k + 1
          rw [ih rest ht]

private theorem grantBlockSplitTakeDrop {α : Type} :
    ∀ (word : List α) (W : Nat),
      word = word.take W ++ word.drop W := by
  intro word W
  induction W generalizing word with
  | zero =>
      simp
  | succ k ih =>
      cases word with
      | nil =>
          rfl
      | cons e rest =>
          change e :: rest = e :: (rest.take k ++ rest.drop k)
          rw [← ih rest]

private theorem grantBlockRenewalSuccessByAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (limit : Nat) (front back : List (Fin n))
    (hlen : limit = front.length) :
    bankTrialRenewalSuccessBy ring root S limit (front ++ back) =
      bankTrialRenewalSuccessBy ring root S limit front := by
  rw [hlen]
  unfold bankTrialRenewalSuccessBy bankTrialRenewalHitWord
  rw [grantBlockTakeAppendLength, grantBlockTakeLengthSelf]

private theorem grantBlockColdProxyWeightAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (W : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (front back : List (Fin n))
    (hlen : cut.length + front.length = W) :
    bankTrialRenewalColdProxyWeight ring root W cut z
      (front ++ back) =
    bankTrialRenewalColdProxyWeight ring root W cut z front := by
  have hcut : cut.length ≤ W := by omega
  have hremain : W - cut.length = front.length := by omega
  have hsuccess (D : Counter.Config q n) :
      bankTrialRenewalSuccessBy ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (W - cut.length) (front ++ back) =
      bankTrialRenewalSuccessBy ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (W - cut.length) front :=
    grantBlockRenewalSuccessByAppend ring root
      (GrantBankReference.bankLocalReferenceStart ring root D)
      (W - cut.length) front back hremain
  cases z with
  | inl x =>
      simp [bankTrialRenewalColdProxyWeight, hcut]
  | inr y =>
      cases y with
      | inl a =>
          simp [bankTrialRenewalColdProxyWeight, hcut]
      | inr out =>
          rcases out with ⟨D, reason⟩
          cases reason with
          | grant =>
              simp [bankTrialRenewalColdProxyWeight, hcut]
          | defect =>
              simp [bankTrialRenewalColdProxyWeight, hcut]
          | clean =>
              by_cases hg : (D root).grant = true
              · simp [bankTrialRenewalColdProxyWeight, hcut, hg]
              · simp [bankTrialRenewalColdProxyWeight, hcut, hg,
                  hsuccess D]

private theorem grantBlockStoppedLateZero
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (W : Nat)
    (hLate : ∀ pre x t suffix,
      W < pre.length → A pre x t suffix = 0) :
    ∀ (word : List (Fin n)) t pre x,
      W < pre.length →
      bankTrialSuccessNatStoppedWord next stop A t pre x word = 0 := by
  intro word
  induction word with
  | nil =>
      intro t pre x hp
      cases hs : stop pre x with
      | false =>
          simp [bankTrialSuccessNatStoppedWord, hs]
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hLate pre x t [] hp)
  | cons e rest ih =>
      intro t pre x hp
      cases hs : stop pre x with
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hLate pre x t (e :: rest) hp)
      | false =>
          have hmore : W < (pre ++ [e]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (ih (t - 1) (pre ++ [e]) (next x e) hmore)

private theorem grantBlockStoppedCutZero
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (W : Nat)
    (hLate : ∀ pre x t suffix,
      W < pre.length → A pre x t suffix = 0)
    (t : Nat) (pre : List (Fin n)) (x : X)
    (word : List (Fin n))
    (hcut : W ≤ pre.length)
    (hs : stop pre x = false) :
    bankTrialSuccessNatStoppedWord next stop A
      t pre x word = 0 := by
  cases word with
  | nil =>
      simp [bankTrialSuccessNatStoppedWord, hs]
  | cons e rest =>
      have hmore : W < (pre ++ [e]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      simpa [bankTrialSuccessNatStoppedWord, hs] using
        (grantBlockStoppedLateZero next stop A W hLate
          rest (t - 1) (pre ++ [e]) (next x e) hmore)

private theorem grantBlockStoppedAtStop
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (t : Nat) (pre : List (Fin n)) (x : X)
    (word : List (Fin n))
    (hstop : stop pre x = true) :
    bankTrialSuccessNatStoppedWord next stop A
      t pre x word = A pre x t word := by
  cases word with
  | nil =>
      simp [bankTrialSuccessNatStoppedWord, hstop]
  | cons e rest =>
      simp [bankTrialSuccessNatStoppedWord, hstop]

private theorem grantBlockStoppedWindowAppend
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (W : Nat)
    (hwindow : ∀ pre x t u front back,
      pre.length + front.length = W →
        A pre x t (front ++ back) = A pre x u front)
    (hLate : ∀ pre x t suffix,
      W < pre.length → A pre x t suffix = 0) :
    ∀ (front back : List (Fin n)) t u pre x,
      pre.length + front.length = W →
      bankTrialSuccessNatStoppedWord next stop A
        t pre x (front ++ back) =
      bankTrialSuccessNatStoppedWord next stop A
        u pre x front := by
  intro front
  induction front with
  | nil =>
      intro back t u pre x hp
      have hcut : W ≤ pre.length := by
        simp only [List.length_nil, Nat.add_zero] at hp
        omega
      cases hs : stop pre x with
      | true =>
          have hleft := grantBlockStoppedAtStop
            next stop A t pre x back hs
          have hright := grantBlockStoppedAtStop
            next stop A u pre x [] hs
          have hweight := hwindow pre x t u [] back hp
          simpa only [List.nil_append, hleft, hright] using hweight
      | false =>
          have hleft := grantBlockStoppedCutZero
            next stop A W hLate t pre x back hcut hs
          have hright := grantBlockStoppedCutZero
            next stop A W hLate u pre x [] hcut hs
          simp only [List.nil_append, hleft, hright]
  | cons e rest ih =>
      intro back t u pre x hp
      cases hs : stop pre x with
      | true =>
          have hweight := hwindow pre x t u
            (e :: rest) back hp
          simpa [bankTrialSuccessNatStoppedWord, hs,
            List.cons_append] using hweight
      | false =>
          have htail :
              (pre ++ [e]).length + rest.length = W := by
            have h1 : (pre ++ [e]).length = pre.length + 1 := by
              simp
            have h2 : (e :: rest).length = rest.length + 1 := rfl
            rw [h2] at hp
            omega
          have hh := ih back (t - 1) (u - 1)
            (pre ++ [e]) (next x e) htail
          simpa [bankTrialSuccessNatStoppedWord, hs,
            List.cons_append] using hh

private theorem grantBlockStoppedClockIrrelevant
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (hclock : ∀ pre x t u suffix,
      A pre x t suffix = A pre x u suffix) :
    ∀ (word : List (Fin n)) t u pre x,
      bankTrialSuccessNatStoppedWord next stop A
        t pre x word =
      bankTrialSuccessNatStoppedWord next stop A
        u pre x word := by
  intro word
  induction word with
  | nil =>
      intro t u pre x
      cases hs : stop pre x with
      | false =>
          simp [bankTrialSuccessNatStoppedWord, hs]
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hclock pre x t u [])
  | cons e rest ih =>
      intro t u pre x
      cases hs : stop pre x with
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hclock pre x t u (e :: rest))
      | false =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (ih (t - 1) (u - 1) (pre ++ [e]) (next x e))

private theorem grantBlockFamilyProxyWordAppend
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (front back : List (Fin n))
    (hlen : front.length = W) :
    grantBlockFamilyProxyWord ring hsp member T W
      (front ++ back) =
    grantBlockFamilyProxyWord ring hsp member W W front := by
  unfold grantBlockFamilyProxyWord
  refine grantBlockStoppedWindowAppend
    (Counter.resetClockBankColdNext ring member.1 hsp)
    (bankTrialRenewalColdStop ring member.1)
    (fun cut z _ suffix =>
      bankTrialRenewalColdProxyWeight ring member.1 W cut z suffix)
    W ?_ ?_ front back T W []
    (Counter.resetClockBankColdStart ring member.1 member.2) ?_
  · intro cut z t u kept suffix hh
    exact grantBlockColdProxyWeightAppend
      ring member.1 W cut z kept suffix hh
  · intro cut z t suffix hh
    change bankTrialRenewalColdProxyWeight
      ring member.1 W cut z suffix = 0
    have hn : ¬ cut.length ≤ W := by omega
    simp [bankTrialRenewalColdProxyWeight, hn]
  · simpa only [List.length_nil, Nat.zero_add] using hlen

private theorem grantBlockFamilyProxyWordClockFree
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T U W : Nat) (word : List (Fin n)) :
    grantBlockFamilyProxyWord ring hsp member T W word =
      grantBlockFamilyProxyWord ring hsp member U W word := by
  unfold grantBlockFamilyProxyWord
  exact grantBlockStoppedClockIrrelevant
    (Counter.resetClockBankColdNext ring member.1 hsp)
    (bankTrialRenewalColdStop ring member.1)
    (fun cut z _ suffix =>
      bankTrialRenewalColdProxyWeight ring member.1 W cut z suffix)
    (by intro pre z t u suffix; rfl)
    word T U [] (Counter.resetClockBankColdStart ring member.1 member.2)

theorem grantBlockFamilyProxyHitPrefixWord
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) :
    grantBlockFamilyProxyHit ring hsp member T W word =
      grantBlockFamilyProxyHit ring hsp member W W (word.take W) := by
  unfold grantBlockFamilyProxyHit
  by_cases hlong : W ≤ word.length
  · have hlen : (word.take W).length = W :=
      grantBlockTakeLength word W hlong
    have hsplit : word = word.take W ++ word.drop W :=
      grantBlockSplitTakeDrop word W
    have hh :
        grantBlockFamilyProxyWord ring hsp member T W word =
          grantBlockFamilyProxyWord ring hsp member W W (word.take W) := by
      calc
        _ = grantBlockFamilyProxyWord ring hsp member T W
              (word.take W ++ word.drop W) :=
            congrArg (grantBlockFamilyProxyWord ring hsp member T W)
              hsplit
        _ = _ := grantBlockFamilyProxyWordAppend
          ring hsp member T W (word.take W) (word.drop W) hlen
    exact congrArg (fun k : Nat => decide (0 < k)) hh
  · have hs : word.length ≤ W := by omega
    have ht : word.take W = word :=
      grantBlockTakeOfLengthLe word W hs
    rw [ht]
    exact congrArg (fun k : Nat => decide (0 < k))
      (grantBlockFamilyProxyWordClockFree
        ring hsp member T W W word)

private theorem grantBlockScheduleZero
    (n : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n 0 f = f [] := by
  simp [Prob.scheduleSum, FixedSpanRenewalPayload.wordSum, allSchedules]

private theorem grantBlockScheduleConst
    (n T K : Nat) :
    Prob.scheduleSum n T (fun _ : List (Fin n) => K) =
      n ^ T * K := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun _ : List (Fin n) => K) = n ^ T * K
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  simp only [ofFn_sum_const]

private theorem grantBlockScheduleSucc
    (n T : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n T (fun w => f (e :: w)))).sum := by
  change FixedSpanRenewalPayload.wordSum n (T + 1) f = _
  rw [FixedSpanRenewalPayload.wordSum_succ]

private theorem grantBlockScheduleTakeMass
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
      rw [grantBlockScheduleZero]
      exact grantBlockScheduleConst n extra (f [])
  | succ W ih =>
      intro extra f
      have htotal : W + 1 + extra = (W + extra) + 1 := by omega
      calc
        Prob.scheduleSum n (W + 1 + extra)
          (fun word => f (word.take (W + 1))) =
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n (W + extra)
            (fun word => f (e :: word.take W)))).sum := by
              rw [htotal, grantBlockScheduleSucc]
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
            rw [grantBlockScheduleSucc]

theorem grantBlockFamilyProxyMassPrefix
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (hWT : W ≤ T) :
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit ring hsp member T W word
      then 1 else 0) =
    n ^ (T - W) *
      Prob.scheduleSum n W (fun word =>
        if grantBlockFamilyProxyHit ring hsp member W W word
        then 1 else 0) := by
  have htotal : W + (T - W) = T := Nat.add_sub_of_le hWT
  calc
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit ring hsp member T W word
      then 1 else 0) =
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit ring hsp member W W
        (word.take W) then 1 else 0) := by
          apply congrArg (Prob.scheduleSum n T)
          funext word
          rw [grantBlockFamilyProxyHitPrefixWord ring hsp member T W word]
    _ = Prob.scheduleSum n (W + (T - W)) (fun word =>
        if grantBlockFamilyProxyHit ring hsp member W W
          (word.take W) then 1 else 0) := by
          rw [htotal]
    _ = _ := grantBlockScheduleTakeMass W (T - W)
      (fun word =>
        if grantBlockFamilyProxyHit ring hsp member W W word
        then 1 else 0)

theorem grantBlockIncomingBoundaryDefectRead
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root predecessor : Fin n)
    (hpred : ring.rightNeighbor predecessor = root)
    (hbad : goodPair (compileAdvice q).b
        (C predecessor).pack (C root).pack = false) :
    Counter.ResetClockBankDefectEntry ring C root predecessor := by
  apply Counter.resetClockBankDefectOfBadPair
    ring C root predecessor (Or.inl hpred)
  simpa only [hpred] using hbad

/-- The frozen clamped BANK latch, not the physical cold observer.
It is deliberately evaluated on the boundary-inclusive support
subword, with all exterior Agent data excluded. -/
noncomputable def grantBlockFrozenProxyHit
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (word : List (Fin n)) : Bool :=
  (GrantBankReference.bankLocalReferenceWordClamped
    ring member.1
    (GrantBankReference.bankLocalReferenceSupportSubword
      (q := ceilLogTwo n) ring member.1 word)
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 member.2.val)).success

theorem grantBlockFrozenProxyHitLocality
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (word : List (Fin n)) :
    grantBlockFrozenProxyHit ring member
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := ceilLogTwo n) ring member.1 word) =
    grantBlockFrozenProxyHit ring member word := by
  unfold grantBlockFrozenProxyHit
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring member.1
    (GrantBankReference.bankLocalReferenceSupportSubword
      (q := ceilLogTwo n) ring member.1 word)
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 member.2.val)]

theorem grantBlockFrozenProxyHitOfSubwordEq
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (u v : List (Fin n))
    (h : GrantBankReference.bankLocalReferenceSupportSubword
        (q := ceilLogTwo n) ring member.1 u =
      GrantBankReference.bankLocalReferenceSupportSubword
        (q := ceilLogTwo n) ring member.1 v) :
    grantBlockFrozenProxyHit ring member u =
      grantBlockFrozenProxyHit ring member v := by
  unfold grantBlockFrozenProxyHit
  rw [h]

theorem grantBlockFrozenProxyHitPrefix
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (u v : List (Fin n))
    (hs : grantBlockFrozenProxyHit ring member u = true) :
    grantBlockFrozenProxyHit ring member (u ++ v) = true := by
  have hfull :
      (GrantBankReference.bankLocalReferenceWordClamped
        ring member.1 u
        (GrantBankReference.bankLocalReferenceStart
          ring member.1 member.2.val)).success = true := by
    have hh := hs
    change
      (GrantBankReference.bankLocalReferenceWordClamped
        ring member.1
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := ceilLogTwo n) ring member.1 u)
        (GrantBankReference.bankLocalReferenceStart
          ring member.1 member.2.val)).success = true at hh
    rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
      ring member.1 u
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)] at hh
    exact hh
  change
    (GrantBankReference.bankLocalReferenceWordClamped
      ring member.1
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := ceilLogTwo n) ring member.1 (u ++ v))
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)).success = true
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring member.1 (u ++ v)
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 member.2.val)]
  rw [GrantBankReference.bankLocalReferenceWordAppendClamped
    ring member.1 u v
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 member.2.val)]
  rw [GrantBankReference.bankLocalReferenceLatchedWordClamped
    ring member.1 v
    (GrantBankReference.bankLocalReferenceWordClamped
      ring member.1 u
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)) hfull]
  exact hfull

/-- Original n-ary length-T mass of frozen success by wall time W. -/
noncomputable def grantBlockFrozenProxyMass
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if grantBlockFrozenProxyHit ring member (word.take W)
    then 1 else 0)

/-- A frozen first-success letter with a physical SafeWord
proper prefix. SafeWord MUST NOT be demanded through the hit
letter, since it includes NoRootSuccessWord. -/
def GrantBlockFrozenSafeFirstHit
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ e : Fin n, ∃ suffix : List (Fin n),
    word.take W = pre ++ e :: suffix ∧
    GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val pre ∧
    grantBlockFrozenProxyHit ring member pre = false ∧
    grantBlockFrozenProxyHit ring member (pre ++ [e]) = true

/-- An unsafe frozen hit is a frozen success with no certified
safe proper-prefix first-hit witness. This is more conservative
than the G14 cold DEFECT event, and is not identified with it. -/
noncomputable def grantBlockFrozenUnsafeBeforeHit
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n)) : Bool :=
  decide (grantBlockFrozenProxyHit
      ring member (word.take W) = true ∧
    ¬ GrantBlockFrozenSafeFirstHit ring member W word)

noncomputable def grantBlockFrozenUnsafeMass
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if grantBlockFrozenUnsafeBeforeHit ring member W word
    then 1 else 0)

/-- CONDITIONAL physical/frozen comparison. The stated hbridge
is an explicit missing physical stopping-time refinement, not a
proved fact or a hidden assumed leaf. The source theorems
bankTrialRenewalFrozenSafePhysicalPrefix and
bankTrialRenewalFrozenFirstPhysicalSuccess do not by themselves
supply the needed implication to grantBlockFamilyProxyHit. -/
theorem grantBlockPhysicalProxyMassGeFrozen
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat)
    (hbridge : ∀ word : List (Fin n),
      GrantBlockFrozenSafeFirstHit ring member W word →
        grantBlockFamilyProxyHit
          ring hsp member T W word = true) :
    grantBlockFrozenProxyMass ring member T W -
      grantBlockFrozenUnsafeMass ring member T W ≤
    bankTrialRenewalColdProxyMass
      ring member.1 hsp member.2 T W := by
  have hpoint (word : List (Fin n)) :
      (if grantBlockFrozenProxyHit
          ring member (word.take W) then 1 else 0) ≤
      (if grantBlockFamilyProxyHit
          ring hsp member T W word then 1 else 0) +
      (if grantBlockFrozenUnsafeBeforeHit
          ring member W word then 1 else 0) := by
    by_cases hf :
        grantBlockFrozenProxyHit
          ring member (word.take W) = true
    · by_cases hs :
          GrantBlockFrozenSafeFirstHit ring member W word
      · have hp := hbridge word hs
        simp [hf, hp, grantBlockFrozenUnsafeBeforeHit, hs]
      · have hu :
            grantBlockFrozenUnsafeBeforeHit
              ring member W word = true := by
          simp [grantBlockFrozenUnsafeBeforeHit, hf, hs]
        simp [hf, hu]
    · have hb :
          grantBlockFrozenProxyHit
            ring member (word.take W) = false := by
        cases hh :
            grantBlockFrozenProxyHit ring member (word.take W) with
        | false => rfl
        | true => exact False.elim (hf hh)
      simp [hb]
  have hsum := Density.schedule_sum_mono T
    (fun word =>
      if grantBlockFrozenProxyHit ring member (word.take W)
      then 1 else 0)
    (fun word =>
      (if grantBlockFamilyProxyHit
        ring hsp member T W word then 1 else 0) +
      (if grantBlockFrozenUnsafeBeforeHit
        ring member W word then 1 else 0)) hpoint
  rw [grantBlockScheduleAdd] at hsum
  change
    grantBlockFrozenProxyMass ring member T W ≤
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit
        ring hsp member T W word then 1 else 0) +
    grantBlockFrozenUnsafeMass ring member T W at hsum
  rw [grantBlockFamilyProxyMassEq ring hsp member T W] at hsum
  omega

/-- CONDITIONAL reduction to the existing G14 crossing estimate.
The unproved hUnsafeCross is precisely the extra attribution
needed; G14 itself bounds cold DEFECT mass via
bankTrialRenewalColdDefectCrossingBound, not arbitrary failure
of GrantBankReference.bankLocalReferenceSafeWord. -/
theorem grantBlockFrozenUnsafeCrossingBound
    {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (radius W T : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring member.2.val radius member.1)
    (hWT : W ≤ T)
    (hwindow : W ≤ radius * n / 8)
    (hUnsafeCross : ∀ word : List (Fin n),
      grantBlockFrozenUnsafeBeforeHit
        ring member W word = true →
      DefectCrossingEntryWithin ring member.2.val member.1
        (word.take W)) :
    8 ^ radius * grantBlockFrozenUnsafeMass
        ring member T W ≤
      Density.N (badSet ring member.2.val) *
        3 ^ radius * n ^ T := by
  have hmass :
      grantBlockFrozenUnsafeMass ring member T W ≤
      Prob.scheduleSum n T (fun word =>
        if DefectCrossingEntryWithin
          ring member.2.val member.1 (word.take W)
        then 1 else 0) := by
    unfold grantBlockFrozenUnsafeMass
    apply Density.schedule_sum_mono T
    intro word
    by_cases hu :
        grantBlockFrozenUnsafeBeforeHit
          ring member W word = true
    · have hc := hUnsafeCross word hu
      simp [hu, hc]
    · cases hz :
          grantBlockFrozenUnsafeBeforeHit ring member W word with
      | false =>
          simp [hz]
      | true =>
          exact False.elim (hu hz)
  have hcross := defectCrossingMass hn ring member.2.val
    member.1 radius W T hBuffered hWT hwindow
  exact Nat.le_trans
    (Nat.mul_le_mul_left (8 ^ radius) hmass) hcross

end L3

#print axioms L3.grantBlockSupportSubwordOutside
#print axioms L3.grantBlockPairNegativeCorrelation
#print axioms L3.grantBlockOppositeChebyshev
#print axioms L3.grantBlockFamilyUnionLowerArithmetic
#print axioms L3.grantBlockFamilyUnionLower
#print axioms L3.grantBlockFamilyProxyHitPrefixWord
#print axioms L3.grantBlockFrozenProxyHitLocality
#print axioms L3.grantBlockFrozenProxyHitPrefix
#print axioms L3.grantBlockPhysicalProxyMassGeFrozen
#print axioms L3.grantBlockFrozenUnsafeCrossingBound
