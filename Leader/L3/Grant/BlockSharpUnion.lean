import Leader.L3.Grant.BlockFamilyRate
import Leader.L3.Grant.Cutoffs

/-!
# G18: the sharp C.17 union bound on a prefix subfamily

`grantBlockFamilyUnionLower` proves `min(N, 2S) ≤ 4U`, which loses a factor 2
against the paper.  Here the paper's C.17 is proved: for a family of events
with the Bonferroni inequality, pairwise negative correlation on prefixes,
monotone unions and `mass ≤ union`, and a threshold `Λ` with
`2048 Λ ≤ B N`,

`2047 * min (B S) Λ ≤ 2048 * (B U)`.

The proof takes the whole family when `B S < Λ`, a single member when some
`B mass ≥ Λ`, and otherwise a prefix whose scaled sum lies in `[Λ, 2Λ)`; on a
piece with `1024 S ≤ N` the Bonferroni inequality and `2 Σ_{i<j} m_i m_j ≤ S²`
give `2047 S ≤ 2048 U`.  The private event helpers of `GrantBlockNegCorr.lean`
are re-proved here.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ### Abstract arithmetic -/

/-- On a piece with `1024 S ≤ N`, Bonferroni and the pair-product bound give
`2047 S ≤ 2048 U`.

Consumer: `grantBlockSharpUnionArithmetic`. -/
theorem grantBlockSharpSmallPiece
    (N S U P prod : Nat) (hN : 0 < N)
    (hSmall : 1024 * S ≤ N)
    (hBonf : S ≤ U + P)
    (hPair : N * P ≤ prod)
    (hProd : 2 * prod ≤ S * S) :
    2047 * S ≤ 2048 * U := by
  have hFirst : N * S ≤ N * U + prod := by
    have h := Nat.mul_le_mul_left N hBonf
    rw [Nat.mul_add] at h
    omega
  have hSq : 1024 * (S * S) ≤ S * N := by
    have h := Nat.mul_le_mul_left S hSmall
    have e : S * (1024 * S) = 1024 * (S * S) := by ac_rfl
    omega
  have hProd2 : 2048 * prod ≤ S * N := by omega
  have hSN : S * N = N * S := Nat.mul_comm _ _
  have hScaled : N * (2047 * S) ≤ N * (2048 * U) := by
    have e1 : N * (2047 * S) = 2047 * (N * S) := by ac_rfl
    have e2 : N * (2048 * U) = 2048 * (N * U) := by ac_rfl
    rw [e1, e2]
    omega
  exact Nat.le_of_mul_le_mul_left hScaled hN

/-- A prefix of scaled sum in `[Λ, 2Λ)` when every member is below `Λ`.

Consumer: `grantBlockSharpUnionArithmetic`. -/
theorem grantBlockSharpPrefixWalk
    {α : Type} (mass : α → Nat) (B Λ : Nat) :
    ∀ (xs : List α) (acc : Nat),
      B * acc < Λ →
      Λ ≤ B * (acc + (xs.map mass).sum) →
      (∀ x : α, x ∈ xs → B * mass x < Λ) →
      ∃ pre rest : List α,
        xs = pre ++ rest ∧
        Λ ≤ B * (acc + (pre.map mass).sum) ∧
        B * (acc + (pre.map mass).sum) < 2 * Λ := by
  intro xs
  induction xs with
  | nil =>
      intro acc hBefore hTotal _
      simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hTotal
      omega
  | cons x xs ih =>
      intro acc hBefore hTotal hEach
      have hx := hEach x List.mem_cons_self
      by_cases hreach : Λ ≤ B * (acc + mass x)
      · refine ⟨[x], xs, rfl, ?_, ?_⟩
        · simpa using hreach
        · simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, Nat.add_zero]
          rw [Nat.mul_add]
          omega
      · have hnext : B * (acc + mass x) < Λ := by omega
        have htotal : Λ ≤ B * ((acc + mass x) +
            (xs.map mass).sum) := by
          simp only [List.map_cons, List.sum_cons] at hTotal
          have e : acc + (mass x + (xs.map mass).sum) =
              (acc + mass x) + (xs.map mass).sum := by omega
          rw [e] at hTotal
          exact hTotal
        obtain ⟨pre, rest, hsplit, hlow, hhigh⟩ := ih (acc + mass x)
          hnext htotal
          (fun y hy => hEach y (List.mem_cons_of_mem x hy))
        refine ⟨x :: pre, rest, ?_, ?_, ?_⟩
        · rw [hsplit]
          rfl
        · simp only [List.map_cons, List.sum_cons]
          have e : acc + (mass x + (pre.map mass).sum) =
              (acc + mass x) + (pre.map mass).sum := by omega
          rw [e]
          exact hlow
        · simp only [List.map_cons, List.sum_cons]
          have e : acc + (mass x + (pre.map mass).sum) =
              (acc + mass x) + (pre.map mass).sum := by omega
          rw [e]
          exact hhigh

/-- **Sharp union, abstract form.**  With `2048 Λ ≤ B N`,
`2047 min(B S, Λ) ≤ 2048 B U`.

Consumer: `grantBlockFrozenFamilySharpUnion`. -/
theorem grantBlockSharpUnionArithmetic
    {α : Type} (N B Λ : Nat) (mass : α → Nat)
    (unionMass pairMass : List α → Nat) (family : List α)
    (hN : 0 < N) (hB : 0 < B)
    (hBonf : ∀ xs : List α,
      (xs.map mass).sum ≤ unionMass xs + pairMass xs)
    (hPair : ∀ pre rest : List α, family = pre ++ rest →
      N * pairMass pre ≤ grantBlockPairProducts mass pre)
    (hPrefix : ∀ pre rest : List α,
      unionMass pre ≤ unionMass (pre ++ rest))
    (hMember : ∀ x : α, x ∈ family → mass x ≤ unionMass family)
    (hCap : 2048 * Λ ≤ B * N) :
    2047 * min (B * (family.map mass).sum) Λ ≤
      2048 * (B * unionMass family) := by
  have piece : ∀ pre rest : List α, family = pre ++ rest →
      1024 * (pre.map mass).sum ≤ N →
      2047 * (pre.map mass).sum ≤ 2048 * unionMass pre := by
    intro pre rest hsplit hsmall
    exact grantBlockSharpSmallPiece N (pre.map mass).sum
      (unionMass pre) (pairMass pre)
      (grantBlockPairProducts mass pre) hN hsmall (hBonf pre)
      (hPair pre rest hsplit) (grantBlockPairProductsSquare mass pre)
  by_cases hsmall : B * (family.map mass).sum < Λ
  · have hcap : 1024 * (family.map mass).sum ≤ N := by
      have h1 : B * (1024 * (family.map mass).sum) ≤ B * N := by
        have e : B * (1024 * (family.map mass).sum) =
            1024 * (B * (family.map mass).sum) := by ac_rfl
        rw [e]
        omega
      exact Nat.le_of_mul_le_mul_left h1 hB
    have h := piece family [] (by simp) hcap
    rw [Nat.min_eq_left (Nat.le_of_lt hsmall)]
    have h2 := Nat.mul_le_mul_left B h
    have e1 : B * (2047 * (family.map mass).sum) =
        2047 * (B * (family.map mass).sum) := by ac_rfl
    have e2 : B * (2048 * unionMass family) =
        2048 * (B * unionMass family) := by ac_rfl
    rw [e1, e2] at h2
    exact h2
  · have hbig : Λ ≤ B * (family.map mass).sum := by omega
    rw [Nat.min_eq_right hbig]
    rcases Nat.eq_zero_or_pos Λ with h0 | hΛ
    · rw [h0]
      omega
    by_cases hsingle : ∃ x : α, x ∈ family ∧ Λ ≤ B * mass x
    · obtain ⟨x, hx, hxbig⟩ := hsingle
      have h1 := Nat.mul_le_mul_left B (hMember x hx)
      omega
    · have hEach : ∀ x : α, x ∈ family → B * mass x < Λ := by
        intro x hx
        by_cases h : Λ ≤ B * mass x
        · exact False.elim (hsingle ⟨x, hx, h⟩)
        · omega
      obtain ⟨pre, rest, hsplit, hlow, hhigh⟩ :=
        grantBlockSharpPrefixWalk mass B Λ family 0
          (by omega) (by simpa using hbig) hEach
      simp only [Nat.zero_add] at hlow hhigh
      have hcap : 1024 * (pre.map mass).sum ≤ N := by
        have h1 : B * (1024 * (pre.map mass).sum) ≤ B * N := by
          have e : B * (1024 * (pre.map mass).sum) =
              1024 * (B * (pre.map mass).sum) := by ac_rfl
          rw [e]
          omega
        exact Nat.le_of_mul_le_mul_left h1 hB
      have h := piece pre rest hsplit hcap
      have hmono : unionMass pre ≤ unionMass family := by
        rw [hsplit]
        exact hPrefix pre rest
      have h2 : 2047 * (pre.map mass).sum ≤ 2048 * unionMass family :=
        Nat.le_trans h (Nat.mul_le_mul_left 2048 hmono)
      have h3 := Nat.mul_le_mul_left B h2
      have e1 : B * (2047 * (pre.map mass).sum) =
          2047 * (B * (pre.map mass).sum) := by ac_rfl
      have e2 : B * (2048 * unionMass family) =
          2048 * (B * unionMass family) := by ac_rfl
      rw [e1, e2] at h3
      omega

/-! ### Event helpers (the private lemmas of `GrantBlockNegCorr.lean`) -/

/-- Consumer: `sharpEventUnionPrefix`. -/
private theorem sharpAnyAppend
    {α : Type} (hit : α → Bool) (xs ys : List α) :
    grantBlockFamilyAny hit (xs ++ ys) =
      (grantBlockFamilyAny hit xs || grantBlockFamilyAny hit ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [grantBlockFamilyAny, ih, Bool.or_assoc]

/-- Consumer: `grantBlockFrozenFamilySharpUnion`. -/
private theorem sharpEventUnionPrefix
    {α : Type} (n T : Nat) (hit : α → List (Fin n) → Bool)
    (xs ys : List α) :
    grantBlockEventUnion n T hit xs ≤
      grantBlockEventUnion n T hit (xs ++ ys) := by
  unfold grantBlockEventUnion
  apply Density.schedule_sum_mono T
  intro w
  rw [sharpAnyAppend]
  cases hh : grantBlockFamilyAny (fun x => hit x w) xs <;>
    simp [hh]

/-- Consumer: `sharpEventMemberMassLe`. -/
private theorem sharpAnyOfMem
    {α : Type} (hit : α → Bool) (xs : List α) (x : α)
    (hx : x ∈ xs) (hh : hit x = true) :
    grantBlockFamilyAny hit xs = true := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with he | he
      · subst y
        simp [grantBlockFamilyAny, hh]
      · by_cases hy : hit y = true
        · simp [grantBlockFamilyAny, hy]
        · have hrest := ih he
          simpa [grantBlockFamilyAny, hy] using hrest

/-- Consumer: `grantBlockFrozenFamilySharpUnion`. -/
private theorem sharpEventMemberMassLe
    {α : Type} (n T : Nat) (hit : α → List (Fin n) → Bool)
    (xs : List α) (x : α) (hx : x ∈ xs) :
    grantBlockEventMass n T hit x ≤
      grantBlockEventUnion n T hit xs := by
  unfold grantBlockEventMass grantBlockEventUnion
  apply Density.schedule_sum_mono T
  intro w
  by_cases h : hit x w = true
  · have hh := sharpAnyOfMem (fun y => hit y w) xs x hx h
    simp [h, hh]
  · simp [h]

/-- Consumer: `sharpScheduleMapSum`. -/
private theorem sharpScheduleConstZero (n T : Nat) :
    Prob.scheduleSum n T (fun _ : List (Fin n) => 0) = 0 := by
  change FixedSpanRenewalPayload.wordSum n T
    (fun _ : List (Fin n) => 0) = 0
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  simp only [ofFn_sum_const, Nat.mul_zero]

/-- Consumer: `sharpScheduleMapSum`. -/
private theorem sharpScheduleAdd
    (n T : Nat) (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => f w + g w) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum,
    ← FixedSpanRenewalPayload.rawWord_sum,
    ← FixedSpanRenewalPayload.rawWord_sum]
  exact ofFn_sum_add _ _

/-- Consumer: `sharpEventPairsCons`. -/
private theorem sharpScheduleMapSum
    {α : Type} (n T : Nat) (xs : List α)
    (f : α → List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => (xs.map (fun x => f x w)).sum) =
      (xs.map (fun x => Prob.scheduleSum n T (f x))).sum := by
  induction xs with
  | nil => exact sharpScheduleConstZero n T
  | cons x xs ih =>
      change Prob.scheduleSum n T
          (fun w => f x w + (xs.map (fun y => f y w)).sum) =
        Prob.scheduleSum n T (f x) +
          (xs.map (fun y => Prob.scheduleSum n T (f y))).sum
      rw [sharpScheduleAdd, ih]

/-- Consumer: `sharpEventPairsCons`. -/
private theorem sharpIntersectionWord
    {α : Type} (hit : α → Bool) (x : α) :
    ∀ xs : List α,
      (if hit x then grantBlockFamilyHits hit xs else 0) =
      (xs.map (fun y => if hit x && hit y then 1 else 0)).sum := by
  intro xs
  induction xs with
  | nil => cases hh : hit x <;> rfl
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
          exact congrArg (fun z => (if hit y then 1 else 0) + z) htail

/-- Consumer: `sharpEventPairsProductBound`. -/
private theorem sharpEventPairsCons
    {α : Type} (n T : Nat) (hit : α → List (Fin n) → Bool)
    (x : α) (xs : List α) :
    grantBlockEventPairs n T hit (x :: xs) =
      (xs.map (fun y => grantBlockEventIntersection n T hit x y)).sum +
      grantBlockEventPairs n T hit xs := by
  unfold grantBlockEventPairs
  change Prob.scheduleSum n T
      (fun w =>
        (if hit x w then
          grantBlockFamilyHits (fun y => hit y w) xs else 0) +
        grantBlockFamilyPairs (fun y => hit y w) xs) = _
  rw [sharpScheduleAdd]
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
              exact sharpIntersectionWord (fun y => hit y w) x xs
      _ = _ := sharpScheduleMapSum n T xs _
  rw [hfirst]

/-- Consumer: `sharpEventPairsProductBound`. -/
private theorem sharpMappedProductBound
    {α : Type} (N a : Nat) (f g : α → Nat) :
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
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add] at *
      omega

/-- Consumer: `grantBlockFrozenFamilySharpUnion`. -/
private theorem sharpNodupPrefix {α : Type} :
    ∀ (pre rest : List α), (pre ++ rest).Nodup → pre.Nodup := by
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

/-- Consumer: `grantBlockFrozenFamilySharpUnion`. -/
private theorem sharpEventPairsProductBound
    {α : Type} (n T : Nat) (hit : α → List (Fin n) → Bool) :
    ∀ xs : List α, xs.Nodup →
      (∀ x : α, x ∈ xs → ∀ y : α, y ∈ xs → x ≠ y →
        n ^ T * grantBlockEventIntersection n T hit x y ≤
          grantBlockEventMass n T hit x *
            grantBlockEventMass n T hit y) →
      n ^ T * grantBlockEventPairs n T hit xs ≤
        grantBlockPairProducts (grantBlockEventMass n T hit) xs := by
  intro xs
  induction xs with
  | nil =>
      intro _ _
      change n ^ T * Prob.scheduleSum n T
        (fun _ : List (Fin n) => 0) ≤ 0
      rw [sharpScheduleConstZero]
      omega
  | cons x xs ih =>
      intro hNodup hNeg
      have hSplit := List.nodup_cons.mp hNodup
      have hfirst :
          n ^ T * (xs.map (fun y =>
            grantBlockEventIntersection n T hit x y)).sum ≤
          grantBlockEventMass n T hit x *
            (xs.map (grantBlockEventMass n T hit)).sum := by
        apply sharpMappedProductBound (n ^ T)
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
          grantBlockPairProducts (grantBlockEventMass n T hit) xs := by
        apply ih hSplit.2
        intro y hy z hz hne
        exact hNeg y (List.mem_cons_of_mem _ hy)
          z (List.mem_cons_of_mem _ hz) hne
      rw [sharpEventPairsCons]
      change n ^ T *
        ((xs.map (fun y =>
          grantBlockEventIntersection n T hit x y)).sum +
          grantBlockEventPairs n T hit xs) ≤
        grantBlockEventMass n T hit x *
          (xs.map (grantBlockEventMass n T hit)).sum +
          grantBlockPairProducts (grantBlockEventMass n T hit) xs
      rw [Nat.mul_add]
      omega

/-! ### The frozen family -/

/-- **Sharp union on the frozen family of selected roots.**  With
`2048 Λ ≤ B n^T`,
`2047 min(B Σ mass, Λ) ≤ 2048 B (union mass)`.

Consumer: `grantBlockSharpFamilyRate`. -/
theorem grantBlockFrozenFamilySharpUnion
    {n : Nat} (ring : DirectedRing n) (hn : 0 < n)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
           Counter.Support (ceilLogTwo n) ring other e))
    (family : List (GrantBlockFamilyMember ring))
    (hnodup : family.Nodup)
    (hfamily : ∀ member, member ∈ family → member.1 ∈ selected)
    (hrootDistinct : ∀ left, left ∈ family →
      ∀ right, right ∈ family → left ≠ right → left.1 ≠ right.1)
    (T W : Nat) (hWT : W ≤ T) (B Λ : Nat) (hB : 0 < B)
    (hCap : 2048 * Λ ≤ B * n ^ T) :
    2047 * min (B * (family.map (grantBlockEventMass n T
        (fun member word =>
          grantBlockFrozenProxyHit ring member (word.take W)))).sum) Λ ≤
      2048 * (B * grantBlockEventUnion n T
        (fun member word =>
          grantBlockFrozenProxyHit ring member (word.take W))
        family) := by
  apply grantBlockSharpUnionArithmetic (n ^ T) B Λ
    (grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W)))
    (grantBlockEventUnion n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W)))
    (grantBlockEventPairs n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W)))
    family (Nat.pow_pos hn) hB
  · intro xs
    exact grantBlockFamilyBonferroniMass n T xs
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
  · intro pre rest hPiece
    have hPrefixNodup : pre.Nodup := by
      have hAll : (pre ++ rest).Nodup := by
        rw [← hPiece]
        exact hnodup
      exact sharpNodupPrefix pre rest hAll
    apply sharpEventPairsProductBound
      n T _ pre hPrefixNodup
    intro x hx y hy hne
    have hxf : x ∈ family := by
      rw [hPiece]
      exact List.mem_append_left _ hx
    have hyf : y ∈ family := by
      rw [hPiece]
      exact List.mem_append_left _ hy
    exact grantBlockFrozenPairNegativeCorrelation
      ring selected hselected x y (hfamily x hxf) (hfamily y hyf)
      (hrootDistinct x hxf y hyf hne) T W hWT
  · intro pre rest
    exact sharpEventUnionPrefix n T _ pre rest
  · intro x hx
    exact sharpEventMemberMassLe n T _ family x hx
  · exact hCap

end L3

#print axioms L3.grantBlockSharpSmallPiece
#print axioms L3.grantBlockSharpPrefixWalk
#print axioms L3.grantBlockSharpUnionArithmetic
#print axioms L3.grantBlockFrozenFamilySharpUnion
