import Leader.L3.Grant.BlockSurrogateFrozen

/-!
G16 C.17 prefix-only pair negative dependence.

The insertion-monotone theorem is not a
prefix-monotone theorem: prepending an individual supported
letter can reduce the chance of a prefix event. A valid new
induction needs the aggregate over ALL supported letters,
not termwise monotonicity.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Genuine boundary-inclusive scheduler-letter support for a
member, expressed as the Boolean expected by the G16 counting
interface. This does not inspect the member's full Agent state. -/
noncomputable def grantBlockFrozenEdgeSupport {n : Nat}
    (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (edge : Fin n) : Bool :=
  decide (Counter.Support (ceilLogTwo n) ring member.1 edge)

/-- The frozen event literally factors through its support
subword, using the already-proved clamped-reference locality. -/
theorem grantBlockFrozenLocalOfSupport
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (word : List (Fin n)) :
    grantBlockFrozenProxyHit ring member
      (grantBlockSupportSubword
        (grantBlockFrozenEdgeSupport ring member) word) =
    grantBlockFrozenProxyHit ring member word := by
  change
    grantBlockFrozenProxyHit ring member
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := ceilLogTwo n) ring member.1 word) =
      grantBlockFrozenProxyHit ring member word
  exact grantBlockFrozenProxyHitLocality ring member word

/-- Prefix monotonicity, without any insertion premise. -/
theorem grantBlockFrozenPrefixProperty
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) :
    GrantBlockPrefixMonotone
      (grantBlockFrozenProxyHit ring member) := by
  intro u v hu
  exact grantBlockFrozenProxyHitPrefix ring member u v hu

/-- The exact geometric input when the roots were selected by
C.9--C.10. Member inequality alone is NOT a root-separation
certificate: the list type is a Sigma of carriers, and arbitrary
nearby roots have overlapping boundary-inclusive supports. -/
theorem grantBlockFrozenPairDisjointOfSelected
    {n : Nat} (ring : DirectedRing n)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ edge : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root edge ∧
           Counter.Support (ceilLogTwo n) ring other edge))
    (left right : GrantBlockFamilyMember ring)
    (hl : left.1 ∈ selected) (hr : right.1 ∈ selected)
    (hne : left.1 ≠ right.1) :
    ∀ edge : Fin n,
      ¬ (grantBlockFrozenEdgeSupport ring left edge = true ∧
         grantBlockFrozenEdgeSupport ring right edge = true) := by
  intro edge h
  exact hselected left.1 right.1 hl hr hne edge
    ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- Two ADJACENT roots can share a supported edge. This is a
literal geometric witness showing why "different roots" cannot
replace the selected-root hDisjoint. The three-site geometry
is only a support witness, not an assertion that an arbitrary
three-site configuration is a complete G13 cold carrier. -/
theorem grantBlockAdjacentRootsOverlap (q : Nat) :
    Counter.Support q
      (⟨by decide⟩ : DirectedRing 3)
      (0 : Fin 3) (1 : Fin 3) ∧
    Counter.Support q
      (⟨by decide⟩ : DirectedRing 3)
      (1 : Fin 3) (1 : Fin 3) := by
  have hb : 1 ≤ (compileAdvice q).b := by
    change 1 ≤ (compileAdvice q).s + 11
    omega
  constructor
  · exact Or.inr ⟨1, hb, rfl⟩
  · exact Or.inr ⟨0, Nat.zero_le _, rfl⟩

/-- The exact scalar covariance inequality needed AFTER the
category-sum decomposition. Variables are deliberately opaque:
no population powers are passed to the arithmetic solver. -/
private theorem grantBlockAggregateCovarianceArithmetic
    (n a b gainA gainB : Nat) :
    n * (n * a * b + gainA * b + gainB * a) ≤
      (n * a + gainA) * (n * b + gainB) := by
  have h :
      (n * a + gainA) * (n * b + gainB) =
        n * (n * a * b + gainA * b + gainB * a) +
          gainA * gainB := by
    simp only [Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [h]
  exact Nat.le_add_right _ _

/-- A minimal prefix event: whether the FIRST supported symbol
is zero. Its true value is absorbing under suffix extension. -/
def grantBlockFirstSymbolHit (word : List (Fin 3)) : Bool :=
  match word with
  | [] => false
  | edge :: _ => decide (edge = (0 : Fin 3))

theorem grantBlockFirstSymbolPrefix :
    GrantBlockPrefixMonotone grantBlockFirstSymbolHit := by
  intro u v hu
  cases u with
  | nil =>
      change false = true at hu
      cases hu
  | cons edge rest =>
      change decide (edge = (0 : Fin 3)) = true at hu
      change decide (edge = (0 : Fin 3)) = true
      exact hu

/-- A literal pointwise obstruction to reusing
grantBlockPairNegativeCorrelation: inserting supported 1
before the successful word [0] destroys the event.
Aggregate-count monotonicity, not insertion monotonicity,
is the missing finite combinatorial input. -/
theorem grantBlockFirstSymbolNotInsertion :
    ¬ GrantBlockInsertionMonotone
      (fun edge : Fin 3 => decide (edge ≠ (2 : Fin 3)))
      grantBlockFirstSymbolHit := by
  intro h
  have hsupport :
      (fun edge : Fin 3 => decide (edge ≠ (2 : Fin 3)))
        (1 : Fin 3) = true := by decide
  have hsuccess :
      grantBlockFirstSymbolHit [(0 : Fin 3)] = true := by decide
  have hbad := h [] [(0 : Fin 3)] (1 : Fin 3)
    hsupport hsuccess
  change grantBlockFirstSymbolHit
    [(1 : Fin 3), (0 : Fin 3)] = true at hbad
  have hfalse :
      grantBlockFirstSymbolHit
        [(1 : Fin 3), (0 : Fin 3)] = false := by decide
  rw [hfalse] at hbad
  cases hbad

/-- The trivial horizon of the desired pair count is exact.
The general T+1 step is not obtained by the old insertion
argument: the two individual conditional masses need not
be ordered after a fixed supported letter. -/
theorem grantBlockPairPrefixEmptyExact
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool) :
    grantBlockLocalPairMass s t a b 0 * n ^ 0 =
      grantBlockLocalMass s a 0 *
        grantBlockLocalMass t b 0 := by
  simp [grantBlockLocalPairMass, grantBlockLocalMass,
    grantBlockLocalHit, grantBlockSupportSubword,
    Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
    allSchedules]
  by_cases ha : a [] = true <;> by_cases hb : b [] = true <;>
    simp [ha, hb]


/-- Prefix-history form of the original-scheduler numerator.
The local history is kept OUTSIDE the next scheduler subsequence;
this is why first-letter induction remains possible without
assuming insertion monotonicity of the base event. -/
noncomputable def grantBlockPrefixHistoryMass
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (history : List (Fin n)) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if success
      (history ++ grantBlockSupportSubword support word)
    then 1 else 0)

noncomputable def grantBlockPrefixHistoryPairMass
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (left right : List (Fin n)) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if a (left ++ grantBlockSupportSubword s word) &&
       b (right ++ grantBlockSupportSubword t word)
    then 1 else 0)

/-- The definition coincides with the existing G16 mass at the
empty prefix. -/
theorem grantBlockPrefixHistoryMassEmpty
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool) (T : Nat) :
    grantBlockPrefixHistoryMass support success [] T =
      grantBlockLocalMass support success T := by
  unfold grantBlockPrefixHistoryMass
    grantBlockLocalMass grantBlockLocalHit
  simp only [List.nil_append]

theorem grantBlockPrefixHistoryPairMassEmpty
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool) (T : Nat) :
    grantBlockPrefixHistoryPairMass s t a b [] [] T =
      grantBlockLocalPairMass s t a b T := by
  unfold grantBlockPrefixHistoryPairMass
    grantBlockLocalPairMass grantBlockLocalHit
  simp only [List.nil_append]

/-- Exact first-letter recursion with a left-side local history.
The forbidden "insert arbitrary letter in a completed word"
step is never used. -/
theorem grantBlockPrefixHistoryMassSucc
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool)
    (history : List (Fin n)) (T : Nat) :
    grantBlockPrefixHistoryMass
      support success history (T + 1) =
      (List.ofFn (fun e : Fin n =>
        grantBlockPrefixHistoryMass support success
          (history ++ (if support e then [e] else [])) T)).sum := by
  unfold grantBlockPrefixHistoryMass
  change FixedSpanRenewalPayload.wordSum n (T + 1)
      (fun word =>
        if success
          (history ++ grantBlockSupportSubword support word)
        then 1 else 0) = _
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  apply congrArg (Prob.scheduleSum n T)
  funext word
  cases he : support e with
  | false =>
      simp [grantBlockSupportSubword, he]
  | true =>
      simp [grantBlockSupportSubword, he,
        List.append_assoc]

theorem grantBlockPrefixHistoryPairMassSucc
    {n : Nat} (s t : Fin n → Bool)
    (a b : List (Fin n) → Bool)
    (left right : List (Fin n)) (T : Nat) :
    grantBlockPrefixHistoryPairMass
      s t a b left right (T + 1) =
      (List.ofFn (fun e : Fin n =>
        grantBlockPrefixHistoryPairMass s t a b
          (left ++ (if s e then [e] else []))
          (right ++ (if t e then [e] else [])) T)).sum := by
  unfold grantBlockPrefixHistoryPairMass
  change FixedSpanRenewalPayload.wordSum n (T + 1)
      (fun word =>
        if a (left ++ grantBlockSupportSubword s word) &&
           b (right ++ grantBlockSupportSubword t word)
        then 1 else 0) = _
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  apply congrArg (Prob.scheduleSum n T)
  funext word
  cases he : s e <;> cases hf : t e <;>
    simp [grantBlockSupportSubword, he, hf,
      List.append_assoc]

/-- One supported letter appended after the currently observed
prefix cannot destroy a TRUE prefix event.  This is a pointwise
Boolean statement, but it is NOT a statement that prepending
that letter to an arbitrary RANDOM continuation increases mass. -/
theorem grantBlockPrefixSuccessAppend
    {n : Nat} (success : List (Fin n) → Bool)
    (hPrefix : GrantBlockPrefixMonotone success)
    (history : List (Fin n)) (e : Fin n)
    (htrue : success history = true) :
    success (history ++ [e]) = true :=
  hPrefix history [e] htrue

/-- The missing induction step has a precise form: a sum over
ALL supported first letters, not the false per-letter increase.
Its proof requires exchanging the fresh supported letter with
the entire random supported-subword kernel, equivalently the
finite shuffle / weighted Chebyshev count. -/
def GrantBlockPrefixAggregateGain
    {n : Nat} (support : Fin n → Bool)
    (success : List (Fin n) → Bool) : Prop :=
  ∀ history : List (Fin n), ∀ T : Nat,
    (List.ofFn (fun e : Fin n =>
      if support e then
        grantBlockPrefixHistoryMass support success
          (history ++ [e]) T
      else 0)).sum ≥
    (List.ofFn (fun e : Fin n =>
      if support e then 1 else 0)).sum *
      grantBlockPrefixHistoryMass
        support success history T


/-- Elementary finite-list Fubini identity.  Needed because
the average-gain induction must exchange two supported letters
before applying its prefix induction hypothesis. -/
private theorem grantBlockPrefixMapSumAdd
    {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil =>
      rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem grantBlockPrefixMapSumSwap
    {α β : Type} (xs : List α) (ys : List β)
    (f : α → β → Nat) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil =>
      simp
      induction ys with
      | nil => rfl
      | cons y ys ih =>
          simp only [List.map_cons, List.sum_cons]
          omega
  | cons x rest ih =>
      change
        (ys.map (f x)).sum +
          (rest.map (fun a => (ys.map (f a)).sum)).sum =
        (ys.map (fun y => f x y +
          (rest.map (fun a => f a y)).sum)).sum
      rw [grantBlockPrefixMapSumAdd]
      rw [ih]

private theorem grantBlockPrefixOfFnSumSwap
    {n m : Nat} (f : Fin n → Fin m → Nat) :
    (List.ofFn (fun e : Fin n =>
      (List.ofFn (fun d : Fin m => f e d)).sum)).sum =
    (List.ofFn (fun d : Fin m =>
      (List.ofFn (fun e : Fin n => f e d)).sum)).sum := by
  have hh := grantBlockPrefixMapSumSwap
    (List.ofFn (fun e : Fin n => e))
    (List.ofFn (fun d : Fin m => d)) f
  simpa only [List.map_ofFn, Function.comp_def] using hh


/-- One extra uniformly selected supported scheduler letter. -/
private def grantBlockPrefixSupportOperator
    {n : Nat} (s : Fin n → Bool)
    (f : List (Fin n) → Nat)
    (u : List (Fin n)) : Nat :=
  (List.ofFn (fun e : Fin n =>
    if s e then f (u ++ [e]) else 0)).sum

private def grantBlockPrefixSupportCount
    {n : Nat} (s : Fin n → Bool) : Nat :=
  (List.ofFn (fun e : Fin n =>
    if s e then 1 else 0)).sum

private def grantBlockPrefixOutsideCount
    {n : Nat} (s : Fin n → Bool) : Nat :=
  (List.ofFn (fun e : Fin n =>
    if s e then 0 else 1)).sum

/-- The first-letter operator on supported-subword histories.
Unsupported letters leave the local history fixed. -/
private def grantBlockPrefixKernel
    {n : Nat} (s : Fin n → Bool)
    (f : List (Fin n) → Nat)
    (u : List (Fin n)) : Nat :=
  grantBlockPrefixSupportOperator s f u +
    grantBlockPrefixOutsideCount s * f u

private theorem grantBlockPrefixSupportOperatorMono
    {n : Nat} (s : Fin n → Bool)
    (f g : List (Fin n) → Nat)
    (h : ∀ u, f u ≤ g u)
    (u : List (Fin n)) :
    grantBlockPrefixSupportOperator s f u ≤
      grantBlockPrefixSupportOperator s g u := by
  unfold grantBlockPrefixSupportOperator
  apply ofFn_sum_le
  intro e
  cases hs : s e with
  | false =>
      simp [hs]
  | true =>
      simpa [hs] using h (u ++ [e])

private theorem grantBlockPrefixSupportOperatorAdd
    {n : Nat} (s : Fin n → Bool)
    (f g : List (Fin n) → Nat)
    (u : List (Fin n)) :
    grantBlockPrefixSupportOperator s
      (fun v => f v + g v) u =
    grantBlockPrefixSupportOperator s f u +
      grantBlockPrefixSupportOperator s g u := by
  unfold grantBlockPrefixSupportOperator
  calc
    (List.ofFn (fun e : Fin n =>
        if s e then f (u ++ [e]) + g (u ++ [e]) else 0)).sum =
      (List.ofFn (fun e : Fin n =>
        (if s e then f (u ++ [e]) else 0) +
        (if s e then g (u ++ [e]) else 0))).sum := by
          apply ofFn_sum_eq
          intro e
          cases s e <;> rfl
    _ = _ := ofFn_sum_add _ _

private theorem grantBlockPrefixSupportOperatorScale
    {n : Nat} (s : Fin n → Bool)
    (f : List (Fin n) → Nat)
    (K : Nat) (u : List (Fin n)) :
    grantBlockPrefixSupportOperator s
      (fun v => K * f v) u =
    K * grantBlockPrefixSupportOperator s f u := by
  unfold grantBlockPrefixSupportOperator
  calc
    (List.ofFn (fun e : Fin n =>
      if s e then K * f (u ++ [e]) else 0)).sum =
    (List.ofFn (fun e : Fin n =>
      K * (if s e then f (u ++ [e]) else 0))).sum := by
        apply ofFn_sum_eq
        intro e
        cases s e <;> simp
    _ = _ := ofFn_sum_mul_left K _

private theorem grantBlockPrefixKernelMono
    {n : Nat} (s : Fin n → Bool)
    (f g : List (Fin n) → Nat)
    (h : ∀ u, f u ≤ g u)
    (u : List (Fin n)) :
    grantBlockPrefixKernel s f u ≤
      grantBlockPrefixKernel s g u := by
  unfold grantBlockPrefixKernel
  exact Nat.add_le_add
    (grantBlockPrefixSupportOperatorMono s f g h u)
    (Nat.mul_le_mul_left
      (grantBlockPrefixOutsideCount s) (h u))

private theorem grantBlockPrefixKernelScale
    {n : Nat} (s : Fin n → Bool)
    (f : List (Fin n) → Nat)
    (K : Nat) (u : List (Fin n)) :
    grantBlockPrefixKernel s (fun v => K * f v) u =
      K * grantBlockPrefixKernel s f u := by
  unfold grantBlockPrefixKernel
  rw [grantBlockPrefixSupportOperatorScale]
  simp only [Nat.mul_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm]

/-- The full scheduler kernel is the supported-letter operator
plus a scalar identity operator, so these operators commute. -/
private theorem grantBlockPrefixKernelCommutesSupport
    {n : Nat} (s : Fin n → Bool)
    (f : List (Fin n) → Nat)
    (u : List (Fin n)) :
    grantBlockPrefixSupportOperator s
      (grantBlockPrefixKernel s f) u =
    grantBlockPrefixKernel s
      (grantBlockPrefixSupportOperator s f) u := by
  unfold grantBlockPrefixKernel
  rw [grantBlockPrefixSupportOperatorAdd,
      grantBlockPrefixSupportOperatorScale]

/-- The actual next-scheduler-letter recursion expressed through
the same positive kernel. -/
theorem grantBlockPrefixHistoryMassKernel
    {n : Nat} (s : Fin n → Bool)
    (a : List (Fin n) → Bool)
    (u : List (Fin n)) (T : Nat) :
    grantBlockPrefixHistoryMass s a u (T + 1) =
      grantBlockPrefixKernel s
        (fun v => grantBlockPrefixHistoryMass s a v T) u := by
  rw [grantBlockPrefixHistoryMassSucc]
  unfold grantBlockPrefixKernel
  have hsplit :
      (List.ofFn (fun e : Fin n =>
        grantBlockPrefixHistoryMass s a
          (u ++ (if s e then [e] else [])) T)).sum =
      (List.ofFn (fun e : Fin n =>
        (if s e then
          grantBlockPrefixHistoryMass s a (u ++ [e]) T
         else 0) +
        (if s e then 0 else
          grantBlockPrefixHistoryMass s a u T))).sum := by
    apply ofFn_sum_eq
    intro e
    cases s e <;> simp
  rw [hsplit, ofFn_sum_add]
  have houtside :
      (List.ofFn (fun e : Fin n =>
        if s e then 0 else
          grantBlockPrefixHistoryMass s a u T)).sum =
      grantBlockPrefixOutsideCount s *
        grantBlockPrefixHistoryMass s a u T := by
    calc
      _ = (List.ofFn (fun e : Fin n =>
          (grantBlockPrefixHistoryMass s a u T) *
            (if s e then 0 else 1))).sum := by
              apply ofFn_sum_eq
              intro e
              cases s e <;> simp
      _ = grantBlockPrefixHistoryMass s a u T *
          grantBlockPrefixOutsideCount s :=
        ofFn_sum_mul_left _ _
      _ = _ := Nat.mul_comm _ _
  rw [houtside]
  rfl

private theorem grantBlockPrefixHistoryMassZero
    {n : Nat} (s : Fin n → Bool)
    (a : List (Fin n) → Bool) (u : List (Fin n)) :
    grantBlockPrefixHistoryMass s a u 0 =
      if a u then 1 else 0 := by
  simp [grantBlockPrefixHistoryMass, Prob.scheduleSum,
    FixedSpanRenewalPayload.wordSum, allSchedules,
    grantBlockSupportSubword]


/-- At zero remaining scheduler steps, prefix monotonicity is
exactly a one-letter supported-average gain inequality. -/
private theorem grantBlockPrefixInitialAggregateGain
    {n : Nat} (s : Fin n → Bool)
    (a : List (Fin n) → Bool)
    (ha : GrantBlockPrefixMonotone a)
    (u : List (Fin n)) :
    grantBlockPrefixSupportCount s *
      (if a u then 1 else 0) ≤
    grantBlockPrefixSupportOperator s
      (fun v => if a v then 1 else 0) u := by
  by_cases hu : a u = true
  · have hh (e : Fin n) (hs : s e = true) :
        a (u ++ [e]) = true :=
      ha u [e] hu
    have heq :
        grantBlockPrefixSupportOperator s
          (fun v => if a v then 1 else 0) u =
        grantBlockPrefixSupportCount s := by
      unfold grantBlockPrefixSupportOperator
        grantBlockPrefixSupportCount
      apply ofFn_sum_eq
      intro e
      cases hs : s e with
      | false =>
          simp [hs]
      | true =>
          simp [hs, hh e hs]
    rw [heq, hu]
    simp
  · have hf : a u = false := by
      cases h : a u with
      | false => rfl
      | true => exact False.elim (hu h)
    rw [hf]
    simp

/-- Correct average-gain induction for EVERY scheduler horizon.
The per-letter insertion claim is false, but the supported-letter
operator commutes with the full scheduler kernel and that kernel
preserves pointwise inequalities. -/
theorem grantBlockPrefixAggregateGainProved
    {n : Nat} (s : Fin n → Bool)
    (a : List (Fin n) → Bool)
    (ha : GrantBlockPrefixMonotone a) :
    GrantBlockPrefixAggregateGain s a := by
  have hall :
      ∀ T : Nat, ∀ v : List (Fin n),
        grantBlockPrefixSupportCount s *
          grantBlockPrefixHistoryMass s a v T ≤
        grantBlockPrefixSupportOperator s
          (fun z => grantBlockPrefixHistoryMass s a z T) v := by
    intro horizon
    induction horizon with
    | zero =>
        intro v
        rw [grantBlockPrefixHistoryMassZero]
        have hbase := grantBlockPrefixInitialAggregateGain
          s a ha v
        simpa only [grantBlockPrefixHistoryMassZero] using hbase
    | succ k ih =>
        intro v
        have hkernel := grantBlockPrefixKernelMono s
          (fun z =>
            grantBlockPrefixSupportCount s *
              grantBlockPrefixHistoryMass s a z k)
          (fun z =>
            grantBlockPrefixSupportOperator s
              (fun w => grantBlockPrefixHistoryMass s a w k) z)
          ih v
        have hscale := grantBlockPrefixKernelScale s
          (fun z => grantBlockPrefixHistoryMass s a z k)
          (grantBlockPrefixSupportCount s) v
        have hcomm := grantBlockPrefixKernelCommutesSupport s
          (fun z => grantBlockPrefixHistoryMass s a z k) v
        rw [hscale] at hkernel
        rw [←hcomm] at hkernel
        simpa only [grantBlockPrefixHistoryMassKernel] using hkernel
  intro u T
  exact hall T u


/-- The exact three-category covariance identity in opaque Nat
variables.  Here the supported gains are represented by
gainS and gainT; the third category is all other letters.
This is the purely arithmetic half of the remaining joint
finite-word induction. -/
private theorem grantBlockPrefixThreeCategoryCovariance
    (sizeS sizeT sizeOther baseS baseT gainS gainT : Nat) :
    (sizeS + sizeT + sizeOther) *
      ((sizeS * baseS + gainS) * baseT +
       (sizeT * baseT + gainT) * baseS +
       sizeOther * baseS * baseT) ≤
    ((sizeS * baseS + gainS) +
      (sizeT + sizeOther) * baseS) *
    ((sizeT * baseT + gainT) +
      (sizeS + sizeOther) * baseT) := by
  have heq :
    ((sizeS * baseS + gainS) +
        (sizeT + sizeOther) * baseS) *
      ((sizeT * baseT + gainT) +
        (sizeS + sizeOther) * baseT) =
    (sizeS + sizeT + sizeOther) *
      ((sizeS * baseS + gainS) * baseT +
       (sizeT * baseT + gainT) * baseS +
       sizeOther * baseS * baseT) +
    gainS * gainT := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [heq]
  exact Nat.le_add_right _ _


end L3

#print axioms L3.grantBlockFrozenLocalOfSupport
#print axioms L3.grantBlockFrozenPrefixProperty
#print axioms L3.grantBlockFrozenPairDisjointOfSelected
#print axioms L3.grantBlockFirstSymbolNotInsertion
#print axioms L3.grantBlockPairPrefixEmptyExact
#print axioms L3.grantBlockPrefixHistoryMassSucc
#print axioms L3.grantBlockPrefixHistoryPairMassSucc
#print axioms L3.grantBlockPrefixAggregateGainProved

