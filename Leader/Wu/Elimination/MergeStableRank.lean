import Lean

/-!
# Merge-stable counting and the missing charge

This self-contained numerical/list model mirrors:
* `LDSinkGapServiceRank.gapWC`: the supplied three-branch Nat formula;
* `GapDoneC`: clean-ready or deletion of an endpoint of the current frame;
* `bulletTop` and `signalTop`: represented by summaries bounded by gap length;
* `EpisodeTelescope.telescoping_quadratic`: its quoted hstep interface.

There are no repository imports or claims of a physical refinement.
Finished flags are summary inputs, not invented CleanReady proofs.
The negative results certify numerical obstructions. They do not produce
an AgentState configuration, a K2 edge, or a reachable deletion witness.

Lists represent disjoint ownership, for example half-open ring gaps.
For global amortization their Booleans are one-use proof-side credits,
not executable extra state and not automatically current dirty-cell bits.
A concrete development must prove no_refill and span_charged_once.
The latter is not supplied by a fixed-gap rank bound.
-/

set_option autoImplicit false

namespace MergeStableRank

/-- Endpoint deletion is relative to the selected frame. -/
def frameDone (clean leftDeleted rightDeleted : Bool) : Bool :=
  clean || leftDeleted || rightDeleted

/-- Old frames may stop at an already-deleted common endpoint while the
outer frame has neither deletion nor cleanliness. This is a logical
reframing witness, not a pre-to-post physical transition witness. -/
theorem shared_endpoint_done_not_inherited :
    frameDone false false true = true ∧
    frameDone false true false = true ∧
    frameDone false false false = false := by
  decide

/-- Exact numerical shape quoted from LDSinkGapServiceRank. -/
def gapWC (finished : Bool) (d bulletTop signalTop : Nat) : Nat :=
  if finished then 0
  else if bulletTop = 0 then d - signalTop
  else d + bulletTop

theorem finished_rank_zero (d bt st : Nat) :
    gapWC true d bt st = 0 := by
  rfl

/-- The signal bound is not needed for this upper bound because subtraction
is Nat subtraction. The bullet-top bound is essential. -/
theorem gapWC_le_two_length (finished : Bool) (d bt st : Nat)
    (hbt : bt ≤ d) : gapWC finished d bt st ≤ 2 * d := by
  unfold gapWC
  split
  · exact Nat.zero_le _
  · split
    · omega
    · omega

/-- The requested small numerical example. No physical consistency of
independently supplied finished flags is asserted. -/
theorem small_zero_base :
    gapWC true 3 0 0 = 0 ∧
    gapWC true 3 0 0 = 0 ∧
    gapWC false 6 0 0 = 6 ∧
    ¬ gapWC false 6 0 0 ≤ gapWC true 3 0 0 + gapWC true 3 0 0 := by
  decide

/-- Unlike one fixed example, this family exceeds every proposed slack. -/
theorem zero_base_exceeds_any_slack (K : Nat) :
    gapWC true (K + 1) 0 0 + gapWC true 1 0 0 + K <
      gapWC false ((K + 1) + 1) 0 0 := by
  simp [gapWC] <;> omega

/-- With right length 3, right top 2 shifts to merged top a+2.
Both tops are within their respective lengths. All gaps are unfinished.
Realizing a deletion with these summaries is a separate physical obligation. -/
theorem surviving_bullet_merge_jump (a : Nat) :
    gapWC false (a + 3) (a + 2) 0 =
      gapWC false a 0 0 + gapWC false 3 2 0 + a := by
  have hb : a + 2 ≠ 0 := by omega
  simp [gapWC] <;> omega

/-- Even the all-unfinished summary family has no universal additive slack. -/
theorem no_uniform_merge_slack :
    ¬ ∃ K : Nat, ∀ a : Nat, 0 < a →
      gapWC false (a + 3) (a + 2) 0 ≤
        gapWC false a 0 0 + gapWC false 3 2 0 + K := by
  intro h
  obtain ⟨K, hK⟩ := h
  have hbound := hK (K + 1) (by omega)
  have hjump := surviving_bullet_merge_jump (K + 1)
  omega

/-! ## Count algebra, separate from physical movement -/

/-- Count marked cells. Marks may denote occupancy in diagnostics or
nonrenewable credit in the later amortization interface. -/
def count : List Bool → Nat
  | [] => 0
  | b :: xs => (if b then 1 else 0) + count xs

/-- The exact additivity furnished by disjoint list concatenation. -/
theorem count_append (L R : List Bool) :
    count (L ++ R) = count L + count R := by
  induction L with
  | nil => simp [count]
  | cons b L ih =>
      change (if b then 1 else 0) + count (L ++ R) =
        ((if b then 1 else 0) + count L) + count R
      rw [ih, Nat.add_assoc]

theorem count_le_length (xs : List Bool) : count xs ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons b xs ih =>
      cases b with
      | false =>
          change 0 + count xs ≤ xs.length + 1
          omega
      | true =>
          change 1 + count xs ≤ xs.length + 1
          omega

/-- A one-cell transport can leave occupancy unchanged, not strictly lower. -/
theorem movement_keeps_count :
    count [true, false, false] = 1 ∧
    count [false, true, false] = 1 ∧
    ¬ count [false, true, false] < count [true, false, false] := by
  decide

/-- Even an arbitrary constant cannot turn zero occupancy into sweep work.
This numerical example uses the unfinished, bullet-free, signal-free branch. -/
theorem dirty_count_cannot_bound_rank (K : Nat) :
    ¬ gapWC false 6 0 0 ≤
      K * count [false, false, false, false, false, false] := by
  simp [gapWC, count]

/-- Terminal rank zero does not bound residual occupancy from below either. -/
theorem count_need_not_le_rank :
    ¬ count [true] ≤ gapWC true 1 1 0 := by
  decide

/-- The same disjoint cells, with marks only erased and never reintroduced.
Arguments are in before/after order. This is a credit relation, not an
assertion that arbitrary physical bullet/signal updates have this property. -/
inductive Clears : List Bool → List Bool → Prop where
  | nil : Clears [] []
  | keep (b : Bool) {xs ys : List Bool} :
      Clears xs ys → Clears (b :: xs) (b :: ys)
  | spend {xs ys : List Bool} :
      Clears xs ys → Clears (true :: xs) (false :: ys)

/-- Exact monotonicity, with no additive slack. -/
theorem count_le_of_clears {xs ys : List Bool} (h : Clears xs ys) :
    count ys ≤ count xs := by
  induction h with
  | nil => exact Nat.le_refl _
  | keep b h ih =>
      exact Nat.add_le_add_left ih (if b then 1 else 0)
  | spend h ih =>
      change 0 + count _ ≤ 1 + count _
      omega

theorem clears_length_eq {xs ys : List Bool} (h : Clears xs ys) :
    ys.length = xs.length := by
  induction h with
  | nil => rfl
  | keep b h ih =>
      simpa only [List.length_cons] using congrArg Nat.succ ih
  | spend h ih =>
      simpa only [List.length_cons] using congrArg Nat.succ ih

/-- Merge ownership and erase any subset of its credits. -/
theorem count_merge_clear_le {L R M : List Bool}
    (h : Clears (L ++ R) M) : count M ≤ count L + count R := by
  have hm := count_le_of_clears h
  simpa only [count_append] using hm

/-- Spending one permanent mark gives exactly one unit of telescope credit. -/
theorem one_spend_exact (pre post : List Bool) :
    count (pre ++ (true :: post)) - count (pre ++ (false :: post)) = 1 := by
  simp [count_append, count] <;> omega

/-- Natural subtraction telescopes because both intervening counts decrease. -/
theorem count_spending_telescope {A B C : List Bool}
    (hAB : Clears A B) (hBC : Clears B C) :
    (count A - count B) + (count B - count C) = count A - count C := by
  have hab := count_le_of_clears hAB
  have hbc := count_le_of_clears hBC
  omega

/-- Total count when the same owned cells are grouped into several gaps. -/
def partitionCount : List (List Bool) → Nat
  | [] => 0
  | g :: gs => count g + partitionCount gs

/-- Removing a partition boundary does not replenish or consume credit. -/
theorem partition_merge (L R : List Bool) (rest : List (List Bool)) :
    partitionCount ((L ++ R) :: rest) = partitionCount (L :: R :: rest) := by
  change count (L ++ R) + partitionCount rest =
    count L + (count R + partitionCount rest)
  rw [count_append, Nat.add_assoc]

/-! ## W-3: preserve the local rank, charge a different global count -/

/-- Bounded scalar summaries, not full physical gap certificates. -/
structure GapSummary where
  d : Nat
  bulletTop : Nat
  signalTop : Nat
  finished : Bool
  bulletTop_le : bulletTop ≤ d
  signalTop_le : signalTop ≤ d

def localRank (g : GapSummary) : Nat :=
  gapWC g.finished g.d g.bulletTop g.signalTop

theorem localRank_le_two_length (g : GapSummary) :
    localRank g ≤ 2 * g.d := by
  exact gapWC_le_two_length g.finished g.d g.bulletTop g.signalTop g.bulletTop_le

/-- Global weight on any later concrete episode state type X. -/
def weight {X : Type} (credits : X → List Bool) (x : X) : Nat :=
  count (credits x)

/-- At most one initial credit per globally owned cell gives w <= n. -/
theorem initial_weight_le_population {X : Type}
    (credits : X → List Bool) (x : X) (n : Nat)
    (hsize : (credits x).length ≤ n) : weight credits x ≤ n := by
  exact Nat.le_trans (count_le_length (credits x)) hsize

/-- Turn an existing 2*n*d-style numerical cost certificate into the
quoted telescope charge. The length-to-spent-credit premise is explicit. -/
theorem w3_span_cost (d n c B wx wy cost : Nat)
    (hcost : cost ≤ (c * n) * (2 * d))
    (hcharge : d ≤ B * ((wx - wy) + 1)) :
    cost ≤ ((2 * c * B) * n) * ((wx - wy) + 1) := by
  calc
    cost ≤ (c * n) * (2 * d) := hcost
    _ = (2 * (c * n)) * d := by ac_rfl
    _ ≤ (2 * (c * n)) * (B * ((wx - wy) + 1)) :=
      Nat.mul_le_mul_left _ hcharge
    _ = ((2 * c * B) * n) * ((wx - wy) + 1) := by ac_rfl

/-- A sharper localRank-based cost certificate can use exactly the same
adapter. No comparison to dirty-cell occupancy is required or claimed. -/
theorem w3_rank_cost (g : GapSummary) (n c B wx wy cost : Nat)
    (hcost : cost ≤ (c * n) * localRank g)
    (hcharge : g.d ≤ B * ((wx - wy) + 1)) :
    cost ≤ ((2 * c * B) * n) * ((wx - wy) + 1) := by
  apply w3_span_cost g.d n c B wx wy cost
  · exact Nat.le_trans hcost
      (Nat.mul_le_mul_left (c * n) (localRank_le_two_length g))
  · exact hcharge

/-- Protocol-facing obligations. This file supplies no concrete instance.
Cost quantities are numerical bound certificates, not claimed deterministic
bounds on elapsed random-scheduler time. Constants c and B must be uniform
in population size for the resulting bound to be quadratic. -/
structure EpisodeBridge {X : Type}
    (next : X → X → Prop) (credits : X → List Bool) (phase : X → Nat)
    (selected : X → X → GapSummary) (episodeBound : X → X → Nat)
    (n c B : Nat) : Prop where
  /-- Global ownership is conserved and spent marks are never refilled,
  including at mergers, new fires, and recovery resets. -/
  no_refill : ∀ {x y : X}, next x y → Clears (credits x) (credits y)
  /-- Strict decrease of the existing episode phase measure. -/
  phase_drop : ∀ {x y : X}, next x y → phase y < phase x
  /-- Existing fixed-gap cleanup results may supply this certificate. -/
  local_cost : ∀ {x y : X}, next x y →
    episodeBound x y ≤ (c * n) * (2 * (selected x y).d)
  /-- THE MISSING AMORTIZATION FACT: a long episode spends proportionately
  many globally one-use credits, up to the constant one-episode allowance.
  Count additivity and gapWC <= 2*d do not establish this field. -/
  span_charged_once : ∀ {x y : X}, next x y →
    (selected x y).d ≤ B * ((weight credits x - weight credits y) + 1)

/-- Exact hstep shape quoted from EpisodeTelescope, with C = 2*c*B.
The weight inequality has no slack. Physical instantiation remains explicit. -/
theorem episode_hstep {X : Type}
    (next : X → X → Prop) (credits : X → List Bool) (phase : X → Nat)
    (selected : X → X → GapSummary) (episodeBound : X → X → Nat)
    (n c B : Nat)
    (h : EpisodeBridge next credits phase selected episodeBound n c B) :
    ∀ {x y : X}, next x y →
      weight credits y ≤ weight credits x ∧ phase y < phase x ∧
      episodeBound x y ≤
        ((2 * c * B) * n) * ((weight credits x - weight credits y) + 1) := by
  intro x y hxy
  refine ⟨count_le_of_clears (h.no_refill hxy), h.phase_drop hxy, ?_⟩
  exact w3_span_cost (selected x y).d n c B
    (weight credits x) (weight credits y) (episodeBound x y)
    (h.local_cost hxy) (h.span_charged_once hxy)

/-- A conserved total length or a pure regrouping has zero credit spend.
It cannot pay for an arbitrarily long episode through the +1 allowance. -/
theorem no_spend_requires_short_span (d B wx wy : Nat)
    (heq : wx = wy) (hcharge : d ≤ B * ((wx - wy) + 1)) : d ≤ B := by
  simpa only [heq, Nat.sub_self, Nat.zero_add, Nat.mul_one] using hcharge

end MergeStableRank

#print axioms MergeStableRank.shared_endpoint_done_not_inherited
#print axioms MergeStableRank.finished_rank_zero
#print axioms MergeStableRank.gapWC_le_two_length
#print axioms MergeStableRank.small_zero_base
#print axioms MergeStableRank.zero_base_exceeds_any_slack
#print axioms MergeStableRank.surviving_bullet_merge_jump
#print axioms MergeStableRank.no_uniform_merge_slack
#print axioms MergeStableRank.count_append
#print axioms MergeStableRank.count_le_length
#print axioms MergeStableRank.movement_keeps_count
#print axioms MergeStableRank.dirty_count_cannot_bound_rank
#print axioms MergeStableRank.count_need_not_le_rank
#print axioms MergeStableRank.count_le_of_clears
#print axioms MergeStableRank.clears_length_eq
#print axioms MergeStableRank.count_merge_clear_le
#print axioms MergeStableRank.one_spend_exact
#print axioms MergeStableRank.count_spending_telescope
#print axioms MergeStableRank.partition_merge
#print axioms MergeStableRank.localRank_le_two_length
#print axioms MergeStableRank.initial_weight_le_population
#print axioms MergeStableRank.w3_span_cost
#print axioms MergeStableRank.w3_rank_cost
#print axioms MergeStableRank.episode_hstep
#print axioms MergeStableRank.no_spend_requires_short_span
