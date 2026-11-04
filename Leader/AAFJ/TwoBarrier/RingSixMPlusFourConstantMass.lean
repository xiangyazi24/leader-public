import Leader.AAFJ.TwoBarrier.RingSixMPlusFourContactDrop
import Leader.Wu.Scheduler.Probability
import Leader.AAFJ.MultiBarrier.GoodSixStageScan

set_option autoImplicit false
set_option Elab.async false

/-!
# The finite code layer for the `6*m+4` contact/drop construction

This file keeps the physical consumer frozen.  It records the exact finite
code objects used by the adaptive construction and proves the denominator
arithmetic handoff for a physical encoder.  The code alphabet uses `0` for the prescribed charged edge,
`1` for the competing charged edge, and `2,...,n-1` for current nonbarrier
edges.  `firstP` says that the first `k` marked letters are all prescribed
charged letters; after the `k`-th one the suffix is free.

The intended closed forms of these counts are
`A_n = Σ_{j=3}^{3n} C(j-1,2)(n-2)^(j-3)n^(3n-j)` and
`G_n = Σ_{s=6}^{6n} C(s-1,5)(n-2)^(s-6)n^(6n-s)`; the recursive count
interface below is the kernel-checked form used before exposing those sums.
-/

namespace AAFJPK.N6m4ConstantMass

open BarrierAlgebra
open OriginalNonbarrierWord
open N6m4ColoredChildTable
open N6m4ContactDropCylinder
open FiniteUniformStoppingTree
open AAFJPK.OriginalPhysicalTraceAdapter

private theorem hk3 : 0 < 3 := by decide

/-! ## The abstract marked-letter code -/

def firstP {n : Nat} : Nat → List (Fin n) → Bool
  | 0, _ => true
  | k + 1, [] => false
  | k + 1, e :: w =>
      if e.val = 0 then firstP k w
      else if 2 ≤ e.val then firstP (k + 1) w
      else false

def goodCode {n : Nat} (k : Nat) (w : List (Fin n)) : Bool :=
  firstP k w.reverse

def goodCount (n k T : Nat) : Nat :=
  (allSchedules n T).countP (goodCode k)

def A (n : Nat) : Nat := goodCount n 3 (3 * n)
def G (n : Nat) : Nat := goodCount n 6 (6 * n)

abbrev ContactCodeCount (n : Nat) : Nat := A n
abbrev AdaptiveDropCodeCount (n : Nat) : Nat := G n

theorem goodCode_append {n k : Nat} (w : List (Fin n)) (e : Fin n) :
    goodCode (k + 1) (w ++ [e]) =
      if e.val = 0 then goodCode k w
      else if 2 ≤ e.val then goodCode (k + 1) w
      else false := by
  simp [goodCode, firstP]

private theorem countP_eq_sum_indicator {α : Type} (xs : List α)
    (p : α → Bool) :
    xs.countP p = (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases p x <;> simp [Nat.add_comm]

private theorem nodup_ofFn_id (n : Nat) :
    (List.ofFn (fun e : Fin n => e)).Nodup := by
  have aux : ∀ {k : Nat} {α : Type} (f : Fin k → α),
      Function.Injective f → (List.ofFn f).Nodup := by
    intro k α f hf
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.ofFn_succ, List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
          have hidx : (0 : Fin (k + 1)) = i.succ := hf hi.symm
          exact (Fin.succ_ne_zero i) hidx.symm
        · apply ih
          intro i j h
          exact Fin.succ_inj.mp (hf h)
  exact aux (fun e : Fin n => e) Function.injective_id

private theorem count_letter_zero (n : Nat) (hn : 0 < n) :
    (List.ofFn (fun e : Fin n => e)).countP
        (fun e => decide (e.val = 0)) = 1 := by
  induction n with
  | zero => omega
  | succ n =>
      rw [List.ofFn_succ, List.countP_cons]
      have hs : (List.ofFn (fun e : Fin n => (e.succ : Fin (Nat.succ n)))).countP
          (fun e => decide (e.val = 0)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro e he_mem he_true
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he_mem
        have hv : i.succ.val = 0 := of_decide_eq_true he_true
        change i.val + 1 = 0 at hv
        omega
      rw [hs]
      rfl

private theorem count_letter_noise (n : Nat) (hn : 2 ≤ n) :
    (List.ofFn (fun e : Fin n => e)).countP
        (fun e => decide (2 ≤ e.val)) = n - 2 := by
  let xs := List.ofFn (fun e : Fin n => e)
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  have hzero : z ∈ xs := by
    exact List.mem_ofFn.mpr ⟨z, rfl⟩
  have hone : o ∈ xs := by
    exact List.mem_ofFn.mpr ⟨o, rfl⟩
  have h01 : z ≠ o := by
    intro h
    have := congrArg Fin.val h
    simp [z, o] at this
  have hsum := sum_two_exceptions xs z o
    (fun e => if decide (2 ≤ e.val) then 1 else 0) 1
    (nodup_ofFn_id n) hzero hone h01 (by
      intro e _ he0 he1
      have he0' : e.val ≠ 0 := by
        intro h
        apply he0
        apply Fin.ext
        exact h
      have he1' : e.val ≠ 1 := by
        intro h
        apply he1
        apply Fin.ext
        exact h
      have hge : 2 ≤ e.val := by omega
      simp [hge])
  rw [countP_eq_sum_indicator]
  change (xs.map (fun e => if decide (2 ≤ e.val) then 1 else 0)).sum = _
  rw [hsum]
  simp [z, o, xs]

private theorem count_letter_not_one (n : Nat) (hn : 2 ≤ n) :
    (List.ofFn (fun e : Fin n => e)).countP
        (fun e => decide (e.val ≠ 1)) = n - 1 := by
  let xs := List.ofFn (fun e : Fin n => e)
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  have hzero : z ∈ xs := List.mem_ofFn.mpr ⟨z, rfl⟩
  have hone : o ∈ xs := List.mem_ofFn.mpr ⟨o, rfl⟩
  have h01 : z ≠ o := by
    intro h
    have hv := congrArg Fin.val h
    simp [z, o] at hv
  have hsum := sum_two_exceptions xs z o
    (fun e => if decide (e.val ≠ 1) then 1 else 0) 1
    (nodup_ofFn_id n) hzero hone h01 (by
      intro e _ he0 he1
      have he0' : e.val ≠ 0 := by
        intro h
        apply he0
        apply Fin.ext
        exact h
      have he1' : e.val ≠ 1 := by
        intro h
        apply he1
        apply Fin.ext
        exact h
      simp [he0', he1'])
  rw [countP_eq_sum_indicator]
  change (xs.map (fun e => if decide (e.val ≠ 1) then 1 else 0)).sum = _
  rw [hsum]
  simp [z, o, xs]
  omega

private theorem count_marked_conditional (n : Nat) (hn : 2 ≤ n)
    (a b : Bool) :
    (List.ofFn (fun e : Fin n => e)).countP
        (fun e => if e.val = 0 then a
          else if 2 ≤ e.val then b else false) =
      (if a then 1 else 0) + (if b then n - 2 else 0) := by
  cases a <;> cases b
  · apply List.countP_eq_zero.mpr
    intro e _ he
    simp at he
  · have hp : (fun e : Fin n =>
        if e.val = 0 then false else if 2 ≤ e.val then true else false) =
      (fun e => decide (2 ≤ e.val)) := by
        funext e
        by_cases h0 : e.val = 0 <;> by_cases h2 : 2 ≤ e.val <;>
          simp [h0, h2]
    rw [hp, count_letter_noise n hn]
    simp
  · have hp : (fun e : Fin n =>
        if e.val = 0 then true else if 2 ≤ e.val then false else false) =
      (fun e => decide (e.val = 0)) := by
        funext e
        by_cases h0 : e.val = 0 <;> by_cases h2 : 2 ≤ e.val <;>
          simp [h0, h2]
    rw [hp, count_letter_zero n (by omega)]
    simp
  · have hp : (fun e : Fin n =>
        if e.val = 0 then true else if 2 ≤ e.val then true else false) =
      (fun e => decide (e.val ≠ 1)) := by
        funext e
        by_cases h0 : e.val = 0 <;> by_cases h2 : 2 ≤ e.val <;>
          simp [h0, h2] <;> omega
    rw [hp, count_letter_not_one n hn]
    simp
    omega

private theorem count_extension {n k : Nat} (hn : 2 ≤ n)
    (w : List (Fin n)) :
    (List.ofFn (fun e : Fin n => w ++ [e])).countP (goodCode (k + 1)) =
      (if goodCode k w then 1 else 0) +
        (if goodCode (k + 1) w then n - 2 else 0) := by
  have hmap : List.ofFn (fun e : Fin n => w ++ [e]) =
      (List.ofFn (fun e : Fin n => e)).map (fun e => w ++ [e]) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.countP_map]
  have hp : (fun e : Fin n => goodCode (k + 1) (w ++ [e])) =
      (fun e => if e.val = 0 then goodCode k w
        else if 2 ≤ e.val then goodCode (k + 1) w else false) := by
    funext e
    exact goodCode_append w e
  change (List.ofFn (fun e : Fin n => e)).countP
      (fun e => goodCode (k + 1) (w ++ [e])) = _
  rw [hp]
  exact count_marked_conditional n hn _ _

private theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

private theorem sum_if_count {α : Type} (xs : List α) (p : α → Bool)
    (c : Nat) :
    (xs.map (fun x => if p x then c else 0)).sum = xs.countP p * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
      cases p x <;> simp [Nat.add_mul, Nat.add_comm]

theorem goodCount_step {n k T : Nat} (hn : 2 ≤ n) :
    goodCount n (k + 1) (T + 1) =
      goodCount n k T + (n - 2) * goodCount n (k + 1) T := by
  unfold goodCount
  rw [allSchedules, List.countP_flatMap]
  have hmap :
      (List.map
          (List.countP (goodCode (k + 1)) ∘
            (fun w => List.ofFn (fun e : Fin n => w ++ [e])))
        (allSchedules n T)) =
      (List.map (fun w =>
          (if goodCode k w then 1 else 0) +
            (if goodCode (k + 1) w then n - 2 else 0))
        (allSchedules n T)) := by
    apply List.map_congr_left
    intro w hw
    change (List.ofFn (fun e : Fin n => w ++ [e])).countP
        (goodCode (k + 1)) = _
    exact count_extension hn w
  rw [hmap, sum_map_add, sum_if_count, sum_if_count]
  simp [Nat.mul_comm]

@[simp] theorem goodCount_zero (n T : Nat) :
    goodCount n 0 T = n ^ T := by
  unfold goodCount
  rw [List.countP_eq_length_filter]
  rw [List.filter_eq_self.mpr (by
    intro a ha
    simp [goodCode, firstP])]
  exact allSchedules_length n T

@[simp] theorem goodCount_empty {n k : Nat} (hk : 0 < k) :
    goodCount n k 0 = 0 := by
  unfold goodCount
  cases k with
  | zero => omega
  | succ k => simp [goodCode, firstP, allSchedules]

theorem goodCount_le_pow (n k T : Nat) :
    goodCount n k T ≤ n ^ T := by
  unfold goodCount
  calc
    (allSchedules n T).countP (goodCode k) ≤
        (allSchedules n T).length := List.countP_le_length
    _ = n ^ T := allSchedules_length n T

/-! ## Dynamic nonbarrier choices

For an exact two-edge support, the filtered physical edge list has exactly
`n-2` entries.  The encoder below uses its `Fin (n-2)` index; this keeps the
choice count and injectivity in the actual ring alphabet rather than in an
uninterpreted copy of it. -/

def freeEdges {n : Nat} (a b : Fin n) : List (Fin n) :=
  (List.ofFn (fun e : Fin n => e)).filter
    (fun e => decide (e ≠ a ∧ e ≠ b))

private theorem freeEdges_length {n : Nat} (hn : 2 ≤ n)
    {a b : Fin n} (hab : a ≠ b) :
    (freeEdges a b).length = n - 2 := by
  let xs := List.ofFn (fun e : Fin n => e)
  have hsum := sum_two_exceptions xs a b
    (fun e => if decide (e ≠ a ∧ e ≠ b) then 1 else 0) 1
    (nodup_ofFn_id n)
    (List.mem_ofFn.mpr ⟨a, rfl⟩)
    (List.mem_ofFn.mpr ⟨b, rfl⟩) hab (by
      intro e _ he0 he1
      simp [he0, he1])
  have hcount : xs.countP (fun e => decide (e ≠ a ∧ e ≠ b)) = n - 2 := by
    rw [countP_eq_sum_indicator]
    change (xs.map (fun e => if decide (e ≠ a ∧ e ≠ b) then 1 else 0)).sum = _
    rw [hsum]
    simp [xs]
  rw [show freeEdges a b = xs.filter
      (fun e => decide (e ≠ a ∧ e ≠ b)) by rfl]
  rw [← List.countP_eq_length_filter, hcount]

noncomputable def freeEdge {n : Nat} (a b : Fin n) (hab : a ≠ b)
    (i : Fin (n - 2)) : Fin n :=
  (freeEdges a b).get ⟨i.val, by
    rw [freeEdges_length (by omega) (a := a) (b := b) hab]
    exact i.isLt⟩

private theorem freeEdge_mem {n : Nat} {a b : Fin n} (hn : 2 ≤ n)
    (hab : a ≠ b) (i : Fin (n - 2)) :
    freeEdge a b hab i ∈ freeEdges a b := by
  exact List.get_mem _ _

private theorem freeEdge_nonbarrier
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} {a b : Fin n}
    (hs : ExactTwoBarrierSupport hk ring C a b)
    (hn : 2 ≤ n) (i : Fin (n - 2)) :
    ¬ BarrierAt hk ring (labelsOf C) (freeEdge a b hs.1 i) := by
  have hm := freeEdge_mem hn hs.1 i
  simp [freeEdges] at hm
  intro hbar
  rcases (hs.2 _).1 hbar with h | h
  · exact hm.1 h
  · exact hm.2 h

private theorem freeEdge_injective {n : Nat} {a b : Fin n}
    (hn : 2 ≤ n) (hab : a ≠ b) :
    Function.Injective (freeEdge a b hab) := by
  intro i j hij
  have hnodup : (freeEdges a b).Nodup := by
    exact (nodup_ofFn_id n).filter _
  have hget : (freeEdges a b).get ⟨i.val, by
      rw [freeEdges_length hn (a := a) (b := b) hab]
      exact i.isLt⟩ =
      (freeEdges a b).get ⟨j.val, by
        rw [freeEdges_length hn (a := a) (b := b) hab]
        exact j.isLt⟩ := hij
  have hget' := (List.getElem_inj hnodup).mp (by
    simpa only [List.get_eq_getElem] using hget)
  exact Fin.ext hget'

/-! ## The actual adaptive six-hit block

The next predicate is a raw scheduler word, not a symbolic success token.
Its six gap proofs are the current-prestate proofs carried by
`GappedSixTrace`; consequently an early strict drop is already accepted by
the endpoint theorem and no no-earlier-drop side condition is introduced. -/

private theorem rawRun_append_trace {m : Nat}
    (C : Fin (N m) → State 3) (u w : List (Fin (N m))) :
    rawRun hk3 (ring m) C (u ++ w) =
      rawRun hk3 (ring m) (rawRun hk3 (ring m) C u) w := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((protocol 3 hk3).step (ring m) C e)

private theorem barrierCount_rawRun_le_trace {m : Nat}
    (C : Fin (N m) → State 3) (w : List (Fin (N m))) :
    barrierCount hk3 (ring m) (labelsOf (rawRun hk3 (ring m) C w)) ≤
      barrierCount hk3 (ring m) (labelsOf C) := by
  induction w generalizing C with
  | nil => simp [rawRun]
  | cons e es ih =>
      have hstep := protocol_step_barrierCount_le hk3 (ring m)
        (by simp [N]) C e
      have htail := ih ((protocol 3 hk3).step (ring m) C e)
      exact Nat.le_trans (by simpa [rawRun] using htail) hstep

private theorem H_exact_two {m : Nat} (hm : 1 ≤ m) :
    ExactTwoBarrierSupport hk3 (ring m) H (v1 m) (v2 m) := by
  refine ⟨?_, H_support hm⟩
  simp [v1, v2, v, Fin.ext_iff]

private theorem barrierCount_eq_two_of_support_trace {m : Nat}
    (C : Fin (N m) → State 3) (a b : Fin (N m)) (hab : a ≠ b)
    (hs : ∀ e, BarrierAt hk3 (ring m) (labelsOf C) e ↔ e = a ∨ e = b) :
    barrierCount hk3 (ring m) (labelsOf C) = 2 := by
  have hnodup : [a, b].Nodup := by simp [hab]
  have hlo : [a, b] ⊆ barrierSupport hk3 (ring m) (labelsOf C) := by
    intro x hx
    simp at hx
    rcases hx with h | h
    · subst x
      exact (mem_barrierSupport_iff hk3 (ring m) (labelsOf C) a).2
        ((hs a).2 (Or.inl rfl))
    · subst x
      exact (mem_barrierSupport_iff hk3 (ring m) (labelsOf C) b).2
        ((hs b).2 (Or.inr rfl))
  have hlow : 2 ≤ (barrierSupport hk3 (ring m) (labelsOf C)).length := by
    simpa using hnodup.length_le_of_subset hlo
  have hhi : barrierSupport hk3 (ring m) (labelsOf C) ⊆ [a, b] := by
    intro x hx
    have hxbar := (mem_barrierSupport_iff hk3 (ring m) (labelsOf C) x).1 hx
    rcases (hs x).1 hxbar with h | h
    · subst x; simp
    · subst x; simp
  have hupp :
      (barrierSupport hk3 (ring m) (labelsOf C)).length ≤ [a, b].length :=
    (barrierSupport_nodup hk3 (ring m) (labelsOf C)).length_le_of_subset hhi
  unfold barrierCount
  simpa using Nat.le_antisymm (by simpa using hupp) hlow

def AdaptiveDropBlock (m : Nat) (w : List (Fin (N m))) : Prop :=
  ∃ w0 w1 w2 w3 w4 w5,
    GappedSixTrace hk3 (ring m) H (v1 m) (v2 m) (v3 m)
      w0 w1 w2 w3 w4 w5 w ∧
    w.length = 6 * N m

theorem AdaptiveDropBlock.strict {m : Nat} (hm : 1 ≤ m)
    {w : List (Fin (N m))} (hw : AdaptiveDropBlock m w) :
    barrierCount hk3 (ring m) (labelsOf (rawRun hk3 (ring m) H w)) <
      barrierCount hk3 (ring m) (labelsOf H) := by
  rcases hw with ⟨w0, w1, w2, w3, w4, w5, htrace, _⟩
  exact gappedSixTrace_strict_drop hk3 (ring m) (by simp [N])
    H (v1 m) (v2 m) (v3 m) w0 w1 w2 w3 w4 w5 w htrace

def ContactAdaptiveDropCylinder (m : Nat) (w : List (Fin (N m))) : Prop :=
  ∃ contact drop suffix,
    ContactPrefix contact ∧ AdaptiveDropBlock m drop ∧
    w = contact ++ drop ++ suffix ∧ w.length = 9 * N m

theorem ContactAdaptiveDropCylinder.strict {m : Nat} (hm : 1 ≤ m)
    {w : List (Fin (N m))} (hw : ContactAdaptiveDropCylinder m w) :
    barrierCount hk3 (ring m)
        (labelsOf (rawRun hk3 (ring m) S0 w)) <
      barrierCount hk3 (ring m) (labelsOf S0) := by
  rcases hw with ⟨contact, drop, suffix, hc, hd, rfl, _⟩
  have hcontact := ContactPrefix.rawRun_eq_H hm hc
  have hprefix :
      rawRun hk3 (ring m) S0 (contact ++ drop) =
        rawRun hk3 (ring m) H drop := by
    rw [rawRun_append_trace, hcontact]
  have hfull :
      rawRun hk3 (ring m) S0 ((contact ++ drop) ++ suffix) =
        rawRun hk3 (ring m)
          (rawRun hk3 (ring m) H drop) suffix := by
    rw [rawRun_append_trace, hprefix]
  rw [hfull]
  have hdrop := AdaptiveDropBlock.strict hm hd
  have hsuffix := barrierCount_rawRun_le_trace
    (rawRun hk3 (ring m) H drop) suffix
  have heq : barrierCount hk3 (ring m) (labelsOf H) =
      barrierCount hk3 (ring m) (labelsOf S0) := by
    rw [barrierCount_eq_two_of_support_trace H (v1 m) (v2 m)
          (by simp [v1, v2, v, Fin.ext_iff]) (H_support hm)]
    rw [barrierCount_eq_two_of_support_trace S0 (v0 m) (v2 m)
          (by simp [v0, v2, v, Fin.ext_iff]) (S0_support hm)]
  rw [heq] at hdrop
  omega

/-! ## Exact code-family cardinalities

These are the finite domains that an eventual physical encoder must inject
into `ContactAdaptiveDropCylinder`.  Keeping the code lists explicit prevents
the product count from being confused with a count of symbolic outcomes. -/

def ContactPrefixCodes (m : Nat) : List (List (Fin (N m))) :=
  (allSchedules (N m) (3 * N m)).filter (goodCode 3)

def AdaptiveDropCodes (m : Nat) : List (List (Fin (N m))) :=
  (allSchedules (N m) (6 * N m)).filter (goodCode 6)

theorem ContactPrefixCodes.length (m : Nat) :
    (ContactPrefixCodes m).length = A (N m) := by
  rw [show ContactPrefixCodes m =
      (allSchedules (N m) (3 * N m)).filter (goodCode 3) by rfl]
  rw [← List.countP_eq_length_filter]
  rfl

theorem AdaptiveDropCodes.length (m : Nat) :
    (AdaptiveDropCodes m).length = G (N m) := by
  rw [show AdaptiveDropCodes m =
      (allSchedules (N m) (6 * N m)).filter (goodCode 6) by rfl]
  rw [← List.countP_eq_length_filter]
  rfl

private theorem sum_replicate_const (a n : Nat) :
    (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.sum_cons, ih]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
      ac_rfl

def ContactAdaptiveDropCodePairs (m : Nat) :
    List (List (Fin (N m)) × List (Fin (N m))) :=
  (ContactPrefixCodes m).flatMap (fun c =>
    (AdaptiveDropCodes m).map (fun d => (c, d)))

theorem ContactAdaptiveDropCodePairs.length (m : Nat) :
    (ContactAdaptiveDropCodePairs m).length = A (N m) * G (N m) := by
  unfold ContactAdaptiveDropCodePairs
  rw [List.length_flatMap]
  have hmap :
      (ContactPrefixCodes m).map (fun _ => (AdaptiveDropCodes m).length) =
        List.replicate (ContactPrefixCodes m).length (AdaptiveDropCodes m).length := by
    induction ContactPrefixCodes m with
    | nil => rfl
    | cons c cs ih =>
        simp only [List.map_cons, List.length_cons]
        rw [List.replicate_succ]
        rw [ih]
  simp only [List.length_map]
  rw [hmap, sum_replicate_const, ContactPrefixCodes.length,
    AdaptiveDropCodes.length]

/-! The same code automaton with the two marked letters identified.  This is
the convenient exact form for the finite second-moment estimate: `markedCount`
counts words with at least `k` marked positions, while `lowCount` counts words
with at most `k-1` marked positions.
-/

def markedCount (n : Nat) : Nat → Nat → Nat
  | 0, T => n ^ T
  | k + 1, 0 => 0
  | k + 1, T + 1 =>
      2 * markedCount n k T + (n - 2) * markedCount n (k + 1) T

def lowCount (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, 0 => 1
  | k + 1, T + 1 =>
      2 * lowCount n k T + (n - 2) * lowCount n (k + 1) T

theorem markedCount_eq_scaled_goodCount {n k T : Nat} (hn : 2 ≤ n) :
    2 ^ k * goodCount n k T = markedCount n k T := by
  induction k generalizing T with
  | zero => simp [markedCount, goodCount_zero]
  | succ k ih =>
      induction T with
      | zero => simp [markedCount, goodCount_empty]
      | succ T ihT =>
          rw [goodCount_step hn, markedCount]
          calc
            2 ^ (k + 1) *
                  (goodCount n k T + (n - 2) * goodCount n (k + 1) T) =
                2 * (2 ^ k * goodCount n k T) +
                  (n - 2) * (2 ^ (k + 1) * goodCount n (k + 1) T) := by
                    simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc,
                      Nat.mul_left_comm, Nat.mul_comm]
            _ = 2 * markedCount n k T +
                  (n - 2) * markedCount n (k + 1) T := by
                    rw [ih, ihT]

theorem markedCount_add_lowCount {n k T : Nat} (hn : 2 ≤ n) :
    markedCount n k T + lowCount n k T = n ^ T := by
  induction T generalizing k with
  | zero =>
      cases k <;> simp [markedCount, lowCount]
  | succ T ih =>
      cases k with
      | zero => simp [markedCount, lowCount]
      | succ k =>
          rw [markedCount, lowCount]
          have h1 := ih (k := k)
          have h2 := ih (k := k + 1)
          calc
            2 * markedCount n k T + (n - 2) * markedCount n (k + 1) T +
                  (2 * lowCount n k T + (n - 2) * lowCount n (k + 1) T) =
                2 * (markedCount n k T + lowCount n k T) +
                  (n - 2) * (markedCount n (k + 1) T +
                    lowCount n (k + 1) T) := by
                      simp only [Nat.mul_add]
                      ac_rfl
            _ = 2 * n ^ T + (n - 2) * n ^ T := by rw [h1, h2]
            _ = n ^ (T + 1) := by
              have hn' : 2 + (n - 2) = n := by omega
              calc
                2 * n ^ T + (n - 2) * n ^ T =
                    (2 + (n - 2)) * n ^ T := by
                      rw [Nat.add_mul]
                _ = n * n ^ T := by rw [hn']
                _ = n ^ T * n := by ac_rfl
                _ = n ^ (T + 1) := by simp [Nat.pow_succ]

theorem lowCount_le_half_weight {n T : Nat} (hn : 2 ≤ n) :
    ∀ k : Nat, lowCount n (k + 1) T ≤ 2 ^ k * (n - 1) ^ T := by
  induction T with
  | zero =>
      intro k
      simp [lowCount]
      exact Nat.one_le_pow k 2 (by decide)
  | succ T ih =>
      intro k
      cases k with
      | zero =>
          have h := ih 0
          simp at h
          have hmul := Nat.mul_le_mul_left (n - 2) h
          have hpow : (n - 2) * (n - 1) ^ T ≤
              (n - 1) * (n - 1) ^ T :=
            Nat.mul_le_mul_right _ (by omega)
          have hbound : (n - 2) * lowCount n 1 T ≤
                (n - 1) * (n - 1) ^ T := Nat.le_trans hmul hpow
          simpa [lowCount, Nat.pow_succ, Nat.mul_comm] using hbound
      | succ k =>
          rw [lowCount]
          have h1 := ih k
          have h2 := ih (k + 1)
          have h1' := Nat.mul_le_mul_left 2 h1
          have h2' := Nat.mul_le_mul_left (n - 2) h2
          have hsum := Nat.add_le_add h1' h2'
          have hpow2 : 2 * (2 ^ k * (n - 1) ^ T) =
                2 ^ (k + 1) * (n - 1) ^ T := by
            simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
          have hn' : 1 + (n - 2) = n - 1 := by omega
          have halg :
              2 * (2 ^ k * (n - 1) ^ T) +
                  (n - 2) * (2 ^ (k + 1) * (n - 1) ^ T) =
                (n - 1) * (2 ^ (k + 1) * (n - 1) ^ T) := by
            calc
              2 * (2 ^ k * (n - 1) ^ T) +
                    (n - 2) * (2 ^ (k + 1) * (n - 1) ^ T) =
                  2 ^ (k + 1) * (n - 1) ^ T +
                    (n - 2) * (2 ^ (k + 1) * (n - 1) ^ T) := by
                      rw [hpow2]
              _ = (1 + (n - 2)) *
                    (2 ^ (k + 1) * (n - 1) ^ T) := by
                      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
                        Nat.mul_left_comm, Nat.mul_comm]
              _ = (n - 1) * (2 ^ (k + 1) * (n - 1) ^ T) := by rw [hn']
          calc
            2 * lowCount n (k + 1) T +
                  (n - 2) * lowCount n (k + 1 + 1) T ≤
                2 * (2 ^ k * (n - 1) ^ T) +
                  (n - 2) * (2 ^ (k + 1) * (n - 1) ^ T) := hsum
            _ = (n - 1) * (2 ^ (k + 1) * (n - 1) ^ T) := halg
            _ = 2 ^ (k + 1) * (n - 1) ^ (T + 1) := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm]

/-! ## The denominator-cleared arithmetic handoff -/

theorem product_bounds_to_1085
    {N A0 G0 D : Nat}
    (hA : 5 * N ^ (3 * N) ≤ 64 * A0)
    (hG : 37 * N ^ (6 * N) ≤ 3136 * G0)
    (hfamily : A0 * G0 ≤ D) :
    N ^ (9 * N) ≤ 1085 * D := by
  have hmul := Nat.mul_le_mul hA hG
  have hpow : N ^ (3 * N) * N ^ (6 * N) = N ^ (9 * N) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hleft : 185 * N ^ (9 * N) ≤ 200704 * (A0 * G0) := by
    calc
      185 * N ^ (9 * N) =
          (5 * N ^ (3 * N)) * (37 * N ^ (6 * N)) := by
            calc
              185 * N ^ (9 * N) =
                  (5 * 37) * (N ^ (3 * N) * N ^ (6 * N)) := by
                    rw [hpow, show 185 = 5 * 37 by decide]
              _ = (5 * N ^ (3 * N)) * (37 * N ^ (6 * N)) := by
                    ac_rfl
      _ ≤ (64 * A0) * (3136 * G0) := hmul
      _ = 200704 * (A0 * G0) := by
        calc
          (64 * A0) * (3136 * G0) =
              (64 * 3136) * (A0 * G0) := by
                simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = 200704 * (A0 * G0) := by
                rw [show 64 * 3136 = 200704 by decide]
  have hright : 200704 * (A0 * G0) ≤ 200704 * D :=
    Nat.mul_le_mul_left _ hfamily
  have hmass : 185 * N ^ (9 * N) ≤ 200704 * D :=
    Nat.le_trans hleft hright
  exact mass_1085_of_mass_185_200704 hmass

/-! The concrete strict-drop numerator at horizon `T`.  This is the
`D_m(T)` that the final arithmetic handoff consumes. -/

def Dm (m T : Nat) : Nat :=
  (allSchedules (N m) T).countP (fun w => decide
    (barrierCount hk3 (ring m)
        (labelsOf (rawRun hk3 (ring m) S0 w)) <
      barrierCount hk3 (ring m) (labelsOf S0)))

theorem product_bounds_to_1085_Dm {m : Nat}
    (hA : 5 * (N m) ^ (3 * N m) ≤ 64 * A (N m))
    (hG : 37 * (N m) ^ (6 * N m) ≤ 3136 * G (N m))
    (hfamily : A (N m) * G (N m) ≤ Dm m (9 * N m)) :
    (N m) ^ (9 * N m) ≤ 1085 * Dm m (9 * N m) := by
  exact product_bounds_to_1085 hA hG hfamily

/-! A physical adaptive encoder supplies the single missing premise `hfamily`:
its injectivity identifies the `A(n)*G(n)` code pairs with distinct successful
raw words.  The theorem above deliberately keeps that semantic premise
explicit; it does not turn the fixed six-word cylinder into an adaptive one.
-/

end AAFJPK.N6m4ConstantMass
