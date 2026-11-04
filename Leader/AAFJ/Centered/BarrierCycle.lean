import Leader.AAFJ.Centered.CoalescenceFrame

/-!
# Cyclic barrier-gap certificate for centered coalescence

This proof-only layer turns the duplicate-free charged support into its
clockwise cyclic order and records the exact physical and phase-corrected gap
budgets used by a centered coalescence trial.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace CoalescenceCycle

open BarrierAlgebra

set_option autoImplicit false

/-! ## Generic clockwise gap arithmetic -/

/-- Last edge of a nonempty list represented by its head and remaining tail. -/
def endEdge {n : Nat} (first : Fin n) : List (Fin n) → Fin n
  | [] => first
  | edge :: rest => endEdge edge rest

/-- Forward (non-wrapping) gaps after a fixed first edge. -/
def forwardGaps {n : Nat} (first : Fin n) : List (Fin n) → List Nat
  | [] => []
  | edge :: rest =>
      (edge.val - first.val) :: forwardGaps edge rest

@[simp] theorem forwardGaps_length {n : Nat} (first : Fin n)
    (rest : List (Fin n)) :
    (forwardGaps first rest).length = rest.length := by
  induction rest generalizing first with
  | nil => rfl
  | cons edge rest ih => simp [forwardGaps, ih]

/-- Forward gaps telescope from the first edge to the last edge. -/
theorem forwardGaps_sum_add_first {n : Nat} (first : Fin n)
    (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    (forwardGaps first rest).sum + first.val = (endEdge first rest).val := by
  induction rest generalizing first with
  | nil => simp [forwardGaps, endEdge]
  | cons edge rest ih =>
      rw [List.pairwise_cons] at horder
      have hlt : first.val < edge.val := horder.1 edge (by simp)
      have htail : (edge :: rest).Pairwise (fun a b => a.val < b.val) :=
        horder.2
      have hih := ih edge htail
      simp only [forwardGaps, List.sum_cons, endEdge]
      omega

/-- Every forward gap in a strictly increasing edge list is positive. -/
theorem forwardGaps_pos {n : Nat} (first : Fin n)
    (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    ∀ gap, gap ∈ forwardGaps first rest → 0 < gap := by
  induction rest generalizing first with
  | nil => simp [forwardGaps]
  | cons edge rest ih =>
      rw [List.pairwise_cons] at horder
      have hlt : first.val < edge.val := horder.1 edge (by simp)
      have htail : (edge :: rest).Pairwise (fun a b => a.val < b.val) :=
        horder.2
      intro gap hgap
      simp only [forwardGaps, List.mem_cons] at hgap
      rcases hgap with rfl | hgap
      · omega
      · exact ih edge htail gap hgap

/-- Clockwise physical gaps of a strictly increasing cyclic edge list.  The
last entry is the wrap from the largest edge back to the smallest edge. -/
def cyclicGaps (n : Nat) : List (Fin n) → List Nat
  | [] => []
  | first :: rest =>
      forwardGaps first rest ++
        [n - (endEdge first rest).val + first.val]

theorem cyclicGaps_length (n : Nat) (support : List (Fin n)) :
    (cyclicGaps n support).length = support.length := by
  cases support with
  | nil => rfl
  | cons first rest => simp [cyclicGaps, forwardGaps_length]

/-- A nonempty strictly increasing cyclic list partitions the ring into
positive clockwise gaps. -/
theorem cyclicGaps_pos {n : Nat} (first : Fin n)
    (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    ∀ gap, gap ∈ cyclicGaps n (first :: rest) → 0 < gap := by
  intro gap hgap
  simp only [cyclicGaps, List.mem_append, List.mem_cons, List.not_mem_nil] at hgap
  rcases hgap with hforward | hwrap
  · exact forwardGaps_pos first rest horder gap hforward
  · rcases hwrap with hwrap | hfalse
    · subst gap
      have hend : (endEdge first rest).val < n := (endEdge first rest).isLt
      omega
    · contradiction

/-- The clockwise physical gaps telescope exactly once around the ring. -/
theorem cyclicGaps_sum {n : Nat} (first : Fin n)
    (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    (cyclicGaps n (first :: rest)).sum = n := by
  have hforward := forwardGaps_sum_add_first first rest horder
  have hend : (endEdge first rest).val < n := (endEdge first rest).isLt
  simp only [cyclicGaps, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  omega

/-! ## Phase-corrected doubled gaps -/

/-- The centered barrier clock as a natural bit. -/
def phaseBit {n k : Nat} (C : Fin n → State k) (edge : Fin n) : Nat :=
  CenteredRenewal.phaseNat (C edge).phase

theorem phaseBit_le_one {n k : Nat} (C : Fin n → State k) (edge : Fin n) :
    phaseBit C edge ≤ 1 := by
  cases h : (C edge).phase <;> simp [phaseBit, CenteredRenewal.phaseNat, h]

/-- Corrected forward gaps.  A phase-one rear is one half-step closer to its
front, while a phase-one front is one half-step farther away. -/
def correctedForward {n k : Nat} (C : Fin n → State k)
    (first : Fin n) : List (Fin n) → List Nat
  | [] => []
  | edge :: rest =>
      (2 * (edge.val - first.val) + phaseBit C edge - phaseBit C first) ::
        correctedForward C edge rest

@[simp] theorem correctedForward_length {n k : Nat}
    (C : Fin n → State k) (first : Fin n) (rest : List (Fin n)) :
    (correctedForward C first rest).length = rest.length := by
  induction rest generalizing first with
  | nil => rfl
  | cons edge rest ih => simp [correctedForward, ih]

/-- The phase correction telescopes together with twice the physical
coordinate. -/
theorem correctedForward_sum_add_first {n k : Nat}
    (C : Fin n → State k) (first : Fin n) (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    (correctedForward C first rest).sum +
        (2 * first.val + phaseBit C first) =
      2 * (endEdge first rest).val + phaseBit C (endEdge first rest) := by
  induction rest generalizing first with
  | nil => simp [correctedForward, endEdge]
  | cons edge rest ih =>
      rw [List.pairwise_cons] at horder
      have hlt : first.val < edge.val := horder.1 edge (by simp)
      have htail : (edge :: rest).Pairwise (fun a b => a.val < b.val) :=
        horder.2
      have hih := ih edge htail
      have hpfirst := phaseBit_le_one C first
      simp only [correctedForward, List.sum_cons, endEdge]
      omega

theorem correctedForward_pos {n k : Nat} (C : Fin n → State k)
    (first : Fin n) (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    ∀ gap, gap ∈ correctedForward C first rest → 0 < gap := by
  induction rest generalizing first with
  | nil => simp [correctedForward]
  | cons edge rest ih =>
      rw [List.pairwise_cons] at horder
      have hlt : first.val < edge.val := horder.1 edge (by simp)
      have htail : (edge :: rest).Pairwise (fun a b => a.val < b.val) :=
        horder.2
      intro gap hgap
      simp only [correctedForward, List.mem_cons] at hgap
      rcases hgap with rfl | hgap
      · have hpfirst := phaseBit_le_one C first
        omega
      · exact ih edge htail gap hgap

/-- Doubled physical gaps corrected by the two endpoint phases. -/
def correctedCyclicGaps {n k : Nat} (C : Fin n → State k) :
    List (Fin n) → List Nat
  | [] => []
  | first :: rest =>
      correctedForward C first rest ++
        [2 * (n - (endEdge first rest).val + first.val) +
          phaseBit C first - phaseBit C (endEdge first rest)]

theorem correctedCyclicGaps_length {n k : Nat} (C : Fin n → State k)
    (support : List (Fin n)) :
    (correctedCyclicGaps C support).length = support.length := by
  cases support with
  | nil => rfl
  | cons first rest => simp [correctedCyclicGaps, correctedForward_length]

theorem correctedCyclicGaps_pos {n k : Nat} (C : Fin n → State k)
    (first : Fin n) (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    ∀ gap, gap ∈ correctedCyclicGaps C (first :: rest) → 0 < gap := by
  intro gap hgap
  simp only [correctedCyclicGaps, List.mem_append, List.mem_cons,
    List.not_mem_nil] at hgap
  rcases hgap with hforward | hwrap
  · exact correctedForward_pos C first rest horder gap hforward
  · rcases hwrap with hwrap | hfalse
    · subst gap
      have hend : (endEdge first rest).val < n := (endEdge first rest).isLt
      have hpend := phaseBit_le_one C (endEdge first rest)
      omega
    · contradiction

/-- Phase corrections telescope on the cycle, so the corrected doubled gaps
sum to exactly twice the ring length. -/
theorem correctedCyclicGaps_sum {n k : Nat} (C : Fin n → State k)
    (first : Fin n) (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    (correctedCyclicGaps C (first :: rest)).sum = 2 * n := by
  have hforward := correctedForward_sum_add_first C first rest horder
  have hend : (endEdge first rest).val < n := (endEdge first rest).isLt
  have hpend := phaseBit_le_one C (endEdge first rest)
  simp only [correctedCyclicGaps, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]
  omega

/-! ## Charged-support cycle certificate -/

/-- Filtering the canonical `Fin n` enumeration preserves its strict physical
order. -/
theorem barrierSupport_pairwise_val_lt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) :
    (barrierSupport hk ring L).Pairwise (fun a b => a.val < b.val) := by
  unfold barrierSupport
  change (List.finRange n).filter
      (fun e => decide (BarrierAt hk ring L e)) |>.Pairwise
        (fun a b => a.val < b.val)
  exact (List.pairwise_lt_finRange n).filter _

/-- Proof-only cyclic enumeration of all charged barriers in one snapshot.
The support is definitionally tied to `barrierSupport`; its additional fields
make duplicate freedom, exhaustiveness, physical order, and cardinality
available without reopening the list filter. -/
structure BarrierCycle {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (m : Nat) where
  support : List (Fin n)
  support_eq : support = barrierSupport hk ring (labelsOf C)
  length_eq : support.length = m
  nodup : support.Nodup
  charged_iff_mem : ∀ edge, edge ∈ support ↔
    BarrierAt hk ring (labelsOf C) edge
  ordered : support.Pairwise (fun a b => a.val < b.val)
  nonempty : support ≠ []

/-- The existing charged support and count canonically produce the exact
cyclic certificate. -/
theorem exists_barrierCycle {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (hm : barrierCount hk ring (labelsOf C) = m) (hmpos : 0 < m) :
    Nonempty (BarrierCycle hk ring C m) := by
  refine ⟨{
    support := barrierSupport hk ring (labelsOf C)
    support_eq := rfl
    length_eq := ?_
    nodup := barrierSupport_nodup hk ring (labelsOf C)
    charged_iff_mem := fun edge =>
      mem_barrierSupport_iff hk ring (labelsOf C) edge
    ordered := barrierSupport_pairwise_val_lt hk ring (labelsOf C)
    nonempty := ?_ }⟩
  · simpa [barrierCount] using hm
  · intro hempty
    have hlen : (barrierSupport hk ring (labelsOf C)).length = 0 := by
      simp [hempty]
    have hmzero : m = 0 := by
      rw [← hm]
      simpa [barrierCount] using hlen
    omega

namespace BarrierCycle

/-- A charged-support cycle cannot contain more edges than the ring. -/
theorem length_le_ring {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) : m ≤ n := by
  have hsubset : cycle.support ⊆ List.finRange n := by
    intro edge _
    simp
  have hlength : cycle.support.length ≤ (List.finRange n).length :=
    cycle.nodup.length_le_of_subset hsubset
  simpa [cycle.length_eq] using hlength

/-- Physical clockwise gaps attached to the canonical support cycle. -/
def gaps {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m) : List Nat :=
  cyclicGaps n cycle.support

/-- Phase-corrected doubled gaps attached to the same snapshot cycle. -/
def doubledGaps {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m) : List Nat :=
  correctedCyclicGaps C cycle.support

theorem gaps_length {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m) :
    cycle.gaps.length = m := by
  rw [gaps, cyclicGaps_length, cycle.length_eq]

theorem doubledGaps_length {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) :
    cycle.doubledGaps.length = m := by
  rw [doubledGaps, correctedCyclicGaps_length, cycle.length_eq]

/-- Every physical gap between consecutive charged edges is positive. -/
theorem gaps_pos {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m) :
    ∀ gap, gap ∈ cycle.gaps → 0 < gap := by
  cases hs : cycle.support with
  | nil => exact (cycle.nonempty hs).elim
  | cons first rest =>
      have horder : (first :: rest).Pairwise
          (fun a b => a.val < b.val) := by
        simpa [hs] using cycle.ordered
      simpa [gaps, hs] using cyclicGaps_pos first rest horder

/-- The physical gaps partition the ring exactly once. -/
theorem gaps_sum_eq_n {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) :
    cycle.gaps.sum = n := by
  cases hs : cycle.support with
  | nil => exact (cycle.nonempty hs).elim
  | cons first rest =>
      have horder : (first :: rest).Pairwise
          (fun a b => a.val < b.val) := by
        simpa [hs] using cycle.ordered
      simpa [gaps, hs] using cyclicGaps_sum first rest horder

/-- Every phase-corrected doubled gap is still positive. -/
theorem doubledGaps_pos {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) :
    ∀ gap, gap ∈ cycle.doubledGaps → 0 < gap := by
  cases hs : cycle.support with
  | nil => exact (cycle.nonempty hs).elim
  | cons first rest =>
      have horder : (first :: rest).Pairwise
          (fun a b => a.val < b.val) := by
        simpa [hs] using cycle.ordered
      simpa [doubledGaps, hs] using
        correctedCyclicGaps_pos C first rest horder

/-- The phase-corrected doubled gaps have exact cyclic total `2n`. -/
theorem doubledGaps_sum_eq_two_mul_n {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) :
    cycle.doubledGaps.sum = 2 * n := by
  cases hs : cycle.support with
  | nil => exact (cycle.nonempty hs).elim
  | cons first rest =>
      have horder : (first :: rest).Pairwise
          (fun a b => a.val < b.val) := by
        simpa [hs] using cycle.ordered
      simpa [doubledGaps, hs] using
        correctedCyclicGaps_sum C first rest horder

/-- The charged edge at cyclic support index `j`. -/
def edge {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m)
    (j : Fin m) : Fin n :=
  cycle.support.get ⟨j.val, by rw [cycle.length_eq]; exact j.isLt⟩

/-- The physical gap at cyclic support index `j`. -/
def gap {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m)
    (j : Fin m) : Nat :=
  cycle.gaps.get ⟨j.val, by rw [cycle.gaps_length]; exact j.isLt⟩

/-- The phase-corrected doubled gap at cyclic support index `j`. -/
def doubledGap {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} (cycle : BarrierCycle hk ring C m)
    (j : Fin m) : Nat :=
  cycle.doubledGaps.get
    ⟨j.val, by rw [cycle.doubledGaps_length]; exact j.isLt⟩

theorem edge_charged {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) (j : Fin m) :
    BarrierAt hk ring (labelsOf C) (cycle.edge j) := by
  rw [← cycle.charged_iff_mem]
  exact List.get_mem _ _

/-- The indexed edges exhaust all charged barriers. -/
theorem exists_edge_eq_of_charged {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) (physical : Fin n)
    (hcharged : BarrierAt hk ring (labelsOf C) physical) :
    ∃ j : Fin m, cycle.edge j = physical := by
  have hmem : physical ∈ cycle.support :=
    (cycle.charged_iff_mem physical).2 hcharged
  rw [List.mem_iff_get] at hmem
  obtain ⟨i, hi⟩ := hmem
  let j : Fin m := ⟨i.val, by
    have hit := i.isLt
    have hlen := cycle.length_eq
    omega⟩
  refine ⟨j, ?_⟩
  unfold edge
  have hindex :
      (⟨j.val, by rw [cycle.length_eq]; exact j.isLt⟩ :
        Fin cycle.support.length) = i := by
    apply Fin.ext
    rfl
  rw [hindex, hi]

theorem gap_pos {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) (j : Fin m) :
    0 < cycle.gap j :=
  cycle.gaps_pos _ (List.get_mem _ _)

theorem doubledGap_pos {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) (j : Fin m) :
    0 < cycle.doubledGap j :=
  cycle.doubledGaps_pos _ (List.get_mem _ _)

/-! ## Division-free minimum-gap certificate -/

/-- Minimum of an explicitly nonempty natural-number list. -/
def minWith (first : Nat) : List Nat → Nat
  | [] => first
  | value :: rest => Nat.min first (minWith value rest)

theorem minWith_mem (first : Nat) (rest : List Nat) :
    minWith first rest ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp [minWith]
  | cons value rest ih =>
      by_cases h : first ≤ minWith value rest
      · simp [minWith, Nat.min_eq_left h]
      · have hle : minWith value rest ≤ first := by omega
        have heq : minWith first (value :: rest) = minWith value rest := by
          simp [minWith, Nat.min_eq_right hle]
        rw [heq]
        exact List.Mem.tail first (ih value)

theorem minWith_le_of_mem (first : Nat) (rest : List Nat) (value : Nat)
    (hmem : value ∈ first :: rest) : minWith first rest ≤ value := by
  induction rest generalizing first with
  | nil =>
      have heq : value = first := by simpa using hmem
      subst value
      simp [minWith]
  | cons next rest ih =>
      cases hmem with
      | head => exact Nat.min_le_left _ _
      | tail _ htail =>
          exact Nat.le_trans (Nat.min_le_right _ _) (ih next htail)

/-- A finite nonempty list has an entry at most its average, stated without
division. -/
theorem length_mul_minWith_le_sum (first : Nat) (rest : List Nat) :
    (first :: rest).length * minWith first rest ≤ (first :: rest).sum := by
  induction rest generalizing first with
  | nil => simp [minWith]
  | cons value rest ih =>
      have hfirst : minWith first (value :: rest) ≤ first :=
        minWith_le_of_mem first (value :: rest) first (by simp)
      have htail : minWith first (value :: rest) ≤ minWith value rest :=
        Nat.min_le_right _ _
      calc
        (first :: value :: rest).length * minWith first (value :: rest) =
            minWith first (value :: rest) +
              (value :: rest).length * minWith first (value :: rest) := by
                simp only [List.length_cons, Nat.succ_mul]
                omega
        _ ≤ first + (value :: rest).length * minWith value rest :=
          Nat.add_le_add hfirst (Nat.mul_le_mul_left _ htail)
        _ ≤ first + (value :: rest).sum :=
          Nat.add_le_add_left (ih value) first
        _ = (first :: value :: rest).sum := by simp

/-- Some phase-corrected doubled gap `q₀` satisfies the exact multiplication
bound `m*q₀ ≤ 2n`.  This is the division-free minimum-gap certificate used by
the cubic coalescence estimate. -/
theorem exists_min_doubledGap_mul_le {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n → State k}
    (cycle : BarrierCycle hk ring C m) :
    ∃ j : Fin m, m * cycle.doubledGap j ≤ 2 * n := by
  cases hlist : cycle.doubledGaps with
  | nil =>
      have hlen := cycle.doubledGaps_length
      rw [hlist] at hlen
      have hmpos : 0 < m := by
        have hslen := cycle.length_eq
        have hsne := cycle.nonempty
        cases hs : cycle.support with
        | nil => exact (hsne hs).elim
        | cons first rest =>
            rw [hs] at hslen
            simp at hslen
            omega
      simp at hlen
      omega
  | cons first rest =>
      let q0 := minWith first rest
      have hbound0 := length_mul_minWith_le_sum first rest
      have hlen : (first :: rest).length = m := by
        rw [← hlist]
        exact cycle.doubledGaps_length
      have hsum : (first :: rest).sum = 2 * n := by
        rw [← hlist]
        exact cycle.doubledGaps_sum_eq_two_mul_n
      have hbound : m * q0 ≤ 2 * n := by
        rw [hlen, hsum] at hbound0
        exact hbound0
      have hmem : q0 ∈ cycle.doubledGaps := by
        rw [hlist]
        exact minWith_mem first rest
      rw [List.mem_iff_get] at hmem
      obtain ⟨i, hi⟩ := hmem
      let j : Fin m := ⟨i.val, by
        have hit := i.isLt
        have hlen' := cycle.doubledGaps_length
        omega⟩
      refine ⟨j, ?_⟩
      have hgap : cycle.doubledGap j = q0 := by
        unfold doubledGap
        have hindex :
            (⟨j.val, by rw [cycle.doubledGaps_length]; exact j.isLt⟩ :
              Fin cycle.doubledGaps.length) = i := by
          apply Fin.ext
          rfl
        rw [hindex, hi]
      simpa [hgap] using hbound

end BarrierCycle

end CoalescenceCycle

end CenteredRenewal
end AAFJPK
