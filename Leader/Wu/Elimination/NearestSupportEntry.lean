import Leader.Wu.Elimination.NearestSupportEntryObserver
import Leader.Core.BellmanGeometricTail

/-!
# Arbitrary-state nearest-support entry for the actual collision component

The scheduler alphabet is the original Fin n. At time 2 r n², the fraction
of words whose physical endpoint has neither nearest support nor zero
leaders is at most n / 2^r. Every statement is division-free. Proof marks
are erased to the identical complete UCell configuration on the same word.
This component theorem enables no leader birth and assumes no signal class.
-/

namespace K2NearestSupportEntry

open PPLL StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination
  K2PeacefulGlobal FiniteUniformStoppingTree LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

variable {n ψ κ : Nat}

private theorem sum_at_le {m : Nat} (f : Fin m → Nat) (i : Fin m) :
    f i ≤ (List.ofFn f).sum := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons]
    cases i using Fin.cases with
    | zero => exact Nat.le_add_right _ _
    | succ i => exact Nat.le_trans (ih (fun j => f j.succ) i) (Nat.le_add_left _ _)

/-- The zero outcome refers to the exact physical output count. -/
theorem count_zero_iff (C : Fin n → UCell ψ κ) :
    K2FiniteProgress.count C = 0 ↔ ¬ hasLeader n (observe C) := by
  constructor
  · intro hz hL
    obtain ⟨i, hi⟩ := hL
    have h := sum_at_le (fun i => if (C i).legacy.leader then 1 else 0) i
    change (C i).legacy.leader = true at hi
    rw [hi] at h
    rw [K2FiniteProgress.count_eq_sum] at hz
    simp only [↓reduceIte] at h
    omega
  · intro hL
    rw [K2FiniteProgress.count_eq_sum]
    have hf : ∀ i, (C i).legacy.leader = false := by
      intro i
      cases hi : (C i).legacy.leader with
      | false => rfl
      | true => exact False.elim (hL ⟨i, hi⟩)
    rw [ofFn_sum_eq _ (fun _ => 0) (by intro i; simp [hf i]), ofFn_sum_const]
    exact Nat.mul_zero _

/-- The actual endpoint condition, with physical zero leaders explicit. -/
def Entry (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  NearestPeaceful ring (observe C) ∨ K2FiniteProgress.count C = 0

/-- Once reached, entry is retained by this exact component. -/
theorem entry_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : Entry ring C) :
    Entry ring (AdjacentLeaderElimination.step hψ ring C e) := by
  rcases hC with hN | hz
  · exact Or.inl (AdjacentLeaderPeaceful.nearest_step hψ hn ring C hN e)
  · apply Or.inr
    apply (count_zero_iff _).2
    intro hL
    obtain ⟨i, hi⟩ := hL
    exact (count_zero_iff C).1 hz
      ⟨i, AdjacentLeaderElimination.step_leader_source hψ ring C e i hi⟩

theorem entry_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Entry ring C) (es : List (Fin n)) :
    Entry ring (run (AdjacentLeaderElimination.step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (entry_step hψ hn ring C e hC)

/-- Exact indicator of physical nonentry. -/
noncomputable def entryMiss (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Nat := by
  classical
  exact if Entry ring C then 0 else 1

/-- No mark at an endpoint implies nearest support or physical zero leaders. -/
theorem miss_le_marks (ring : DirectedRing n) (s : Observer ring ψ κ) :
    entryMiss ring s.C ≤ (List.ofFn (fun i => activeWeight (s.marks i))).sum := by
  classical
  unfold entryMiss
  split
  · exact Nat.zero_le _
  · rename_i h
    have hL : hasLeader n (observe s.C) := by
      by_cases hL : hasLeader n (observe s.C)
      · exact hL
      · exact False.elim (h (Or.inr ((count_zero_iff s.C).2 hL)))
    have hex : ∃ p, Bad ring s.C p := by
      by_cases hex : ∃ p, Bad ring s.C p
      · exact hex
      · apply False.elim
        apply h
        apply Or.inl
        intro p hp
        by_cases hs : ∃ d, Support ring (observe s.C) p d
        · exact hs
        · exact False.elim (hex ⟨p, hp, hs⟩)
    obtain ⟨p, hp⟩ := hex
    obtain ⟨i, a, hi, _⟩ := s.covers hL p hp
    have hs := sum_at_le (fun i => activeWeight (s.marks i)) i
    simpa only [hi, activeWeight] using hs

/-- Complete-state erasure also intertwines exact raw scheduler sums. -/
theorem wordSum_erases (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (w : (Fin n → UCell ψ κ) → Nat) (s : Observer ring ψ κ) (T : Nat) :
    wordSum (AdjacentLeaderElimination.step hψ ring) w s.C T =
      wordSum (observerStep hψ hn ring) (fun s => w s.C) s T := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    exact ofFn_sum_eq _ _ (fun e => ih (observerStep hψ hn ring s e))

private theorem sum_swap {m l : Nat} (f : Fin m → Fin l → Nat) :
    (List.ofFn (fun i => (List.ofFn (f i)).sum)).sum =
      (List.ofFn (fun j => (List.ofFn (fun i => f i j)).sum)).sum := by
  induction m with
  | zero => simp [ofFn_sum_const]
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, ih]
    symm
    calc
      (List.ofFn (fun j => (List.ofFn (fun i : Fin (m + 1) => f i j)).sum)).sum =
          (List.ofFn (fun j => f 0 j + (List.ofFn (fun i => f i.succ j)).sum)).sum := by
        apply ofFn_sum_eq
        intro j
        rw [List.ofFn_succ, List.sum_cons]
      _ = _ := ofFn_sum_add _ _

/-- Finite union over the n initial proof marks. Dependencies and coalescence
between marks are retained; no independence premise is used. -/
theorem observer_union (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : Observer ring ψ κ) (T : Nat) :
    wordSum (observerStep hψ hn ring) (fun s => entryMiss ring s.C) s T ≤
      (List.ofFn (fun i => activeCount (markStep hψ ring) (s.marks i) T)).sum := by
  induction T generalizing s with
  | zero => exact miss_le_marks ring s
  | succ T ih =>
    calc
      wordSum (observerStep hψ hn ring) (fun s => entryMiss ring s.C) s (T + 1) ≤
          (List.ofFn (fun e => (List.ofFn (fun i =>
            activeCount (markStep hψ ring) ((observerStep hψ hn ring s e).marks i) T)).sum)).sum :=
        ofFn_sum_le _ _ (fun e => ih (observerStep hψ hn ring s e))
      _ = _ := sum_swap _

/-- Uniform one-mark geometric tail from the produced actual-row Bellman
law. Each block has exactly 2n² original scheduler symbols. -/
theorem mark_tail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : StopNode (Mark ring ψ κ)) (r : Nat) :
    2 ^ r * activeCount (markStep hψ ring) s (r * (2 * (n * n))) ≤
      n ^ (r * (2 * (n * n))) :=
  BellmanGeometricTail.geometric_tail (markStep hψ ring) (markPotential ring)
    (mark_bellman hψ hn ring) (markPotential_bound ring) ring.hn s r

/-- From every existing finite configuration, nonentry at time 2rn² has
original raw word mass at most n/2^r. No initial bullet or signal premise. -/
theorem arbitrary_entry_tail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (r : Nat) :
    2 ^ r * wordSum (AdjacentLeaderElimination.step hψ ring) (entryMiss ring) C
        (r * (2 * (n * n))) ≤ n * n ^ (r * (2 * (n * n))) := by
  let s := initialObserver ring C
  have hu := observer_union hψ hn ring s (r * (2 * (n * n)))
  have he := wordSum_erases hψ hn ring (entryMiss ring) s (r * (2 * (n * n)))
  change wordSum (AdjacentLeaderElimination.step hψ ring) (entryMiss ring) C _ = _ at he
  rw [he]
  calc
    2 ^ r * wordSum (observerStep hψ hn ring) (fun s => entryMiss ring s.C) s
        (r * (2 * (n * n))) ≤
        2 ^ r * (List.ofFn (fun i => activeCount (markStep hψ ring) (s.marks i)
          (r * (2 * (n * n))))).sum := Nat.mul_le_mul_left _ hu
    _ = (List.ofFn (fun i => 2 ^ r * activeCount (markStep hψ ring) (s.marks i)
          (r * (2 * (n * n))))).sum := (ofFn_sum_mul_left _ _).symm
    _ ≤ (List.ofFn (fun _ : Fin n => n ^ (r * (2 * (n * n))))).sum :=
      ofFn_sum_le _ _ (fun i => mark_tail hψ hn ring (s.marks i) r)
    _ = _ := ofFn_sum_const _ _

/-- A convenient reciprocal form of the exact finite bound. -/
theorem arbitrary_entry_reciprocal (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (r q : Nat) (hq : n * q ≤ 2 ^ r) :
    q * wordSum (AdjacentLeaderElimination.step hψ ring) (entryMiss ring) C
        (r * (2 * (n * n))) ≤ n ^ (r * (2 * (n * n))) := by
  have h := arbitrary_entry_tail hψ hn ring C r
  have hh := Nat.le_trans (Nat.mul_le_mul_right
    (wordSum (AdjacentLeaderElimination.step hψ ring) (entryMiss ring) C
      (r * (2 * (n * n)))) hq) h
  rw [Nat.mul_assoc] at hh
  exact Nat.le_of_mul_le_mul_left hh ring.hn

/-- Polynomially small nonentry mass in a concrete O(n² log n) raw horizon.
The exponent c is arbitrary; the bound retains every original scheduler word. -/
theorem arbitrary_entry_polynomial_tail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (c : Nat) :
    let T := ((c + 1) * (Nat.log2 n + 1)) * (2 * (n * n))
    n ^ c * wordSum (AdjacentLeaderElimination.step hψ ring) (entryMiss ring) C T ≤ n ^ T := by
  apply arbitrary_entry_reciprocal hψ hn ring C
  have hn0 : n ≠ 0 := by have := ring.hn; omega
  have hlog : n ≤ 2 ^ (Nat.log2 n + 1) :=
    Nat.le_of_lt ((Nat.log2_lt hn0).1 (by omega))
  calc
    n * n ^ c = n ^ (c + 1) := by rw [Nat.pow_succ]; ac_rfl
    _ ≤ (2 ^ (Nat.log2 n + 1)) ^ (c + 1) := Nat.pow_le_pow_left hlog _
    _ = 2 ^ ((c + 1) * (Nat.log2 n + 1)) := by rw [← Nat.pow_mul]; ac_rfl

/-- The displayed logarithmic clock is at most 4(c+1)n² floor(log₂ n). -/
theorem polynomial_clock_le (hn : 1 < n) (c : Nat) :
    ((c + 1) * (Nat.log2 n + 1)) * (2 * (n * n)) ≤
      4 * (c + 1) * n * n * Nat.log2 n := by
  have hl := (LeaderCountDyadicTail.log_parameters n (by omega)).1
  have hlog : Nat.log2 n + 1 ≤ 2 * Nat.log2 n := by omega
  calc
    ((c + 1) * (Nat.log2 n + 1)) * (2 * (n * n)) ≤
        ((c + 1) * (2 * Nat.log2 n)) * (2 * (n * n)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlog)
    _ = _ := by simp only [show (4 : Nat) = 2 * 2 from rfl]; ac_rfl

/-- A single-site ring is handled by its literal aliasing row. The sole
output is a follower after one step, including a self-collision. -/
theorem singleton_count_zero (hψ : 0 < ψ) (ring : DirectedRing 1)
    (C : Fin 1 → UCell ψ κ) (e : Fin 1) :
    K2FiniteProgress.count (AdjacentLeaderElimination.step hψ ring C e) = 0 := by
  apply (count_zero_iff _).2
  rintro ⟨i, hi⟩
  have he : i = e := Subsingleton.elim _ _
  subst i
  have hf : (AdjacentLeaderElimination.step hψ ring C e e).legacy.leader = false := by
    cases hl : (C e).legacy.leader with
    | false => exact AdjacentLeaderElimination.step_follower hψ ring C e e hl
    | true =>
      apply AdjacentLeaderElimination.adjacent_deletes_source hψ ring C e hl
      have hr : ring.rightNeighbor e = e := Subsingleton.elim _ _
      simpa only [hr] using hl
  change (AdjacentLeaderElimination.step hψ ring C e e).legacy.leader = true at hi
  rw [hi] at hf
  cases hf

end K2NearestSupportEntry

#print axioms K2NearestSupportEntry.count_zero_iff
#print axioms K2NearestSupportEntry.entry_step
#print axioms K2NearestSupportEntry.wordSum_erases
#print axioms K2NearestSupportEntry.observer_union
#print axioms K2NearestSupportEntry.arbitrary_entry_tail
#print axioms K2NearestSupportEntry.arbitrary_entry_polynomial_tail

#print axioms K2NearestSupportEntry.polynomial_clock_le
#print axioms K2NearestSupportEntry.singleton_count_zero
