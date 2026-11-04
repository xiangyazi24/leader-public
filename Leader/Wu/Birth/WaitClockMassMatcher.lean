import Leader.Core.ControlledSchedulerMass
import Leader.Core.PredictableTwoTargetFiniteTree

/-!
# Ordered service patterns before one killing edge

The raw matcher reads every original edge.  It fails at the killing edge,
advances only on the next requested edge, and absorbs once the whole pattern
has appeared.  Its comparison maps both the requested and killing edges to
the same advance.  Every successful raw word has exactly two preimages per
requested letter, including words padded after their successful prefix.
-/

namespace BirthWaitClockMass.Matcher

open FiniteUniformStoppingTree PredictableTwoTargetFiniteTree

set_option autoImplicit false
set_option Elab.async false

structure Pending {n : Nat} (kill : Fin n) where
  head : Fin n
  tail : List (Fin n)
  avoid : kill ∉ head :: tail

def Pending.word {n : Nat} {kill : Fin n} (p : Pending kill) : List (Fin n) :=
  p.head :: p.tail

def Pending.length {n : Nat} {kill : Fin n} (p : Pending kill) : Nat := p.word.length

theorem Pending.distinct {n : Nat} {kill : Fin n} (p : Pending kill) : p.head ≠ kill := by
  intro he
  exact p.avoid (by simp [he])

def advance {n : Nat} {kill : Fin n} : Pending kill → StopNode (Pending kill)
  | ⟨_, [], _⟩ => .success
  | ⟨a, b :: rest, h⟩ => .active ⟨b, rest, fun hm => h (List.mem_cons_of_mem a hm)⟩

theorem advance_nil {n : Nat} {kill : Fin n} (p : Pending kill) (ht : p.tail = []) :
    advance p = .success := by cases p; cases ht; rfl

theorem advance_cons {n : Nat} {kill : Fin n} (p : Pending kill)
    (a : Fin n) (rest : List (Fin n)) (ht : p.tail = a :: rest) :
    advance p = .active ⟨a, rest, by
      intro hm
      exact p.avoid (List.mem_cons_of_mem p.head (by simpa [ht] using hm))⟩ := by
  cases p
  cases ht
  rfl

def raw {n : Nat} {kill : Fin n} (p : Pending kill) (e : Fin n) : StopNode (Pending kill) :=
  if e = kill then .failure else if e = p.head then advance p else .active p

def controlled {n : Nat} {kill : Fin n}
    (p : Pending kill) (e : Fin n) : StopNode (Pending kill) :=
  if e = p.head ∨ e = kill then advance p else .active p

def remaining {n : Nat} {kill : Fin n} : StopNode (Pending kill) → Nat
  | .active p => p.length
  | _ => 0

@[simp] theorem advance_remaining {n : Nat} {kill : Fin n} (p : Pending kill) :
    remaining (advance p) + 1 = p.length := by
  cases p with
  | mk a tail h => cases tail <;> simp [advance, remaining, Pending.length, Pending.word]

theorem advance_ne_failure {n : Nat} {kill : Fin n} (p : Pending kill) :
    advance p ≠ .failure := by cases p with | mk a tail h => cases tail <;> simp [advance]

theorem failure_zero {n : Nat} {kill : Fin n} (p : Pending kill) (T : Nat) :
    failureCount controlled (.active p) T = 0 := by
  induction T generalizing p with
  | zero => rfl
  | succ T ih =>
    unfold failureCount
    rw [treeWeight]
    apply Eq.trans (ofFn_sum_eq _ (fun _ => 0) ?_) (by simp [ofFn_sum_const])
    intro e
    simp only [stepNode, controlled]
    split
    · cases ht : p.tail
      · rw [advance_nil p ht, treeWeight_success]
        simp [failureWeight]
      · rw [advance_cons p _ _ ht]
        exact ih _
    · exact ih p

theorem remaining_sum {n : Nat} {kill : Fin n} (p : Pending kill) :
    2 + (List.ofFn (fun e => remaining (controlled p e))).sum = n * p.length := by
  have hn : 2 ≤ n := by
    have ha := p.head.isLt
    have hb := kill.isLt
    have hd := p.distinct
    have hv : p.head.val ≠ kill.val := fun he => hd (Fin.ext he)
    omega
  have hs := ofFn_sum_two_values_else_const p.head kill
    (fun e => remaining (controlled p e)) p.length p.distinct (by
      intro e ha hb
      simp [controlled, ha, hb, remaining])
  have hd := advance_remaining p
  rw [hs]
  simp only [controlled, true_or, or_true, if_true]
  have he : n = (n - 2) + 2 := by omega
  have hm := congrArg (· * p.length) he
  rw [Nat.add_mul, Nat.two_mul] at hm
  omega

def potential {n : Nat} {kill : Fin n} (x : StopNode (Pending kill)) : Nat :=
  n * remaining x

theorem bellman {n : Nat} {kill : Fin n} :
    NatBellmanSuperSolution (controlled (kill := kill)) 2 potential := by
  refine ⟨by simp [potential, remaining], by simp [potential, remaining], ?_⟩
  intro p
  simp only [potential]
  rw [ofFn_sum_mul_left]
  have h := congrArg (n * ·) (remaining_sum p)
  simpa only [Nat.mul_add, Nat.mul_comm n 2, remaining] using Nat.le_of_eq h

/-- The comparison completes at least half the full raw tree by `n*L`.
No fair stream or service-time distribution is a premise. -/
theorem controlled_half {n : Nat} {kill : Fin n} (p : Pending kill) :
    n ^ (n * p.length) ≤ 2 * successCount controlled (.active p) (n * p.length) := by
  let T := n * p.length
  have hn : 0 < n := by have := kill.isLt; omega
  have hp : 0 < p.length := by simp [Pending.length, Pending.word]
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    controlled 2 potential bellman (.active p) T
  have hhalf := two_mul_activeCount_le_pow_of_scaled_cost
    controlled (.active p) (Nat.mul_pos hn hp) (by decide : 0 < 2)
    (num := n * p.length) (by simpa [potential, remaining, Nat.mul_comm] using hcost)
    (by omega)
  have hpart := node_count_partition controlled (.active p) T
  have hz := failure_zero p T
  dsimp [T] at *
  omega

/-- The exact finite fiber count: both distinguished raw choices are charged
at each requested letter; padding after success contributes no extra factor. -/
theorem success_count_eq {n : Nat} {kill : Fin n} (p : Pending kill) (T : Nat) :
    successCount controlled (.active p) T =
      2 ^ p.length * successCount raw (.active p) T := by
  induction T generalizing p with
  | zero => simp [successCount, treeWeight, successWeight]
  | succ T ih =>
    have hctrl := ofFn_sum_two_values_else_const p.head kill
      (fun e => successCount controlled (controlled p e) T)
      (successCount controlled (.active p) T) p.distinct (by
        intro e ha hb
        simp [controlled, ha, hb])
    have hraw := ofFn_sum_two_values_else_const p.head kill
      (fun e => successCount raw (raw p e) T)
      (successCount raw (.active p) T) p.distinct (by
        intro e ha hb
        simp [raw, ha, hb])
    have hnext : 2 * successCount controlled (advance p) T =
        2 ^ p.length * successCount raw (advance p) T := by
      cases ht : p.tail with
      | nil =>
        rw [advance_nil p ht]
        simp [ht, Pending.length, Pending.word, successCount,
          treeWeight_success, successWeight]
      | cons a rest =>
        let q : Pending kill := ⟨a, rest, by
          intro hm
          exact p.avoid (List.mem_cons_of_mem p.head (by simpa [ht] using hm))⟩
        have he : p.length = q.length + 1 := by
          simp [Pending.length, Pending.word, ht, q]
        rw [advance_cons p a rest ht]
        change 2 * successCount controlled (.active q) T =
          2 ^ p.length * successCount raw (.active q) T
        rw [ih q, he, Nat.pow_succ]
        ac_rfl
    change (List.ofFn (fun e => successCount controlled (controlled p e) T)).sum =
      2 ^ p.length * (List.ofFn (fun e => successCount raw (raw p e) T)).sum
    rw [hctrl, hraw]
    simp only [controlled, raw, p.distinct, if_false, if_true, true_or, or_true,
      successCount, treeWeight_failure, successWeight, Nat.mul_zero, Nat.add_zero]
    change successCount controlled (advance p) T + successCount controlled (advance p) T +
        (n - 2) * successCount controlled (.active p) T =
      2 ^ p.length * (successCount raw (advance p) T +
        (n - 2) * successCount raw (.active p) T)
    rw [← Nat.two_mul, hnext, ih p, Nat.mul_add]
    congr 1
    ac_rfl

theorem raw_half_fiber_mass {n : Nat} {kill : Fin n} (p : Pending kill) :
    n ^ (n * p.length) ≤
      2 ^ (p.length + 1) * successCount raw (.active p) (n * p.length) := by
  have h := controlled_half p
  rw [success_count_eq] at h
  rw [Nat.pow_succ]
  simpa only [Nat.mul_assoc, Nat.mul_left_comm 2] using h

end BirthWaitClockMass.Matcher

#print axioms BirthWaitClockMass.Matcher.bellman
#print axioms BirthWaitClockMass.Matcher.success_count_eq
#print axioms BirthWaitClockMass.Matcher.raw_half_fiber_mass
