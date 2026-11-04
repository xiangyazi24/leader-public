import Leader.AAFJ.NonbarrierWord
import Leader.AAFJ.OneBarrier.Sanitation

/-!
# Counterexample to the one-shot leader-elimination step in Lemma 9.2

The proof of Lemma 9.2 on printed page 26 of Angluin--Aspnes--Fischer--Jiang,
*Self-stabilizing Population Protocols*, says to choose the leader farthest
counterclockwise from the unique barrier, fire one bullet, and propagate it
until the barrier absorbs it.  It then says, "Now at most one leader remains."

The closed `n = 3`, `k = 2` trace below satisfies the phase premises in the
strong form: one barrier, exactly two leaders, no bullets, no probes, and a
unique farthest leader.  The literal word `[1, 0, 2]` fires that leader, moves
the bullet to the barrier head, and performs the absorbing barrier hit.  Both
leaders remain.  This refutes that proof-step implication, but does not refute
the statement of Lemma 9.2 or the later theorems.
-/

set_option autoImplicit false

namespace AAFJPK.JournalLemma92LeaderEliminationCounterexample

open BarrierAlgebra
open OriginalNonbarrierWord
open SingleBarrierSanitation

private theorem hk2 : 0 < (2 : Nat) := by decide
set_option linter.defProp false in
private def ring3 : DirectedRing 3 := ⟨by decide⟩

private def head : Fin 3 := 0
private def mid : Fin 3 := 1
private def tail : Fin 3 := 2

/-- Initial state: labels `[0,1,0]`, leaders `{0,2}`, no bullets or probes,
and phase true only at the unique barrier tail `2`. -/
def C (i : Fin 3) : State 2 :=
  if i = head then
    { bullet := false, leader := true, label := 0,
      probe := false, phase := false }
  else if i = mid then
    { bullet := false, leader := false, label := 1,
      probe := false, phase := false }
  else
    { bullet := false, leader := true, label := 0,
      probe := false, phase := true }

/-- State after edge `1 -> 2`: the farthest leader fires a bullet to site 1. -/
def ExpectedC1 (i : Fin 3) : State 2 :=
  if i = head then
    { bullet := false, leader := true, label := 0,
      probe := false, phase := false }
  else if i = mid then
    { bullet := true, leader := false, label := 1,
      probe := false, phase := false }
  else
    { bullet := false, leader := true, label := 0,
      probe := false, phase := true }

/-- State after edges `[1,0]`: the bullet has moved to the barrier head. -/
def ExpectedC2 (i : Fin 3) : State 2 :=
  if i = head then
    { bullet := true, leader := true, label := 0,
      probe := false, phase := false }
  else if i = mid then
    { bullet := false, leader := false, label := 1,
      probe := false, phase := false }
  else
    { bullet := false, leader := true, label := 0,
      probe := false, phase := true }

/-- Final state after `[1,0,2]`: the barrier absorbs the bullet and advances,
giving labels `[1,1,0]`, while both leaders survive. -/
def ExpectedD (i : Fin 3) : State 2 :=
  if i = head then
    { bullet := false, leader := true, label := 1,
      probe := false, phase := false }
  else if i = mid then
    { bullet := false, leader := false, label := 1,
      probe := false, phase := false }
  else
    { bullet := false, leader := true, label := 0,
      probe := false, phase := true }

def shotPrefix : List (Fin 3) := [mid, head]
def shotWord : List (Fin 3) := [mid, head, tail]

def C1 : Fin 3 → State 2 :=
  (protocol 2 hk2).step ring3 C mid

def C2 : Fin 3 → State 2 :=
  rawRun hk2 ring3 C shotPrefix

def D : Fin 3 → State 2 :=
  rawRun hk2 ring3 C shotWord

/-- Maximum cut coordinate formalizes "farthest from the barrier" in the
paper's counterclockwise bullet direction. -/
def FarthestLeader {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k) (barrier selected : Fin n) : Prop :=
  (X selected).leader = true ∧
    ∀ i : Fin n, (X i).leader = true →
      (cutCoord ring barrier i).val ≤
        (cutCoord ring barrier selected).val

def UniqueLeader {n k : Nat} (X : Fin n → State k) : Prop :=
  ∃ ell : Fin n, (X ell).leader = true ∧
    ∀ i : Fin n, (X i).leader = true → i = ell

def NoBullets {n k : Nat} (X : Fin n → State k) : Prop :=
  ∀ i : Fin n, (X i).bullet = false

def NoProbes {n k : Nat} (X : Fin n → State k) : Prop :=
  ∀ i : Fin n, (X i).probe = false

/-- The complete literal four-state trace, including the moving unique
barrier and every local field through the final absorption. -/
theorem exact_full_trace :
    C1 = ExpectedC1 ∧
      C2 = ExpectedC2 ∧
      D = ExpectedD ∧
      OneBarrierAt hk2 ring3 C tail ∧
      OneBarrierAt hk2 ring3 C1 tail ∧
      OneBarrierAt hk2 ring3 C2 tail ∧
      OneBarrierAt hk2 ring3 D head := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert

/-- The initial state satisfies the paper's one-barrier leader phase with a
forced farthest leader: it has two leaders and no bullets or probes. -/
theorem paper_leader_phase_premise :
    OneBarrierAt hk2 ring3 C tail ∧
      NoBullets C ∧
      NoProbes C ∧
      leaderCount C = 2 ∧
      FarthestLeader ring3 C tail tail ∧
      (∀ i : Fin 3, FarthestLeader ring3 C tail i → i = tail) := by
  refine ⟨?_, ?_, ?_, by decide, ?_, ?_⟩
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert
  · constructor
    · decide
    · intro i hi
      rcases i with ⟨i, hi'⟩
      have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases h with rfl | rfl | rfl <;> decide +revert
  · intro i hi
    rcases i with ⟨i, hi'⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change FarthestLeader ring3 C tail head at hi
      exact False.elim ((by decide :
        ¬ (cutCoord ring3 tail tail).val ≤
          (cutCoord ring3 tail head).val) (hi.2 tail (by decide)))
    · change FarthestLeader ring3 C tail mid at hi
      exact False.elim ((by decide : (C mid).leader ≠ true) hi.1)
    · apply Fin.ext
      rfl

/-- The first two services are nonbarrier services in their actual current
states; the last letter is the unique barrier and absorbs the head bullet. -/
theorem prescribed_word_is_literal_fire_move_absorb :
    shotWord = [1, 0, 2] ∧
      CurrentNonbarrierWord hk2 ring3 C shotPrefix ∧
      (C1 mid).bullet = true ∧
      (C2 head).bullet = true ∧
      (D head).bullet = false ∧
      NoBullets D := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_⟩
  · unfold shotPrefix CurrentNonbarrierWord
    refine ⟨by decide, ?_, trivial⟩
    change ¬ IsBarrier hk2 (C1 head) (C1 (ring3.rightNeighbor head))
    rw [exact_full_trace.1]
    decide
  intro i
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide +revert

/-- Closed refutation of the printed one-shot implication: after the selected
farthest leader's bullet is absorbed, two distinct leaders still remain. -/
theorem one_shot_farthest_leader_counterexample :
    (D head).leader = true ∧
      (D tail).leader = true ∧
      head ≠ tail ∧
      leaderCount D = 2 ∧
      ¬ UniqueLeader D ∧
      ¬ (leaderCount D ≤ 1) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide⟩
  intro hu
  rcases hu with ⟨ell, hell, honly⟩
  rcases ell with ⟨ell, hellLt⟩
  have heq : ell = 0 ∨ ell = 1 ∨ ell = 2 := by omega
  rcases heq with rfl | rfl | rfl
  · exact (by decide : tail ≠ head) (honly tail (by decide))
  · exact (by decide : (D mid).leader ≠ true) hell
  · exact (by decide : head ≠ tail) (honly head (by decide))

/-- In particular the prescribed one-shot word neither lowers the leader
count nor reaches a unique-leader state. -/
theorem one_shot_neither_drops_nor_unique :
    leaderCount D = leaderCount C ∧
      ¬ (leaderCount D < leaderCount C ∨ UniqueLeader D) := by
  constructor
  · decide
  · rintro (hlt | hu)
    · exact (by decide : ¬ leaderCount D < leaderCount C) hlt
    · exact one_shot_farthest_leader_counterexample.2.2.2.2.1 hu

#print axioms exact_full_trace
#print axioms paper_leader_phase_premise
#print axioms prescribed_word_is_literal_fire_move_absorb
#print axioms one_shot_farthest_leader_counterexample
#print axioms one_shot_neither_drops_nor_unique

end AAFJPK.JournalLemma92LeaderEliminationCounterexample
