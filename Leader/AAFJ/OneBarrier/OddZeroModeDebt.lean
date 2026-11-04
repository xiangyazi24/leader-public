import Leader.AAFJ.OneBarrier.OddZeroPhiFamily
import Leader.AAFJ.OneBarrier.ZeroLeaderToUnique

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OddZeroModeDebt

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.ZeroLeaderToUnique
open AAFJPK.OddZeroPhiFamily
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalUniqueLeaderCleanup

/-!
The odd alternating family is a literal one-barrier, zero-leader plateau.  A
one-bit debt is enough to record the finite mode that matters at this first
composition edge: `1` means that the selected one-barrier state is still in
the zero-leader mode, and `0` means that a leader has already been created.
The debt deliberately does not pretend to be a global rank; this file only
connects the accepted zero-to-unique producer to this concrete family.
-/

def zeroModeDebt {n k : Nat} (C : Fin n → State k) : Nat :=
  if leaderCount C = 0 then 1 else 0

private theorem one_leaderCount_of_true
    {n k : Nat} (C : Fin n → State k) (i : Fin n)
    (hi : (C i).leader = true) : 1 ≤ leaderCount C := by
  let after : Fin n → Bool := fun j => if j = i then false else (C j).leader
  have hdrop := bitCount_single_drop
    (fun j : Fin n => (C j).leader) after i hi
    (by simp [after])
    (by
      intro j hji
      simp [after, hji])
  unfold leaderCount
  have hnonneg : 0 ≤ bitCount after := Nat.zero_le _
  omega

private theorem zeroModeDebt_eq_one_of_all_false
    {n k : Nat} (C : Fin n → State k)
    (hzero : ∀ i, (C i).leader = false) :
    zeroModeDebt C = 1 := by
  have hc : leaderCount C = 0 := leaderCount_eq_zero_of_all_false C hzero
  simp [zeroModeDebt, hc]

private theorem zeroModeDebt_eq_zero_of_leader
    {n k : Nat} (C : Fin n → State k) (i : Fin n)
    (hi : (C i).leader = true) : zeroModeDebt C = 0 := by
  have hpos : 0 < leaderCount C := one_leaderCount_of_true C i hi
  simp [zeroModeDebt, Nat.ne_of_gt hpos]

/-! The odd source is cold in every control coordinate.  This is the source
fact that lets the accepted zero-birth producer, rather than an abstract
transition relation, be selected on this plateau. -/
theorem oddZero_cold_controls
    {m : Nat} (hm : 1 ≤ m) :
    (∀ i, (oddZero m i).leader = false) ∧
      (∀ i, (oddZero m i).bullet = false) ∧
      (∀ i, (oddZero m i).probe = false) ∧
      (∀ i, (oddZero m i).phase = false) := by
  refine ⟨oddZero_all_leaders_false m, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl
  · intro i
    rfl

theorem oddZero_source_mode_debt
    {m : Nat} (hm : 1 ≤ m) :
    zeroModeDebt (oddZero m) = 1 := by
  exact zeroModeDebt_eq_one_of_all_false
    (oddZero m) (oddZero_all_leaders_false m)

/-! This is the actual selected macro edge.  The word is supplied by the
accepted `zeroLeader_oneBarrierAt_unique_word` producer, whose proof chooses
the literal `ZeroLeaderBirth` chase word.  The endpoint keeps the transported
one-barrier witness and `PhiAt = 1`, and its unique leader pays the one-bit
zero-mode debt. -/
theorem oddZero_selected_birth_decreases
    {m : Nat} (hm : 1 ≤ m) :
    ∃ w b' ell,
      w.length ≤ (2 * m + 1) + 2 ∧
      OneBarrierAt hk2 (oddRing m) (rawRun hk2 (oddRing m) (oddZero m) w) b' ∧
      PhiAt (oddRing m) b' (rawRun hk2 (oddRing m) (oddZero m) w) = 1 ∧
      UniqueLeaderAt (rawRun hk2 (oddRing m) (oddZero m) w) ell ∧
      zeroModeDebt (rawRun hk2 (oddRing m) (oddZero m) w) <
        zeroModeDebt (oddZero m) := by
  have hn3 : 3 ≤ 2 * m + 1 := by omega
  have hndvd : ¬ 2 ∣ 2 * m + 1 := by
    intro h
    rcases h with ⟨q, hq⟩
    omega
  obtain ⟨w, b', ell, hw, hB, hphi, hunique⟩ :=
    zeroLeader_oneBarrierAt_unique_word
      hk2 (oddRing m) hn3 hndvd (oddZero m) (oddTail m)
      (oddZero_one_barrier hm) (oddZero_all_leaders_false m)
  refine ⟨w, b', ell, ?_, hB, hphi, hunique, ?_⟩
  · omega
  · have hdebt : zeroModeDebt
        (rawRun hk2 (oddRing m) (oddZero m) w) = 0 :=
      zeroModeDebt_eq_zero_of_leader
        (rawRun hk2 (oddRing m) (oddZero m) w) ell hunique.1
    rw [hdebt, oddZero_source_mode_debt hm]
    omega

/-! For the smallest odd ring the producer's branch is fully visible: the
selected word is `[2,0,1,2]`, namely arm the cold barrier, carry its probe
through the two non-barrier edges, and hit the barrier to create a leader. -/

def oddZero3 : Fin 3 → State 2 := oddZero 1

def oddZero3BirthWord : List (Fin 3) := [2, 0, 1, 2]

theorem oddZero3_selected_word_decreases :
    OneBarrierAt hk2 (oddRing 1) oddZero3 (oddTail 1) ∧
      oddZero3BirthWord.length ≤ 3 + 2 ∧
      OneBarrierAt hk2 (oddRing 1)
        (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord) 0 ∧
      PhiAt (oddRing 1) 0
        (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord) = 1 ∧
      (∃ ell, UniqueLeaderAt
        (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord) ell) ∧
      zeroModeDebt
          (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord) <
      zeroModeDebt oddZero3 := by
  decide +kernel

theorem oddZero3_selected_word_changes_cold_tail_history :
    (oddZero3 2).phase = false ∧
      (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord 2).phase = true ∧
      (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord 2).probe = false ∧
      (rawRun hk2 (oddRing 1) oddZero3 oddZero3BirthWord 2).leader = true := by
  decide +kernel

#print axioms oddZero_cold_controls
#print axioms oddZero_source_mode_debt
#print axioms oddZero_selected_birth_decreases
#print axioms oddZero3_selected_word_decreases
#print axioms oddZero3_selected_word_changes_cold_tail_history

end AAFJPK.OddZeroModeDebt
