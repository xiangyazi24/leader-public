import Leader.AAFJ.OneBarrier.DirtyTailBellman

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OddZeroPhiFamily

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.SingleBarrierSanitation.DirtyTailBellman

def hk2 : 0 < (2 : Nat) := by decide +kernel

def oddRing (m : Nat) : DirectedRing (2 * m + 1) :=
  ⟨by omega⟩

def oddTail (m : Nat) : Fin (2 * m + 1) :=
  ⟨2 * m, by omega⟩

def oddLabel {m : Nat} (i : Fin (2 * m + 1)) : Fin 2 :=
  ⟨i.val % 2, by omega⟩

def oddZero (m : Nat) (i : Fin (2 * m + 1)) : State 2 :=
  { bullet := false
    leader := false
    label := oddLabel i
    probe := false
    phase := false }

private theorem mod_two_succ_ne (x : Nat) :
    x % 2 ≠ (x + 1) % 2 := by
  omega

private theorem odd_non_tail_label_ne
    {m : Nat} (hm : 1 ≤ m) (e : Fin (2 * m + 1))
    (he : e ≠ oddTail m) :
    (oddZero m e).label ≠
      (oddZero m ((oddRing m).rightNeighbor e)).label := by
  have hval : e.val < 2 * m := by
    have hlt := e.isLt
    have hne : e.val ≠ 2 * m := by
      intro h
      apply he
      apply Fin.ext
      exact h
    omega
  have hright : ((oddRing m).rightNeighbor e).val = e.val + 1 := by
    unfold oddRing DirectedRing.rightNeighbor
    dsimp only
    rw [Nat.mod_eq_of_lt]
    omega
  intro hlabel
  have hvalLabel := congrArg Fin.val hlabel
  simp [oddZero, oddLabel, hright] at hvalLabel
  exact mod_two_succ_ne e.val hvalLabel

theorem oddZero_one_barrier
    {m : Nat} (hm : 1 ≤ m) :
    OneBarrierAt hk2 (oddRing m) (oddZero m) (oddTail m) := by
  intro e
  rw [barrierAt_labelsOf_iff hk2 (oddRing m) (oddZero m) e]
  rw [isBarrier_two_iff_label_eq]
  by_cases he : e = oddTail m
  · subst e
    simp [oddZero, oddTail, oddRing, oddLabel,
      DirectedRing.rightNeighbor]
  · constructor
    · intro hEq
      exact False.elim ((odd_non_tail_label_ne hm e he) hEq)
    · intro hEq
      exact (he hEq).elim

theorem oddZero_all_leaders_false
    (m : Nat) : ∀ i, (oddZero m i).leader = false := by
  intro i
  rfl

theorem oddZero_phi_one
    {m : Nat} (hm : 1 ≤ m) :
    PhiAt (oddRing m) (oddTail m) (oddZero m) = 1 := by
  unfold PhiAt
  apply phi_eq_one_of_no_leaders
  intro i
  exact oddZero_all_leaders_false m _

theorem oddZero_dirty_zero
    {m : Nat} (hm : 1 ≤ m) :
    dirtyCtl (oddZero m) (oddTail m) = 0 := by
  rfl

private theorem oddZero_step_fields
    {m : Nat} (hm : 1 ≤ m) (e : Fin (2 * m + 1)) :
    let D := (protocol 2 hk2).step (oddRing m) (oddZero m) e
    (∀ i, (D i).leader = false) ∧
      (D (oddTail m)).bullet = false := by
  dsimp
  have hpair :
      (transition hk2 (oddZero m e)
        (oddZero m ((oddRing m).rightNeighbor e))).1.leader = false ∧
      (transition hk2 (oddZero m e)
        (oddZero m ((oddRing m).rightNeighbor e))).2.leader = false ∧
      (transition hk2 (oddZero m e)
        (oddZero m ((oddRing m).rightNeighbor e))).1.bullet = false ∧
      (transition hk2 (oddZero m e)
        (oddZero m ((oddRing m).rightNeighbor e))).2.bullet = false := by
    unfold transition
    split <;> simp [barrierStep, nonBarrierStep, probeHitsBarrier, oddZero]
  constructor
  · intro i
    unfold PopulationProtocol.step protocol
    dsimp only
    by_cases h1 : i = e
    · subst i
      simp [hpair]
    · by_cases h2 : i = (oddRing m).rightNeighbor e
      · subst i
        simp [h1, hpair]
      · simp [h1, h2, oddZero]
  · unfold PopulationProtocol.step protocol
    dsimp only
    by_cases h1 : oddTail m = e
    · subst e
      simp [hpair]
    · by_cases h2 : oddTail m = (oddRing m).rightNeighbor e
      · have hne : (oddRing m).rightNeighbor e ≠ e := by
          exact rightNeighbor_ne_self (oddRing m) (by omega) e
        simp [hne, h2, hpair]
      · simp [h1, h2, oddZero]

private theorem oddZero_not_ready
    {m : Nat} (hm : 1 ≤ m) (e : Fin (2 * m + 1)) :
    ¬ AdvanceReady hk2 (oddRing m) (oddZero m) e := by
  intro hready
  change PairAdvanceReady hk2 (oddZero m e)
      (oddZero m ((oddRing m).rightNeighbor e)) at hready
  have hphase : (oddZero m e).phase = true := hready.2.1
  simp [oddZero] at hphase

theorem oddZero_all_raw_children_plateau
    {m : Nat} (hm : 1 ≤ m) :
    ∀ e : Fin (2 * m + 1),
      let D := (protocol 2 hk2).step (oddRing m) (oddZero m) e
      let b' := postTail hk2 (oddRing m) (oddZero m) (oddTail m) e
      PhiAt (oddRing m) b' D = 1 ∧ dirtyCtl D b' = 0 := by
  intro e
  have hnot := oddZero_not_ready hm e
  have hpost :
      postTail hk2 (oddRing m) (oddZero m) (oddTail m) e = oddTail m := by
    simp [postTail, hnot]
  rw [hpost]
  have hfields := oddZero_step_fields hm e
  dsimp only at hfields
  constructor
  · unfold PhiAt
    apply phi_eq_one_of_no_leaders
    intro i
    exact hfields.1 _
  · exact by simpa [dirtyCtl] using hfields.2

theorem oddZero_all_raw_children_one_barrier
    {m : Nat} (hm : 1 ≤ m) :
    ∀ e : Fin (2 * m + 1),
      let D := (protocol 2 hk2).step (oddRing m) (oddZero m) e
      let b' := postTail hk2 (oddRing m) (oddZero m) (oddTail m) e
      OneBarrierAt hk2 (oddRing m) D b' := by
  have hn3 : 3 ≤ 2 * m + 1 := by omega
  have hndvd : ¬ 2 ∣ 2 * m + 1 := by
    intro h
    rcases h with ⟨q, hq⟩
    omega
  intro e
  exact (dirtyTail_child_frame hk2 (oddRing m) hn3 hndvd
    (oddZero m) (oddTail m) e (oddZero_one_barrier hm)
    (oddZero_phi_one hm)).1

private theorem ofFn_sum_const {n c : Nat} :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

theorem oddZero_phi_child_sum_row_fails
    {m : Nat} (hm : 1 ≤ m) :
    (List.ofFn (fun e : Fin (2 * m + 1) =>
      PhiAt (oddRing m)
        (postTail hk2 (oddRing m) (oddZero m) (oddTail m) e)
        ((protocol 2 hk2).step (oddRing m) (oddZero m) e))).sum + 1 >
      (2 * m + 1) * PhiAt (oddRing m) (oddTail m) (oddZero m) := by
  have hall := oddZero_all_raw_children_plateau hm
  have hfun :
      (fun e : Fin (2 * m + 1) =>
        PhiAt (oddRing m)
          (postTail hk2 (oddRing m) (oddZero m) (oddTail m) e)
          ((protocol 2 hk2).step (oddRing m) (oddZero m) e)) =
        (fun _ : Fin (2 * m + 1) => 1) := by
    funext e
    exact (hall e).1
  rw [hfun, ofFn_sum_const, oddZero_phi_one hm]
  omega

theorem oddZero_dirty_child_sum_row_fails
    {m : Nat} (hm : 1 ≤ m) :
    (List.ofFn (fun e : Fin (2 * m + 1) =>
      dirtyChild hk2 (oddRing m) (oddZero m) (oddTail m) e)).sum + 1 >
      (2 * m + 1) * dirtyCtl (oddZero m) (oddTail m) := by
  have hall := oddZero_all_raw_children_plateau hm
  have hfun :
      (fun e : Fin (2 * m + 1) =>
        dirtyChild hk2 (oddRing m) (oddZero m) (oddTail m) e) =
        (fun _ : Fin (2 * m + 1) => 0) := by
    funext e
    have he := hall e
    dsimp only at he
    have hnot := oddZero_not_ready hm e
    have hpost :
        postTail hk2 (oddRing m) (oddZero m) (oddTail m) e = oddTail m := by
      simp [postTail, hnot]
    simpa [dirtyChild, hpost] using he.2
  rw [hfun, ofFn_sum_const, oddZero_dirty_zero hm]
  omega

theorem oddZero_nonnegative_linear_child_sum_row_fails
    {m : Nat} (hm : 1 ≤ m) (a d : Nat) :
    (List.ofFn (fun e : Fin (2 * m + 1) =>
      a * PhiAt (oddRing m)
        (postTail hk2 (oddRing m) (oddZero m) (oddTail m) e)
        ((protocol 2 hk2).step (oddRing m) (oddZero m) e) +
      d * dirtyChild hk2 (oddRing m) (oddZero m) (oddTail m) e)).sum + 1 >
      (2 * m + 1) *
        (a * PhiAt (oddRing m) (oddTail m) (oddZero m) +
          d * dirtyCtl (oddZero m) (oddTail m)) := by
  have hall := oddZero_all_raw_children_plateau hm
  have hfun :
      (fun e : Fin (2 * m + 1) =>
        a * PhiAt (oddRing m)
          (postTail hk2 (oddRing m) (oddZero m) (oddTail m) e)
          ((protocol 2 hk2).step (oddRing m) (oddZero m) e) +
        d * dirtyChild hk2 (oddRing m) (oddZero m) (oddTail m) e) =
        (fun _ : Fin (2 * m + 1) => a) := by
    funext e
    have hphi := (hall e).1
    have hdirty := (hall e).2
    have hnot := oddZero_not_ready hm e
    have hpost :
        postTail hk2 (oddRing m) (oddZero m) (oddTail m) e = oddTail m := by
      simp [postTail, hnot]
    rw [hpost] at hphi hdirty
    simp only [dirtyChild]
    rw [hpost, hphi, hdirty]
    simp
  rw [hfun, ofFn_sum_const, oddZero_phi_one hm, oddZero_dirty_zero hm]
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
  omega

theorem oddZero_source_plateau_certificate
    {m : Nat} (hm : 1 ≤ m) :
    OneBarrierAt hk2 (oddRing m) (oddZero m) (oddTail m) ∧
      PhiAt (oddRing m) (oddTail m) (oddZero m) = 1 ∧
      dirtyCtl (oddZero m) (oddTail m) = 0 ∧
      (∀ e : Fin (2 * m + 1),
        let D := (protocol 2 hk2).step (oddRing m) (oddZero m) e
        let b' := postTail hk2 (oddRing m) (oddZero m) (oddTail m) e
        PhiAt (oddRing m) b' D = 1 ∧ dirtyCtl D b' = 0) ∧
      (List.ofFn (fun e : Fin (2 * m + 1) =>
        PhiAt (oddRing m)
          (postTail hk2 (oddRing m) (oddZero m) (oddTail m) e)
          ((protocol 2 hk2).step (oddRing m) (oddZero m) e))).sum + 1 >
        (2 * m + 1) * PhiAt (oddRing m) (oddTail m) (oddZero m) ∧
      (List.ofFn (fun e : Fin (2 * m + 1) =>
        dirtyChild hk2 (oddRing m) (oddZero m) (oddTail m) e)).sum + 1 >
        (2 * m + 1) * dirtyCtl (oddZero m) (oddTail m) := by
  refine ⟨oddZero_one_barrier hm, oddZero_phi_one hm,
    oddZero_dirty_zero hm, oddZero_all_raw_children_plateau hm,
    oddZero_phi_child_sum_row_fails hm,
    oddZero_dirty_child_sum_row_fails hm⟩

#print axioms oddZero_all_raw_children_plateau
#print axioms oddZero_all_raw_children_one_barrier

#print axioms oddZero_phi_child_sum_row_fails
#print axioms oddZero_dirty_child_sum_row_fails
#print axioms oddZero_source_plateau_certificate

#print axioms oddZero_one_barrier
#print axioms oddZero_phi_one
#print axioms oddZero_dirty_zero

end AAFJPK.OddZeroPhiFamily
