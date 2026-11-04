import Leader.Wu.Seal.BirthBarrierShortBlocks

/-!
# Polynomial iid mass for entering the committed birth domain

The deterministic producer in R93 fixes one particular clockwise commitment
word.  Counting only that word gives exponentially small scheduler mass.  The
actual birth-barrier transition has a stronger monotonicity property: every
uncommitted site is committed whenever its incoming edge is selected, and a
committed site never becomes uncommitted again.

This module records the resulting exact finite-tree contraction.  If `U(C)` is
the number of `true` barrier bits, then, over all `n` possible next edges,

`sum_e U(step C e) <= (n - 1) * U(C)`.

Consequently the number of length-`t` scheduler words whose endpoint is not
fully committed is at most `n * (n - 1)^t`.  At `t = n^2`, elementary finite
arithmetic gives success mass at least `2/(n+2)`.  No single favorable word is
selected and no probabilistic axiom is used.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidBirthEntryMassSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLClosedDomainSchedulerAmplificationSol
open PPartialSealSweepOverlaySol PPartialSealSweepIidComplexitySol
open PPartialSealSweepIidBirthRepairSol
open PPartialSealSweepIidBirthComplexitySol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Finite-sum infrastructure -/

private theorem sum_ofFn_eq
    (f g : Fin n → Nat) (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_le
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_add (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem sum_ofFn_mul_left (a : Nat) (f : Fin n → Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]

private theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem sum_ofFn_balance_one
    (f g : Fin n → Nat) (j : Fin n)
    (hother : ∀ i, i ≠ j → f i = g i) :
    (List.ofFn f).sum + g j = (List.ofFn g).sum + f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply sum_ofFn_eq
          intro i
          apply hother i.succ
          intro hbad
          have hv := congrArg Fin.val hbad
          simp at hv
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 := hother 0 (Ne.symm hj0)
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ) j'
          (by
            intro i hij
            apply hother i.succ
            intro hbad
            apply hij
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        rw [hjsucc] at htail
        omega

private theorem sum_ofFn_balance_two
    (f g : Fin n → Nat) (a b : Fin n) (hab : a ≠ b)
    (hother : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  let mid : Fin n → Nat := fun i => if i = a then f i else g i
  have hga : (List.ofFn mid).sum + g a =
      (List.ofFn g).sum + mid a := by
    apply sum_ofFn_balance_one mid g a
    intro i hia
    simp [mid, hia]
  have hfb : (List.ofFn f).sum + mid b =
      (List.ofFn mid).sum + f b := by
    apply sum_ofFn_balance_one f mid b
    intro i hib
    by_cases hia : i = a
    · subst i
      simp [mid]
    · simp [mid, hia, hother i hia hib]
  have hma : mid a = f a := by simp [mid]
  have hmb : mid b = g b := by simp [mid, Ne.symm hab]
  rw [hma] at hga
  rw [hmb] at hfb
  omega

private theorem sum_ofFn_rightNeighbor
    (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.rightNeighbor e))).sum =
      (List.ofFn f).sum := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun e : Fin (m + 1) => f (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin m =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last m))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last m) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin m,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin m => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin m => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

/-! ## Monotone commitment mass -/

def iidBirthUncommittedIndicator
    (u : IidBirthState psi kappa tau) : Nat :=
  if u.2 then 1 else 0

def iidBirthUncommittedCount
    (C : IidBirthConfig n psi kappa tau) : Nat :=
  (List.ofFn (fun i => iidBirthUncommittedIndicator (C i))).sum

theorem iidBirthUncommittedCount_le
    (C : IidBirthConfig n psi kappa tau) :
    iidBirthUncommittedCount C ≤ n := by
  unfold iidBirthUncommittedCount
  calc
    (List.ofFn (fun i => iidBirthUncommittedIndicator (C i))).sum ≤
        (List.ofFn (fun _ : Fin n => 1)).sum := by
      apply sum_ofFn_le
      intro i
      cases h : (C i).2 <;>
        simp [iidBirthUncommittedIndicator, h]
    _ = n := by simpa using sum_ofFn_const n 1

private theorem iidBirth_indicator_localStep_other
    (ring : DirectedRing n) (C : IidBirthConfig n psi kappa tau)
    (e i : Fin n) (hie : i ≠ e)
    (hij : i ≠ ring.rightNeighbor e) :
    iidBirthUncommittedIndicator
        (localStep ring P_partialSealIidBirth C e i) =
      iidBirthUncommittedIndicator (C i) := by
  simp [localStep, hie, hij]

private theorem iidBirth_indicator_endpoints
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) (e : Fin n) :
    let j := ring.rightNeighbor e
    let D := localStep ring P_partialSealIidBirth C e
    iidBirthUncommittedIndicator (D e) +
        iidBirthUncommittedIndicator (D j) ≤
      iidBirthUncommittedIndicator (C e) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let D := localStep ring P_partialSealIidBirth C e
  cases he : (C e).2 with
  | false =>
      cases hj : (C j).2 with
      | false =>
          have hpair := P_partialSealIidBirth_committed
            (C e) (C j) he hj
          simp [D, localStep, j, hje, hpair,
            iidBirthUncommittedIndicator]
      | true =>
          have hpair := P_partialSealIidBirth_propagate
            (C e) (C j) he hj
          simp [D, localStep, j, hje, hpair, he,
            iidBirthUncommittedIndicator]
  | true =>
      cases hj : (C j).2 with
      | false =>
          have hpair := P_partialSealIidBirth_reverse_inert
            (C e) (C j) he hj
          simp [D, localStep, j, hje, hpair, he, hj,
            iidBirthUncommittedIndicator]
      | true =>
          have hce := hclean e he
          have hcj := hclean j hj
          have hpair := P_partialSealIidBirth_birth
            (C e) (C j) he hj hce.1 hce.2 hcj.1 hcj.2
          simp [D, localStep, j, hje, hpair, he,
            iidBirthUncommittedIndicator]

/-- Selecting an incoming edge removes its responder's uncommitted mass; no
other outer bit can increase. -/
theorem iidBirthUncommittedCount_localStep_balance
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) (e : Fin n) :
    iidBirthUncommittedCount
        (localStep ring P_partialSealIidBirth C e) +
      iidBirthUncommittedIndicator (C (ring.rightNeighbor e)) ≤
        iidBirthUncommittedCount C := by
  let j := ring.rightNeighbor e
  have hje : e ≠ j :=
    (rightNeighbor_ne_self_of_one_lt ring hn e).symm
  let D := localStep ring P_partialSealIidBirth C e
  have hsum := sum_ofFn_balance_two
    (fun i => iidBirthUncommittedIndicator (D i))
    (fun i => iidBirthUncommittedIndicator (C i)) e j hje
    (by
      intro i hie hij
      exact iidBirth_indicator_localStep_other ring C e i hie
        (by simpa [j] using hij))
  have hend := iidBirth_indicator_endpoints ring hn C hclean e
  change iidBirthUncommittedIndicator (D e) +
      iidBirthUncommittedIndicator (D j) ≤
        iidBirthUncommittedIndicator (C e) at hend
  change iidBirthUncommittedCount D +
      iidBirthUncommittedIndicator (C e) +
      iidBirthUncommittedIndicator (C j) =
    iidBirthUncommittedCount C +
      iidBirthUncommittedIndicator (D e) +
      iidBirthUncommittedIndicator (D j) at hsum
  change iidBirthUncommittedCount D +
      iidBirthUncommittedIndicator (C j) ≤
        iidBirthUncommittedCount C
  omega

/-- Exact scheduler-average contraction of the uncommitted population. -/
theorem iidBirthUncommittedCount_step_sum
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) :
    (List.ofFn (fun e => iidBirthUncommittedCount
      (localStep ring P_partialSealIidBirth C e))).sum ≤
      (n - 1) * iidBirthUncommittedCount C := by
  have hsum := sum_ofFn_le
    (fun e => iidBirthUncommittedCount
        (localStep ring P_partialSealIidBirth C e) +
      iidBirthUncommittedIndicator (C (ring.rightNeighbor e)))
    (fun _ : Fin n => iidBirthUncommittedCount C)
    (fun e => iidBirthUncommittedCount_localStep_balance
      ring hn C hclean e)
  rw [sum_ofFn_add, sum_ofFn_const,
    sum_ofFn_rightNeighbor ring
      (fun i => iidBirthUncommittedIndicator (C i))] at hsum
  change (List.ofFn (fun e => iidBirthUncommittedCount
      (localStep ring P_partialSealIidBirth C e))).sum +
      iidBirthUncommittedCount C ≤
    n * iidBirthUncommittedCount C at hsum
  have hmul : n * iidBirthUncommittedCount C =
      (n - 1) * iidBirthUncommittedCount C +
        iidBirthUncommittedCount C := by
    calc
      n * iidBirthUncommittedCount C =
          ((n - 1) + 1) * iidBirthUncommittedCount C := by
            congr 1
            omega
      _ = (n - 1) * iidBirthUncommittedCount C +
          iidBirthUncommittedCount C := by
            rw [Nat.add_mul, Nat.one_mul]
  rw [hmul] at hsum
  omega

/-! ## Exact scheduler trees -/

/-- Sum of the uncommitted count over all exact length-`t` scheduler words. -/
def iidBirthUncommittedTreeTotal
    (ring : DirectedRing n) :
    IidBirthConfig n psi kappa tau → Nat → Nat
  | C, 0 => iidBirthUncommittedCount C
  | C, t + 1 =>
      (List.ofFn (fun e => iidBirthUncommittedTreeTotal ring
        (localStep ring P_partialSealIidBirth C e) t)).sum

/-- Number of exact length-`t` scheduler words whose endpoint is not wholly
committed. -/
noncomputable def iidBirthCommitmentFinalMissTree
    (ring : DirectedRing n) :
    IidBirthConfig n psi kappa tau → Nat → Nat
  | C, 0 => @ite Nat (IidBirthAllCommitted C)
      (Classical.propDecidable _) 0 1
  | C, t + 1 =>
      (List.ofFn (fun e => iidBirthCommitmentFinalMissTree ring
        (localStep ring P_partialSealIidBirth C e) t)).sum

/-- Complementary exact endpoint-success tree. -/
noncomputable def iidBirthCommitmentFinalHitTree
    (ring : DirectedRing n) :
    IidBirthConfig n psi kappa tau → Nat → Nat
  | C, 0 => @ite Nat (IidBirthAllCommitted C)
      (Classical.propDecidable _) 1 0
  | C, t + 1 =>
      (List.ofFn (fun e => iidBirthCommitmentFinalHitTree ring
        (localStep ring P_partialSealIidBirth C e) t)).sum

theorem iidBirthUncommittedTreeTotal_le
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) (t : Nat) :
    iidBirthUncommittedTreeTotal ring C t ≤
      (n - 1) ^ t * iidBirthUncommittedCount C := by
  induction t generalizing C with
  | zero => simp [iidBirthUncommittedTreeTotal]
  | succ t ih =>
      rw [iidBirthUncommittedTreeTotal]
      have hchildren := sum_ofFn_le
        (fun e => iidBirthUncommittedTreeTotal ring
          (localStep ring P_partialSealIidBirth C e) t)
        (fun e => (n - 1) ^ t * iidBirthUncommittedCount
          (localStep ring P_partialSealIidBirth C e))
        (fun e => ih (localStep ring P_partialSealIidBirth C e)
          (iidBirthArmedClean_localStep ring C hclean e))
      rw [sum_ofFn_mul_left] at hchildren
      have hstep := iidBirthUncommittedCount_step_sum
        ring hn C hclean
      have hscaled := Nat.mul_le_mul_left ((n - 1) ^ t) hstep
      calc
        (List.ofFn (fun e => iidBirthUncommittedTreeTotal ring
            (localStep ring P_partialSealIidBirth C e) t)).sum ≤
            (n - 1) ^ t *
              (List.ofFn (fun e => iidBirthUncommittedCount
                (localStep ring P_partialSealIidBirth C e))).sum := hchildren
        _ ≤ (n - 1) ^ t * ((n - 1) *
              iidBirthUncommittedCount C) := hscaled
        _ = (n - 1) ^ (t + 1) *
              iidBirthUncommittedCount C := by
          rw [Nat.pow_succ]
          grind

private theorem term_le_sum_ofFn (f : Fin n → Nat) (j : Fin n) :
    f j ≤ (List.ofFn f).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have ht := ih (fun i : Fin n => f i.succ) j'
        rw [hjsucc] at ht
        omega

private theorem iidBirthCommitmentFinalMissTree_zero_le_count
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau) :
    iidBirthCommitmentFinalMissTree ring C 0 ≤
      iidBirthUncommittedCount C := by
  simp only [iidBirthCommitmentFinalMissTree]
  by_cases hall : IidBirthAllCommitted C
  · rw [if_pos hall]
    exact Nat.zero_le _
  · rw [if_neg hall]
    have hex : ∃ i : Fin n, (C i).2 ≠ false := by
      apply Classical.not_forall.mp
      exact hall
    obtain ⟨i, hi⟩ := hex
    have htrue : (C i).2 = true := by
      cases h : (C i).2
      · contradiction
      · rfl
    have ht := term_le_sum_ofFn
      (fun i => iidBirthUncommittedIndicator (C i)) i
    change 1 ≤ iidBirthUncommittedCount C
    simpa [iidBirthUncommittedIndicator, htrue,
      iidBirthUncommittedCount] using ht

/-- Every final-miss leaf contributes at least one unit of uncommitted mass. -/
theorem iidBirthCommitmentFinalMissTree_le_weight
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) (t : Nat) :
    iidBirthCommitmentFinalMissTree ring C t ≤
      iidBirthUncommittedTreeTotal ring C t := by
  induction t generalizing C with
  | zero => exact iidBirthCommitmentFinalMissTree_zero_le_count ring C
  | succ t ih =>
      simp only [iidBirthCommitmentFinalMissTree,
        iidBirthUncommittedTreeTotal]
      apply sum_ofFn_le
      intro e
      exact ih (localStep ring P_partialSealIidBirth C e)
        (iidBirthArmedClean_localStep ring C hclean e)

/-- Exact endpoint-failure numerator at every horizon. -/
theorem iidBirthCommitmentFinalMissTree_le
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) (t : Nat) :
    iidBirthCommitmentFinalMissTree ring C t ≤
      n * (n - 1) ^ t := by
  have hmiss := iidBirthCommitmentFinalMissTree_le_weight
    ring C hclean t
  have hweight := iidBirthUncommittedTreeTotal_le
    ring hn C hclean t
  have hcount := iidBirthUncommittedCount_le C
  have hscaled := Nat.mul_le_mul_left ((n - 1) ^ t) hcount
  calc
    iidBirthCommitmentFinalMissTree ring C t ≤
        iidBirthUncommittedTreeTotal ring C t := hmiss
    _ ≤ (n - 1) ^ t * iidBirthUncommittedCount C := hweight
    _ ≤ (n - 1) ^ t * n := hscaled
    _ = n * (n - 1) ^ t := Nat.mul_comm _ _

/-- Final hits and misses partition all `n^t` exact scheduler words. -/
theorem iidBirthCommitmentFinal_partition
    (ring : DirectedRing n) (C : IidBirthConfig n psi kappa tau)
    (t : Nat) :
    iidBirthCommitmentFinalMissTree ring C t +
      iidBirthCommitmentFinalHitTree ring C t = n ^ t := by
  induction t generalizing C with
  | zero =>
      simp only [iidBirthCommitmentFinalMissTree,
        iidBirthCommitmentFinalHitTree, Nat.pow_zero]
      by_cases hall : IidBirthAllCommitted C <;> simp [hall]
  | succ t ih =>
      simp only [iidBirthCommitmentFinalMissTree,
        iidBirthCommitmentFinalHitTree]
      rw [← sum_ofFn_add]
      calc
        (List.ofFn (fun e =>
          iidBirthCommitmentFinalMissTree ring
              (localStep ring P_partialSealIidBirth C e) t +
            iidBirthCommitmentFinalHitTree ring
              (localStep ring P_partialSealIidBirth C e) t)).sum =
            (List.ofFn (fun _ : Fin n => n ^ t)).sum := by
              apply sum_ofFn_eq
              intro e
              exact ih (localStep ring P_partialSealIidBirth C e)
        _ = n * n ^ t := sum_ofFn_const n _
        _ = n ^ (t + 1) := by
          rw [Nat.pow_succ]
          exact Nat.mul_comm _ _

/-! ## Quadratic-horizon arithmetic -/

private theorem pow_add_one_lower_two_terms (a t : Nat) :
    a ^ (t + 1) + (t + 1) * a ^ t ≤ (a + 1) ^ (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmul := Nat.mul_le_mul_right (a + 1) ih
      have hfirst :
          a ^ (Nat.succ t + 1) +
              (Nat.succ t + 1) * a ^ Nat.succ t ≤
            (a ^ (t + 1) + (t + 1) * a ^ t) * (a + 1) := by
        calc
          a ^ (Nat.succ t + 1) +
                (Nat.succ t + 1) * a ^ Nat.succ t ≤
              a ^ (Nat.succ t + 1) +
                  (Nat.succ t + 1) * a ^ Nat.succ t +
                    (t + 1) * a ^ t :=
            Nat.le_add_right _ _
          _ = (a ^ (t + 1) + (t + 1) * a ^ t) *
                (a + 1) := by
            simp only [Nat.succ_eq_add_one, Nat.pow_succ,
              Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
              Nat.mul_assoc]
            ac_rfl
      simpa only [Nat.succ_eq_add_one] using Nat.le_trans hfirst (by
        simpa only [Nat.pow_succ] using hmul)

/-- Over `n^2` trials, avoiding one fixed edge is smaller by a factor at
least `n+2` than the complete scheduler tree. -/
theorem iidBirth_quadratic_avoid_ratio
    (hn : 1 < n) :
    (n + 2) * (n - 1) ^ (n * n) ≤ n ^ (n * n) := by
  let a := n - 1
  let H := n * n
  have ha : 0 < a := by dsimp [a]; omega
  have hH : 0 < H := by
    dsimp [H]
    exact Nat.mul_pos (by omega) (by omega)
  have hsplit : H = (H - 1) + 1 := by omega
  have hbin := pow_add_one_lower_two_terms a (H - 1)
  rw [← hsplit] at hbin
  have hcoeff : (n + 1) * a ≤ H := by
    have hnA : n = a + 1 := by
      dsimp [a]
      omega
    dsimp [H]
    rw [hnA]
    calc
      (a + 1 + 1) * a ≤ (a + 1 + 1) * a + 1 :=
        Nat.le_add_right _ _
      _ = (a + 1) * (a + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
  have hcoeffScaled := Nat.mul_le_mul_right (a ^ (H - 1)) hcoeff
  have hpow : a ^ H = a ^ (H - 1) * a := by
    calc
      a ^ H = a ^ ((H - 1) + 1) :=
        congrArg (fun t => a ^ t) hsplit
      _ = a ^ (H - 1) * a := by rw [Nat.pow_succ]
  have hlower : (n + 2) * a ^ H ≤
      a ^ H + H * a ^ (H - 1) := by
    rw [hpow]
    calc
      (n + 2) * (a ^ (H - 1) * a) =
          a ^ (H - 1) * a +
            ((n + 1) * a) * a ^ (H - 1) := by
        have hn2 : n + 2 = 1 + (n + 1) := by omega
        rw [hn2, Nat.add_mul, Nat.one_mul]
        ac_rfl
      _ ≤ a ^ (H - 1) * a + H * a ^ (H - 1) :=
        by
          simpa only [Nat.mul_assoc] using
            Nat.add_le_add_left hcoeffScaled (a ^ (H - 1) * a)
  have haSucc : a + 1 = n := by dsimp [a]; omega
  rw [haSucc] at hbin
  simpa only [a, H] using Nat.le_trans hlower hbin

/-- At quadratic horizon the exact endpoint-success mass is at least
`2/(n+2)`.  This is the division-free integer form. -/
theorem iidBirthCommitmentFinalHitTree_inverse_linear
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) :
    2 * n ^ (n * n) ≤
      (n + 2) * iidBirthCommitmentFinalHitTree ring C (n * n) := by
  let H := n * n
  let miss := iidBirthCommitmentFinalMissTree ring C H
  let hit := iidBirthCommitmentFinalHitTree ring C H
  let avoid := (n - 1) ^ H
  have hmiss : miss ≤ n * avoid := by
    exact iidBirthCommitmentFinalMissTree_le ring hn C hclean H
  have hratio : (n + 2) * avoid ≤ n ^ H := by
    exact iidBirth_quadratic_avoid_ratio hn
  have hscaled := Nat.mul_le_mul_left (n + 2) hmiss
  have hscaledRatio := Nat.mul_le_mul_left n hratio
  have hpartition : miss + hit = n ^ H := by
    exact iidBirthCommitmentFinal_partition ring C H
  have hscaled' : (n + 2) *
      miss ≤ n * ((n + 2) * avoid) := by
    calc
      (n + 2) * miss ≤
          (n + 2) * (n * avoid) := hscaled
      _ = n * ((n + 2) * avoid) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hfail : (n + 2) * miss ≤ n * n ^ H :=
    Nat.le_trans hscaled' hscaledRatio
  have hfail' : (n + 2) * miss ≤ n * (miss + hit) := by
    simpa [hpartition] using hfail
  rw [Nat.add_mul, Nat.mul_add] at hfail'
  have htwoMiss : 2 * miss ≤ n * hit := by
    omega
  change 2 * n ^ H ≤ (n + 2) * hit
  calc
    2 * n ^ H = 2 * (miss + hit) := by rw [hpartition]
    _ = 2 * miss + 2 * hit := by rw [Nat.mul_add]
    _ ≤ n * hit + 2 * hit := Nat.add_le_add_right htwoMiss _
    _ = (n + 2) * hit := by rw [Nat.add_mul]

/-! ## Authorized-domain interface -/

def IidBirthCommittedPositive
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  IidBirthAllCommitted C ∧ IidBirthPositive C

/-- The exact post-commitment interface on every nonempty ring.  The second
branch is needed only on the one-agent self-edge, whose birth kernel is not
the two-site open-balanced positive state. -/
def IidBirthCommittedEntry
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  IidBirthCommittedPositive C ∨ IidBirthSingletonKernel C

/-- The committed-positive interface is a closed exact refinement of the
inner R91 seal-sweep dynamics: every outer suffix remains committed-positive
and erases to the inner suffix on the same scheduler word. -/
theorem iidBirthCommittedPositive_run_simulation
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthCommittedPositive C) (word : DetSchedule n) :
    let D := runLocalSchedule ring P_partialSealIidBirth C word
    IidBirthCommittedPositive D ∧
      iidBirthErase D =
        runLocalSchedule ring P_partialSealSweep (iidBirthErase C) word := by
  let D := runLocalSchedule ring P_partialSealIidBirth C word
  have hsimulation :=
    iidBirth_committed_run_simulation ring C hC.1 word
  change IidBirthAllCommitted D ∧
    iidBirthErase D =
      runLocalSchedule ring P_partialSealSweep (iidBirthErase C) word
    at hsimulation
  have hpositive : IidBirthPositive D :=
    localStepClosed_runLocalSchedule
      ring P_partialSealIidBirth IidBirthPositive
      (fun X hX edge => iidBirthPositive_localStep ring X hX edge)
      hC.2 word
  exact ⟨⟨hsimulation.1, hpositive⟩, hsimulation.2⟩

/-- Once random commitment has entered `IidBirthCommittedPositive`, no
additional barrier sweep is needed: the existing tight inner landing theorem
is consumed directly through exact committed simulation. -/
theorem iidBirthCommittedPositive_reaches_isSafe_inner_short
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthCommittedPositive C) :
    ∃ word : DetSchedule n,
      word.length ≤ iidBirthInnerLandingLength n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  obtain ⟨word, hlength, hsafe⟩ :=
    sealSweep_balancedPositive_reaches_isSafe_half_tight
      ring (iidBirthErase C) hC.2.2.1 hC.2.2.2.1
  let D := runLocalSchedule ring P_partialSealIidBirth C word
  have hsimulation := iidBirthCommittedPositive_run_simulation
    ring C hC word
  change IidBirthCommittedPositive D ∧
    iidBirthErase D =
      runLocalSchedule ring P_partialSealSweep (iidBirthErase C) word
    at hsimulation
  have hEraseSafe : PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring
      (iidBirthErase D) isLeaderOutput := by
    rw [hsimulation.2]
    exact hsafe
  exact ⟨word, hlength,
    iidBirthAllCommitted_lift_isSafe
      ring D hsimulation.1.1 hEraseSafe⟩

theorem iidBirthDomain_armedClean
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) : IidBirthArmedClean C := by
  rcases hC with hzero | hpositive | hsingleton
  · exact iidBirthZeroStart_armedClean C hzero
  · exact hpositive.1
  · intro i hi
    rw [hsingleton.2.1 i] at hi
    contradiction

/-- On a nontrivial ring, every all-committed endpoint reached from the
authorized restart domain is in the precise committed-positive interface
needed by the inner seal-sweep phase. -/
theorem iidBirthDomain_allCommitted_run_committedPositive
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) (word : DetSchedule n)
    (hall : IidBirthAllCommitted
      (runLocalSchedule ring P_partialSealIidBirth C word)) :
    IidBirthCommittedPositive
      (runLocalSchedule ring P_partialSealIidBirth C word) := by
  refine ⟨hall, ?_⟩
  rcases hC with hzero | hpositive | hsingleton
  · cases word with
    | nil =>
        let i : Fin n := ⟨0, ring.hn⟩
        have hopen := hzero.1 i
        have hclosed := hall i
        simp only [runLocalSchedule] at hclosed
        rw [hopen] at hclosed
        contradiction
    | cons e rest =>
        have hfirst := iidBirthZeroStart_localStep_positive
          ring hn C hzero e
        exact localStepClosed_runLocalSchedule
          ring P_partialSealIidBirth IidBirthPositive
          (fun X hX edge => iidBirthPositive_localStep ring X hX edge)
          hfirst rest
  · exact localStepClosed_runLocalSchedule
      ring P_partialSealIidBirth IidBirthPositive
      (fun X hX edge => iidBirthPositive_localStep ring X hX edge)
      hpositive word
  · exfalso
    have hone : n = 1 := hsingleton.1
    omega

/-- Every successful nontrivial commitment prefix has the same uniform inner
consumer bound.  This is the exact handoff needed to compose the entry-mass
phase with any many-word inner convergence theorem. -/
theorem iidBirthDomain_allCommitted_run_reaches_isSafe_inner_short
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) (pre : DetSchedule n)
    (hall : IidBirthAllCommitted
      (runLocalSchedule ring P_partialSealIidBirth C pre)) :
    ∃ tail : DetSchedule n,
      tail.length ≤ iidBirthInnerLandingLength n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth
          (runLocalSchedule ring P_partialSealIidBirth C pre) tail)
        isLeaderOutput := by
  have hentry := iidBirthDomain_allCommitted_run_committedPositive
    ring hn C hC pre hall
  exact iidBirthCommittedPositive_reaches_isSafe_inner_short
    ring (runLocalSchedule ring P_partialSealIidBirth C pre) hentry

/-- Without excluding the self-edge ring, a committed endpoint reached from
the authorized domain lies in either the positive R94 interface or its exact
one-agent kernel. -/
theorem iidBirthDomain_allCommitted_run_committedEntry
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) (word : DetSchedule n)
    (hall : IidBirthAllCommitted
      (runLocalSchedule ring P_partialSealIidBirth C word)) :
    IidBirthCommittedEntry
      (runLocalSchedule ring P_partialSealIidBirth C word) := by
  have hdomain := localStepClosed_runLocalSchedule
    ring P_partialSealIidBirth IidBirthDomain
    (iidBirthDomain_localStepClosed ring) hC word
  rcases hdomain with hzero | hpositive | hsingleton
  · let i : Fin n := ⟨0, ring.hn⟩
    have hopen := hzero.1 i
    have hclosed := hall i
    rw [hopen] at hclosed
    contradiction
  · exact Or.inl ⟨hall, hpositive⟩
  · exact Or.inr hsingleton

/-- On every scheduler word from the authorized domain, the tree predicate
`IidBirthAllCommitted` is exactly the intended post-entry interface, not a
disconnected auxiliary event. -/
theorem iidBirthDomain_run_committedEntry_iff_allCommitted
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) (word : DetSchedule n) :
    IidBirthCommittedEntry
        (runLocalSchedule ring P_partialSealIidBirth C word) ↔
      IidBirthAllCommitted
        (runLocalSchedule ring P_partialSealIidBirth C word) := by
  constructor
  · intro hentry
    rcases hentry with hpositive | hsingleton
    · exact hpositive.1
    · exact hsingleton.2.1
  · exact iidBirthDomain_allCommitted_run_committedEntry
      ring C hC word

/-- On the one-agent ring, every authorized start is committed after the
single possible interaction: zero-start births, while positive and singleton
starts were already committed. -/
theorem iidBirthDomain_one_finalHitTree
    (ring : DirectedRing 1)
    (C : IidBirthConfig 1 psi kappa tau)
    (hC : IidBirthDomain C) :
    iidBirthCommitmentFinalHitTree ring C 1 = 1 := by
  have hstep : ∀ e : Fin 1,
      IidBirthAllCommitted
        (localStep ring P_partialSealIidBirth C e) := by
    intro e
    rcases hC with hzero | hpositive | hsingleton
    · exact (iidBirthZeroStart_localStep_singleton
        ring C hzero e).2.1
    · have hall : IidBirthAllCommitted C := by
        obtain ⟨root, hroot⟩ := hpositive.2.2.2
        intro i
        have hir : i = root := Subsingleton.elim _ _
        subst i
        exact hroot
      exact iidBirthAllCommitted_localStep ring C hall e
    · exact iidBirthAllCommitted_localStep
        ring C hsingleton.2.1 e
  change (List.ofFn (fun e : Fin 1 =>
    iidBirthCommitmentFinalHitTree ring
      (localStep ring P_partialSealIidBirth C e) 0)).sum = 1
  calc
    (List.ofFn (fun e : Fin 1 =>
      iidBirthCommitmentFinalHitTree ring
        (localStep ring P_partialSealIidBirth C e) 0)).sum =
        (List.ofFn (fun _ : Fin 1 => 1)).sum := by
          apply sum_ofFn_eq
          intro e
          simp only [iidBirthCommitmentFinalHitTree]
          rw [if_pos (hstep e)]
    _ = 1 := by simpa using sum_ofFn_const 1 1

/-- Every authorized nontrivial start therefore has the same inverse-linear
quadratic-horizon entry mass. -/
theorem iidBirthDomain_commitmentEntry_inverse_linear
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) :
    2 * n ^ (n * n) ≤
      (n + 2) * iidBirthCommitmentFinalHitTree ring C (n * n) :=
  iidBirthCommitmentFinalHitTree_inverse_linear
    ring hn C (iidBirthDomain_armedClean C hC)

/-- All authorized restart-domain configurations, including the exact
one-agent branch, have inverse-linear endpoint entry mass by horizon `n^2`. -/
theorem iidBirthDomain_commitmentEntry_inverse_linear_all
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthDomain C) :
    2 * n ^ (n * n) ≤
      (n + 2) * iidBirthCommitmentFinalHitTree ring C (n * n) := by
  by_cases hn : n = 1
  · subst n
    have hhit := iidBirthDomain_one_finalHitTree ring C hC
    simp [hhit]
  · have hnTwo : 1 < n := by
      have hnPos := ring.hn
      omega
    exact iidBirthDomain_commitmentEntry_inverse_linear
      ring hnTwo C hC

end PPartialSealSweepIidBirthEntryMassSol
end PPLLCompleteMultiLeaderCleanup
