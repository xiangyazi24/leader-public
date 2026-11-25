import Leader.L4.Height.LeaderBridge

namespace L4.Height

set_option autoImplicit false

open Classical

/-!
Conditional Bellman algebra for the augmented steered chain.

The physical state may need candidate-prefix and escrow history so that
the next-letter map is Markovian.  K is the serial rank multiplier;
K = n is the value used in the residual analysis, and n <= K is necessary in general.

otherSerial plus entryEscrow express all-letter EF nonincrease from a
serial state, even when the next letter enters FENCE.  otherFence plus
exitEscrow express all-letter serial-rank nonincrease from a FENCE state.
At an exit the FENCE escrow is also discharged.

The oneFence condition is a physical one-excursion bookkeeping
obligation, unused by the local Bellman algebra but needed in the
construction and initial bound of EF.  No physical instantiation of
these hypotheses is asserted here.
-/

structure ResidualPotentialData {S : Type} {n : Nat} where
  next : S → Fin n → S
  Q : S → Prop
  P : S → Prop
  inFence : S → Prop
  Rserial : S → Nat
  EF : S → Nat
  K : Nat
  hweight : n ≤ K
  closed : ∀ (y : S) (e : Fin n), Q y → Q (next y e)
  hserial : ∀ (y : S), Q y → ¬ P y → ¬ inFence y →
    (∀ e : Fin n, Rserial (next y e) ≤ Rserial y) ∧
    (∃ e : Fin n, Rserial (next y e) + 1 ≤ Rserial y)
  hfence : ∀ (y : S), Q y → ¬ P y → inFence y →
    n + (List.ofFn (fun e : Fin n => EF (next y e))).sum ≤ n * EF y
  otherSerial : ∀ (y : S) (e : Fin n),
    Q y → ¬ P y → ¬ inFence y → ¬ inFence (next y e) →
      EF (next y e) ≤ EF y
  otherFence : ∀ (y : S) (e : Fin n),
    Q y → ¬ P y → inFence y → inFence (next y e) →
      Rserial (next y e) ≤ Rserial y
  entryEscrow : ∀ (y : S) (e : Fin n),
    Q y → ¬ P y → ¬ inFence y → inFence (next y e) →
      EF (next y e) ≤ EF y
  exitEscrow : ∀ (y : S) (e : Fin n),
    Q y → ¬ P y → inFence y → ¬ inFence (next y e) →
      Rserial (next y e) ≤ Rserial y ∧ EF (next y e) = 0
  oneFence : ∀ (y : S) (before gap tail : List (Fin n)),
    Q y →
    inFence (runWord next y before) →
    ¬ inFence (runWord next y (before ++ gap)) →
    ¬ P (runWord next y (before ++ gap ++ tail)) →
    ¬ inFence (runWord next y (before ++ gap ++ tail))

/-- The residual potential is recovered by setting K = n. -/
def ResidualPotentialData.Phi {S : Type} {n : Nat}
    (D : ResidualPotentialData (S := S) (n := n)) (y : S) : Nat :=
  D.K * D.Rserial y + D.EF y

/-- One strict decrease saves exactly one unit in the unweighted sum. -/
private theorem residual_sum_one_strict :
    ∀ (m : Nat) (f : Fin m → Nat) (b : Nat),
      (∀ e, f e ≤ b) →
      (∃ e, f e + 1 ≤ b) →
      1 + (List.ofFn f).sum ≤ m * b := by
  intro m
  induction m with
  | zero =>
      intro f b hweak hit
      rcases hit with ⟨e, _⟩
      exact Fin.elim0 e
  | succ m ih =>
      intro f b hweak hit
      rcases hit with ⟨e, he⟩
      cases e using Fin.cases with
      | zero =>
          have htail :
              (List.ofFn (fun j : Fin m => f j.succ)).sum ≤ m * b := by
            calc
              _ ≤ (List.ofFn (fun _ : Fin m => b)).sum :=
                sum_ofFn_le _ _ (fun j => hweak j.succ)
              _ = m * b := sum_ofFn_const m b
          simp only [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
          omega
      | succ j =>
          have htail :
              1 + (List.ofFn (fun k : Fin m => f k.succ)).sum ≤ m * b :=
            ih (fun k => f k.succ) b (fun k => hweak k.succ) ⟨j, he⟩
          have hfirst : f 0 ≤ b := hweak 0
          simp only [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
          omega

/-- Split the raw candidate-letter sum into the serial and escrow sums. -/
private theorem residual_phi_sum {S : Type} {n : Nat}
    (D : ResidualPotentialData (S := S) (n := n)) (y : S) :
    (List.ofFn (fun e : Fin n => D.Phi (D.next y e))).sum =
      D.K * (List.ofFn (fun e : Fin n => D.Rserial (D.next y e))).sum +
        (List.ofFn (fun e : Fin n => D.EF (D.next y e))).sum := by
  change
    (List.ofFn (fun e : Fin n =>
      D.K * D.Rserial (D.next y e) + D.EF (D.next y e))).sum =
      D.K * (List.ofFn (fun e : Fin n => D.Rserial (D.next y e))).sum +
        (List.ofFn (fun e : Fin n => D.EF (D.next y e))).sum
  rw [sum_ofFn_add, sum_ofFn_mul_left]

/-- Bellman drift on the closed, off-target part of the steered chain. -/
theorem residual_potential_step {S : Type} {n : Nat}
    (D : ResidualPotentialData (S := S) (n := n))
    (y : S) (hq : D.Q y) (hnot : ¬ D.P y) :
    n + (List.ofFn (fun e : Fin n => D.Phi (D.next y e))).sum
      ≤ n * D.Phi y := by
  by_cases hf : D.inFence y
  · have hother : ∀ e : Fin n,
        D.Rserial (D.next y e) ≤ D.Rserial y := by
      intro e
      by_cases hnext : D.inFence (D.next y e)
      · exact D.otherFence y e hq hnot hf hnext
      · exact (D.exitEscrow y e hq hnot hf hnext).1
    have hR :
        (List.ofFn (fun e : Fin n => D.Rserial (D.next y e))).sum
          ≤ n * D.Rserial y := by
      calc
        _ ≤ (List.ofFn (fun _ : Fin n => D.Rserial y)).sum :=
          sum_ofFn_le _ _ hother
        _ = n * D.Rserial y :=
          sum_ofFn_const n (D.Rserial y)
    have hE := D.hfence y hq hnot hf
    calc
      n + (List.ofFn (fun e : Fin n => D.Phi (D.next y e))).sum
          = (n + (List.ofFn (fun e : Fin n => D.EF (D.next y e))).sum) +
              D.K * (List.ofFn (fun e : Fin n =>
                D.Rserial (D.next y e))).sum := by
            rw [residual_phi_sum D y]
            omega
      _ ≤ n * D.EF y +
            D.K * (List.ofFn (fun e : Fin n =>
              D.Rserial (D.next y e))).sum :=
        Nat.add_le_add_right hE _
      _ ≤ n * D.EF y + D.K * (n * D.Rserial y) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left D.K hR) _
      _ = n * D.Phi y := by
        unfold ResidualPotentialData.Phi
        rw [Nat.mul_add]
        ac_rfl
  · obtain ⟨hweak, hstrict⟩ := D.hserial y hq hnot hf
    have hR :
        1 + (List.ofFn (fun e : Fin n =>
          D.Rserial (D.next y e))).sum ≤ n * D.Rserial y :=
      residual_sum_one_strict n
        (fun e : Fin n => D.Rserial (D.next y e))
        (D.Rserial y) hweak hstrict
    have hother : ∀ e : Fin n, D.EF (D.next y e) ≤ D.EF y := by
      intro e
      by_cases hnext : D.inFence (D.next y e)
      · exact D.entryEscrow y e hq hnot hf hnext
      · exact D.otherSerial y e hq hnot hf hnext
    have hE :
        (List.ofFn (fun e : Fin n => D.EF (D.next y e))).sum
          ≤ n * D.EF y := by
      calc
        _ ≤ (List.ofFn (fun _ : Fin n => D.EF y)).sum :=
          sum_ofFn_le _ _ hother
        _ = n * D.EF y :=
          sum_ofFn_const n (D.EF y)
    have hweighted :
        n + D.K * (List.ofFn (fun e : Fin n =>
          D.Rserial (D.next y e))).sum
          ≤ n * (D.K * D.Rserial y) := by
      calc
        n + D.K * (List.ofFn (fun e : Fin n =>
            D.Rserial (D.next y e))).sum
          ≤ D.K + D.K * (List.ofFn (fun e : Fin n =>
              D.Rserial (D.next y e))).sum :=
            Nat.add_le_add_right D.hweight _
        _ = D.K * (1 + (List.ofFn (fun e : Fin n =>
              D.Rserial (D.next y e))).sum) := by
            rw [Nat.mul_add, Nat.mul_one]
        _ ≤ D.K * (n * D.Rserial y) :=
            Nat.mul_le_mul_left D.K hR
        _ = n * (D.K * D.Rserial y) := by ac_rfl
    calc
      n + (List.ofFn (fun e : Fin n => D.Phi (D.next y e))).sum
          = (n + D.K * (List.ofFn (fun e : Fin n =>
              D.Rserial (D.next y e))).sum) +
              (List.ofFn (fun e : Fin n => D.EF (D.next y e))).sum := by
            rw [residual_phi_sum D y]
            omega
      _ ≤ n * (D.K * D.Rserial y) +
            (List.ofFn (fun e : Fin n => D.EF (D.next y e))).sum :=
        Nat.add_le_add_right hweighted _
      _ ≤ n * (D.K * D.Rserial y) + n * D.EF y :=
        Nat.add_le_add_left hE _
      _ = n * D.Phi y := by
        unfold ResidualPotentialData.Phi
        rw [Nat.mul_add]

/-- Direct first-hit cost induction.  Global iid_potential_le requires
drift outside Q, which is not available; closure allows us to prove the
same numerator inequality for each y in Q without extra assumptions. -/
theorem residual_expected {S : Type} {n : Nat}
    (D : ResidualPotentialData (S := S) (n := n))
    (y0 : S) (hy0 : D.Q y0) :
    IIDExpectedHittingTimeAtMost D.next D.P y0 (D.Phi y0) := by
  classical
  have hcost : ∀ (t : Nat) (y : S), D.Q y →
      iidHitCost D.next D.P t y ≤ D.Phi y * n ^ t := by
    intro t
    induction t with
    | zero =>
        intro y hy
        simp [iidHitCost]
    | succ t ih =>
        intro y hy
        by_cases hp : D.P y
        · rw [iidHitCost_of_target D.next D.P y hp (t + 1)]
          exact Nat.zero_le _
        · have hsum :
            (List.ofFn (fun e : Fin n =>
              iidHitCost D.next D.P t (D.next y e))).sum
              ≤ n ^ t *
                (List.ofFn (fun e : Fin n => D.Phi (D.next y e))).sum := by
            calc
              _ ≤ (List.ofFn (fun e : Fin n =>
                    D.Phi (D.next y e) * n ^ t)).sum := by
                  apply sum_ofFn_le
                  intro e
                  exact ih (D.next y e) (D.closed y e hy)
              _ = (List.ofFn (fun e : Fin n =>
                    n ^ t * D.Phi (D.next y e))).sum := by
                  apply sum_ofFn_eq
                  intro e
                  ac_rfl
              _ = n ^ t *
                    (List.ofFn (fun e : Fin n =>
                      D.Phi (D.next y e))).sum :=
                  sum_ofFn_mul_left (n ^ t)
                    (fun e : Fin n => D.Phi (D.next y e))
          have hstep := residual_potential_step D y hy hp
          calc
            iidHitCost D.next D.P (t + 1) y
                = n ^ (t + 1) +
                    (List.ofFn (fun e : Fin n =>
                      iidHitCost D.next D.P t (D.next y e))).sum := by
                    simp [iidHitCost, hp]
            _ ≤ n ^ (t + 1) +
                  n ^ t * (List.ofFn (fun e : Fin n =>
                    D.Phi (D.next y e))).sum :=
                Nat.add_le_add_left hsum _
            _ = n ^ t * (n +
                  (List.ofFn (fun e : Fin n =>
                    D.Phi (D.next y e))).sum) := by
                rw [Nat.pow_succ, Nat.mul_add]
            _ ≤ n ^ t * (n * D.Phi y) :=
                Nat.mul_le_mul_left _ hstep
            _ = D.Phi y * n ^ (t + 1) := by
                rw [Nat.pow_succ]
                ac_rfl
  intro t
  exact hcost t y0 hy0

/-- A proposed physical initial cap may be supplied separately. -/
theorem residual_expected_le {S : Type} {n : Nat}
    (D : ResidualPotentialData (S := S) (n := n))
    (y0 : S) (hy0 : D.Q y0) (A : Nat)
    (hA : D.Phi y0 ≤ A) :
    IIDExpectedHittingTimeAtMost D.next D.P y0 A := by
  intro t
  exact Nat.le_trans (residual_expected D y0 hy0 t)
    (Nat.mul_le_mul_right (n ^ t) hA)

/-!
Unweighted rank is insufficient.  With two labels and two states,
label zero changes false to true; label one stutters.  Serial rank is
one at false and zero at true.  Both weak and nominated strict
decrease hold, but weight one would require 2 + (0 + 1) <= 2*1.
-/

private def residualTwoStateNext (y : Bool) (e : Fin 2) : Bool :=
  if e = 0 then true else y

private def residualTwoStateRank (y : Bool) : Nat :=
  if y then 0 else 1

theorem residual_unweighted_counterexample :
    (∀ e : Fin 2,
      residualTwoStateRank (residualTwoStateNext false e) ≤
        residualTwoStateRank false) ∧
    (∃ e : Fin 2,
      residualTwoStateRank (residualTwoStateNext false e) + 1 ≤
        residualTwoStateRank false) ∧
    ¬ (2 + (List.ofFn (fun e : Fin 2 =>
          residualTwoStateRank (residualTwoStateNext false e))).sum ≤
        2 * residualTwoStateRank false) := by
  decide

#print axioms residual_potential_step
#print axioms residual_expected
#print axioms residual_expected_le
#print axioms residual_unweighted_counterexample

end L4.Height

