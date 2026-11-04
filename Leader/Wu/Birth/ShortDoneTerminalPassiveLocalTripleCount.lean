import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTriple
import Leader.Core.ThreePortSerialCount

namespace BirthShortDoneTerminalPassiveLocal3Count

open FiniteUniformStoppingTree
open BirthShortDoneTerminalPassiveLocal3
open ThreePortSerialCount

set_option autoImplicit false

variable {n : Nat}

private def ports0 (hn : 4 <= n) : ThreePortSerialCount.Ports n := {
  a := p0 hn
  b := p2 hn
  c := leftCross hn
  ab := Fin.ne_of_val_ne (by simp [p0, p2])
  ac := Fin.ne_of_val_ne (by simp [p0, leftCross]; omega)
  bc := Fin.ne_of_val_ne (by simp [p2, leftCross]; omega) }

private def ports1 (hn : 4 <= n) : ThreePortSerialCount.Ports n := {
  a := p1 hn
  b := p2 hn
  c := leftCross hn
  ab := Fin.ne_of_val_ne (by simp [p1, p2])
  ac := Fin.ne_of_val_ne (by simp [p1, leftCross]; omega)
  bc := Fin.ne_of_val_ne (by simp [p2, leftCross]; omega) }

/-- Original raw scheduler. Only p2 and leftCross fail in either phase. -/
def twoCrossStep (hn : 4 <= n) : Bool -> Fin n -> StopNode Bool
  | false, e =>
      if e = (ports0 hn).a then .active true
      else if e = (ports0 hn).b then .failure
      else if e = (ports0 hn).c then .failure
      else .active false
  | true, e =>
      if e = (ports1 hn).a then .success
      else if e = (ports1 hn).b then .failure
      else if e = (ports1 hn).c then .failure
      else .active true

private theorem sum_spike (n : Nat) :
    forall (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have hz :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          calc
            (List.ofFn (fun i : Fin n =>
                if i.succ = (0 : Fin (n + 1)) then v else 0)).sum =
                (List.ofFn (fun _ : Fin n => 0)).sum := by
                  apply ofFn_sum_eq
                  intro i
                  have hne : i.succ ≠ (0 : Fin (n + 1)) := by
                    intro he
                    have hv : i.val + 1 = 0 := by
                      simpa using congrArg Fin.val he
                    omega
                  exact if_neg hne
            _ = 0 := by
              simp only [ofFn_sum_const, Nat.mul_zero]
        simp [hz]
      · intro b
        have hz : (0 : Fin (n + 1)) ≠ b.succ := by
          intro he
          have hv : 0 = b.val + 1 := by
            simpa using congrArg Fin.val he
          omega
        rw [List.ofFn_succ, List.sum_cons]
        simp only [hz, ite_false, Nat.zero_add]
        calc
          (List.ofFn (fun i : Fin n =>
              if i.succ = b.succ then v else 0)).sum =
              (List.ofFn (fun i : Fin n => if i = b then v else 0)).sum := by
                apply ofFn_sum_eq
                intro i
                simp only [Fin.succ_inj]
          _ = v := ih b v

private theorem sum_three {n : Nat} (p : ThreePortSerialCount.Ports n)
    (hn : 3 <= n) (f : Fin n -> Nat) (q : Nat)
    (ho : forall e, e ≠ p.a -> e ≠ p.b -> e ≠ p.c -> f e = q) :
    (List.ofFn f).sum = f p.a + f p.b + f p.c + (n-3)*q := by
  have hp : forall e : Fin n,
      f e + (if e=p.a then q else 0) + (if e=p.b then q else 0) +
          (if e=p.c then q else 0) =
        q + (if e=p.a then f p.a else 0) +
          (if e=p.b then f p.b else 0) +
          (if e=p.c then f p.c else 0) := by
    intro e
    by_cases ha : e=p.a
    · subst e; simp [p.ab, p.ac, Nat.add_comm]
    · by_cases hb : e=p.b
      · subst e; simp [p.ab.symm, p.bc, Nat.add_comm]
      · by_cases hc : e=p.c
        · subst e; simp [p.ac.symm, p.bc.symm, Nat.add_comm]
        · simp [ha,hb,hc,ho e ha hb hc]
  have hs := ofFn_sum_eq _ _ hp
  simp only [ofFn_sum_add, sum_spike, ofFn_sum_const] at hs
  have hm : n*q = (n-3)*q + 3*q := by
    calc
      n*q = ((n-3)+3)*q := by
        rw [show (n-3)+3 = n by omega]
      _ = (n-3)*q + 3*q := Nat.add_mul _ _ _
  omega

private theorem first_sum (hn : 4 <= n)
    (w : StopNode Bool -> Nat) :
    (List.ofFn (fun e : Fin n => w (twoCrossStep hn false e))).sum =
      w (.active true) + w .failure + w .failure +
        (n-3) * w (.active false) := by
  have hs := sum_three (ports0 hn) (by omega)
    (fun e => w (twoCrossStep hn false e)) (w (.active false)) (by
      intro e ha hb hc
      simp [twoCrossStep, ha, hb, hc])
  have hba : (ports0 hn).b ≠ (ports0 hn).a := (ports0 hn).ab.symm
  have hca : (ports0 hn).c ≠ (ports0 hn).a := (ports0 hn).ac.symm
  have hcb : (ports0 hn).c ≠ (ports0 hn).b := (ports0 hn).bc.symm
  simpa [twoCrossStep, hba, hca, hcb] using hs

private theorem first_succ (hn : 4 <= n) (T : Nat) :
    successCount (twoCrossStep hn) (.active false) (T+1) =
      successCount (twoCrossStep hn) (.active true) T +
        (n-3) * successCount (twoCrossStep hn) (.active false) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (twoCrossStep hn) successWeight
      (twoCrossStep hn false e) T)).sum = _
  rw [first_sum hn (fun y => treeWeight (twoCrossStep hn) successWeight y T)]
  simp [treeWeight_failure, successWeight, successCount]

private theorem second_eq_stage (hn : 4 <= n) (T : Nat) :
    successCount (twoCrossStep hn) (.active true) T =
      successCount (ThreePortSerialCount.stageStep (ports1 hn))
        (.active ()) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun e : Fin n =>
        treeWeight (twoCrossStep hn) successWeight
          (twoCrossStep hn true e) T)).sum = _
      rw [ThreePortSerialCount.stage_success_succ (ports1 hn) (by omega) T]
      have hs := sum_three (ports1 hn) (by omega)
        (fun e => treeWeight (twoCrossStep hn) successWeight
          (twoCrossStep hn true e) T)
        (successCount (twoCrossStep hn) (.active true) T) (by
          intro e ha hb hc
          simp [twoCrossStep, ha, hb, hc, successCount])
      have hba : (ports1 hn).b ≠ (ports1 hn).a := (ports1 hn).ab.symm
      have hca : (ports1 hn).c ≠ (ports1 hn).a := (ports1 hn).ac.symm
      have hcb : (ports1 hn).c ≠ (ports1 hn).b := (ports1 hn).bc.symm
      rw [hs]
      dsimp only [successCount] at ih
      simp [twoCrossStep, hba, hca, hcb, treeWeight_success, treeWeight_failure,
        successWeight, successCount, ih]

/-- Stopped-prefix composition of two different one-good/two-bad stages. -/
theorem two_stage_lower (hn : 4 <= n) (u v : Nat) :
    successCount (ThreePortSerialCount.stageStep (ports0 hn)) (.active ()) u *
      successCount (ThreePortSerialCount.stageStep (ports1 hn)) (.active ()) v <=
    successCount (twoCrossStep hn) (.active false) (u+v) := by
  induction u with
  | zero => simp [successCount, treeWeight, successWeight]
  | succ u ih =>
      have hpad : n^u *
          successCount (ThreePortSerialCount.stageStep (ports1 hn)) (.active ()) v <=
          successCount (ThreePortSerialCount.stageStep (ports1 hn))
            (.active ()) (u+v) := by
        simpa only [Nat.add_comm] using
          ThreePortSerialCount.success_padding
            (ThreePortSerialCount.stageStep (ports1 hn)) (.active ()) v u
      calc
        _ = (n^u + (n-3) *
              successCount (ThreePortSerialCount.stageStep (ports0 hn))
                (.active ()) u) *
              successCount (ThreePortSerialCount.stageStep (ports1 hn))
                (.active ()) v := by
          rw [ThreePortSerialCount.stage_success_succ (ports0 hn) (by omega) u]
        _ = n^u * successCount (ThreePortSerialCount.stageStep (ports1 hn))
              (.active ()) v +
            (n-3) * (successCount (ThreePortSerialCount.stageStep (ports0 hn))
              (.active ()) u *
              successCount (ThreePortSerialCount.stageStep (ports1 hn))
                (.active ()) v) := by rw [Nat.add_mul]; ac_rfl
        _ <= successCount (ThreePortSerialCount.stageStep (ports1 hn))
              (.active ()) (u+v) +
            (n-3) * successCount (twoCrossStep hn) (.active false) (u+v) :=
          Nat.add_le_add hpad (Nat.mul_le_mul_left _ ih)
        _ = successCount (twoCrossStep hn) (.active false) ((u+1)+v) := by
          rw [show (u+1)+v = (u+v)+1 by omega,
            first_succ hn (u+v), second_eq_stage hn (u+v)]

/-- Original n-ary scheduler mass; no conditioning and no host replacement. -/
theorem two_cross_sixteenth (hn : 4 <= n) :
    n^(4*n) <= 16 *
      successCount (twoCrossStep hn) (.active false) (4*n) := by
  let s0 := successCount (ThreePortSerialCount.stageStep (ports0 hn))
    (.active ()) (2*n)
  let s1 := successCount (ThreePortSerialCount.stageStep (ports1 hn))
    (.active ()) (2*n)
  have h0 : n^(2*n) <= 4*s0 :=
    ThreePortSerialCount.single_stage_quarter (ports0 hn) (by omega)
  have h1 : n^(2*n) <= 4*s1 :=
    ThreePortSerialCount.single_stage_quarter (ports1 hn) (by omega)
  have hc : s0*s1 <= successCount (twoCrossStep hn) (.active false) (4*n) := by
    simpa only [show 2*n + 2*n = 4*n by omega] using
      two_stage_lower hn (2*n) (2*n)
  calc
    n^(4*n) = n^(2*n) * n^(2*n) := by
      rw [<- Nat.pow_add, show 2*n + 2*n = 4*n by omega]
    _ <= (4*s0)*(4*s1) := Nat.mul_le_mul h0 h1
    _ = 16*(s0*s1) := by ac_rfl
    _ <= 16*successCount (twoCrossStep hn) (.active false) (4*n) :=
      Nat.mul_le_mul_left 16 hc

#print axioms BirthShortDoneTerminalPassiveLocal3Count.two_cross_sixteenth

end BirthShortDoneTerminalPassiveLocal3Count
