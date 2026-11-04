import Leader.Core.ThreePortSerialCount

set_option autoImplicit false

/-! # Three same-port hits before either bad port: success mass at least 1/64 over 6n

The V10e global progress theorem needs three consecutive services of one edge (the good port)
before the two neighbouring edges (the bad ports) interfere.  This is the three-hit analogue of
`ThreePortSerialCount.serialStep`: its count is the serial count followed by one more stage. -/

namespace B9SpliceTripleHitBridge

open FiniteUniformStoppingTree ThreePortSerialCount

/-- Number of good-port hits so far. -/
inductive Hits where
  | zero | one | two
  deriving DecidableEq, Repr

def tripleStep {n : Nat} (p : Ports n) : Hits → Fin n → StopNode Hits
  | .zero, e =>
      if e = p.a then .active .one
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active .zero
  | .one, e =>
      if e = p.a then .active .two
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active .one
  | .two, e =>
      if e = p.a then .success
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active .two

/-! ## Local copies of the private counting helpers of ThreePortSerialCount -/

private theorem sum_spike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have htail :
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
            _ = 0 := by simp only [ofFn_sum_const, Nat.mul_zero]
        simp [htail]
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

private theorem sum_three {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (f : Fin n → Nat) (q : Nat)
    (hother : ∀ e, e ≠ p.a → e ≠ p.b → e ≠ p.c → f e = q) :
    (List.ofFn f).sum = f p.a + f p.b + f p.c + (n - 3) * q := by
  have hp : ∀ e : Fin n,
      f e + (if e = p.a then q else 0) +
          (if e = p.b then q else 0) + (if e = p.c then q else 0) =
        q + (if e = p.a then f p.a else 0) +
          (if e = p.b then f p.b else 0) +
          (if e = p.c then f p.c else 0) := by
    intro e
    by_cases ha : e = p.a
    · subst e
      simp [p.ab, p.ac, Nat.add_comm]
    · by_cases hb : e = p.b
      · subst e
        simp [p.ab.symm, p.bc, Nat.add_comm]
      · by_cases hc : e = p.c
        · subst e
          simp [p.ac.symm, p.bc.symm, Nat.add_comm]
        · simp [ha, hb, hc, hother e ha hb hc]
  have hs := ofFn_sum_eq _ _ hp
  simp only [ofFn_sum_add, sum_spike, ofFn_sum_const] at hs
  have hmul : n * q = (n - 3) * q + 3 * q := by
    calc
      n * q = ((n - 3) + 3) * q := by
        rw [show (n - 3) + 3 = n by omega]
      _ = (n - 3) * q + 3 * q := Nat.add_mul _ _ _
  omega

/-! ## Child sums and recursions -/

private theorem triple_child_sum_zero {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Hits → Nat) :
    (List.ofFn (fun e : Fin n => w (tripleStep p .zero e))).sum =
      w (.active .one) + w .failure + w .failure + (n - 3) * w (.active .zero) := by
  have hs := sum_three p hn (fun e => w (tripleStep p .zero e)) (w (.active .zero)) (by
    intro e ha hb hc
    simp [tripleStep, ha, hb, hc])
  simpa [tripleStep, p.ab, p.ac, p.bc, p.ab.symm, p.ac.symm, p.bc.symm] using hs

private theorem triple_child_sum_one {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Hits → Nat) :
    (List.ofFn (fun e : Fin n => w (tripleStep p .one e))).sum =
      w (.active .two) + w .failure + w .failure + (n - 3) * w (.active .one) := by
  have hs := sum_three p hn (fun e => w (tripleStep p .one e)) (w (.active .one)) (by
    intro e ha hb hc
    simp [tripleStep, ha, hb, hc])
  simpa [tripleStep, p.ab, p.ac, p.bc, p.ab.symm, p.ac.symm, p.bc.symm] using hs

private theorem triple_child_sum_two {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Hits → Nat) :
    (List.ofFn (fun e : Fin n => w (tripleStep p .two e))).sum =
      w .success + w .failure + w .failure + (n - 3) * w (.active .two) := by
  have hs := sum_three p hn (fun e => w (tripleStep p .two e)) (w (.active .two)) (by
    intro e ha hb hc
    simp [tripleStep, ha, hb, hc])
  simpa [tripleStep, p.ab, p.ac, p.bc, p.ab.symm, p.ac.symm, p.bc.symm] using hs

theorem triple_zero_succ {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (tripleStep p) (.active .zero) (T + 1) =
      successCount (tripleStep p) (.active .one) T +
        (n - 3) * successCount (tripleStep p) (.active .zero) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (tripleStep p) successWeight (tripleStep p .zero e) T)).sum = _
  rw [triple_child_sum_zero p hn (fun y => treeWeight (tripleStep p) successWeight y T)]
  simp [treeWeight_failure, successWeight, successCount]

theorem triple_one_succ {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (tripleStep p) (.active .one) (T + 1) =
      successCount (tripleStep p) (.active .two) T +
        (n - 3) * successCount (tripleStep p) (.active .one) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (tripleStep p) successWeight (tripleStep p .one e) T)).sum = _
  rw [triple_child_sum_one p hn (fun y => treeWeight (tripleStep p) successWeight y T)]
  simp [treeWeight_failure, successWeight, successCount]

theorem triple_two_succ {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (tripleStep p) (.active .two) (T + 1) =
      n ^ T + (n - 3) * successCount (tripleStep p) (.active .two) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (tripleStep p) successWeight (tripleStep p .two e) T)).sum = _
  rw [triple_child_sum_two p hn (fun y => treeWeight (tripleStep p) successWeight y T)]
  simp [treeWeight_success, treeWeight_failure, successWeight, successCount]

/-- From two hits the triple count is the single-stage count. -/
theorem triple_two_eq_stage {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (tripleStep p) (.active .two) T =
      successCount (stageStep p) (.active ()) T := by
  induction T with
  | zero => rfl
  | succ T ih => rw [triple_two_succ p hn T, stage_success_succ p hn T, ih]

/-- From one hit the triple count is the two-hit serial count. -/
theorem triple_one_eq_serial {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (tripleStep p) (.active .one) T =
      successCount (serialStep p) (.active false) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [triple_one_succ p hn T, serial_first_succ p hn T, ih, triple_two_eq_stage p hn T,
        serial_second_eq_stage p hn T]

/-- Concatenation: a serial prefix of length `u` followed by a stage of length `v`. -/
theorem triple_concatenation_lower_bound {n : Nat} (p : Ports n) (hn : 3 ≤ n) (u v : Nat) :
    successCount (serialStep p) (.active false) u * successCount (stageStep p) (.active ()) v ≤
      successCount (tripleStep p) (.active .zero) (u + v) := by
  induction u with
  | zero => simp [successCount, treeWeight, successWeight]
  | succ u ih =>
      calc
        successCount (serialStep p) (.active false) (u + 1) *
            successCount (stageStep p) (.active ()) v =
          (successCount (serialStep p) (.active true) u +
            (n - 3) * successCount (serialStep p) (.active false) u) *
            successCount (stageStep p) (.active ()) v := by
              rw [serial_first_succ p hn u]
        _ = successCount (stageStep p) (.active ()) u * successCount (stageStep p) (.active ()) v +
              (n - 3) * (successCount (serialStep p) (.active false) u *
                successCount (stageStep p) (.active ()) v) := by
              rw [serial_second_eq_stage p hn u, Nat.add_mul]
              ac_rfl
        _ ≤ successCount (serialStep p) (.active false) (u + v) +
              (n - 3) * successCount (tripleStep p) (.active .zero) (u + v) :=
          Nat.add_le_add (serial_concatenation_lower_bound p hn u v) (Nat.mul_le_mul_left (n - 3) ih)
        _ = successCount (tripleStep p) (.active .zero) ((u + 1) + v) := by
          rw [show (u + 1) + v = (u + v) + 1 by omega, triple_zero_succ p hn (u + v),
            triple_one_eq_serial p hn (u + v)]

/-- Three same-port hits within `6n` interactions have mass at least 1/64. -/
theorem triple_sixty_fourth {n : Nat} (p : Ports n) (hn : 3 ≤ n) :
    n ^ (6 * n) ≤ 64 * successCount (tripleStep p) (.active .zero) (6 * n) := by
  let s := successCount (stageStep p) (.active ()) (2 * n)
  let d := successCount (serialStep p) (.active false) (4 * n)
  have hstage : n ^ (2 * n) ≤ 4 * s := single_stage_quarter p hn
  have hserial : n ^ (4 * n) ≤ 16 * d := serial_sixteenth p hn
  have hcat : d * s ≤ successCount (tripleStep p) (.active .zero) (6 * n) := by
    have hh := triple_concatenation_lower_bound p hn (4 * n) (2 * n)
    simpa only [show 4 * n + 2 * n = 6 * n by omega] using hh
  calc
    n ^ (6 * n) = n ^ (4 * n) * n ^ (2 * n) := by
      rw [← Nat.pow_add, show 4 * n + 2 * n = 6 * n by omega]
    _ ≤ (16 * d) * (4 * s) := Nat.mul_le_mul hserial hstage
    _ = 64 * (d * s) := by ac_rfl
    _ ≤ 64 * successCount (tripleStep p) (.active .zero) (6 * n) := Nat.mul_le_mul_left 64 hcat

end B9SpliceTripleHitBridge
