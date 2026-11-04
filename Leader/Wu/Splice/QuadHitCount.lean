import Leader.Wu.Splice.TripleHitCount

set_option autoImplicit false

/-! # Four same-port hits before either bad port: success mass at least 1/256 over 8n

`quadStep p` counts hits of the good port `p.a` and fails at either bad port.  From one hit its success count is
the three-hit count of `B9SpliceTripleHitBridge.tripleStep` (`quad_one_eq_triple`); a single stage of `2n` letters
followed by a three-hit window of `6n` letters is a lower bound (`quad_concatenation_lower_bound`), hence
`n^(8n) ≤ 256 * successCount (quadStep p) zero (8n)` (`quad_two_fifty_sixth`). -/

namespace B9SpliceQuadHitCount

open FiniteUniformStoppingTree ThreePortSerialCount B9SpliceTripleHitBridge

variable {n : Nat}

/-- Number of good-port hits so far. -/
inductive Hits4 where
  | zero | one | two | three
  deriving DecidableEq, Repr

def quadStep {n : Nat} (p : Ports n) : Hits4 → Fin n → StopNode Hits4
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
      if e = p.a then .active .three
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active .two
  | .three, e =>
      if e = p.a then .success
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active .three

/-! ## Local copies of the private counting helpers -/

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

private theorem quad_child_sum (p : Ports n) (hn : 3 ≤ n) (s : Hits4) (next : StopNode Hits4)
    (hnext : quadStep p s p.a = next)
    (w : StopNode Hits4 → Nat) :
    (List.ofFn (fun e : Fin n => w (quadStep p s e))).sum =
      w next + w .failure + w .failure + (n - 3) * w (.active s) := by
  have hs := sum_three p hn (fun e => w (quadStep p s e)) (w (.active s)) (by
    intro e ha hb hc
    cases s <;> simp [quadStep, ha, hb, hc])
  rw [hs, hnext]
  have hb : quadStep p s p.b = .failure := by cases s <;> simp [quadStep, p.ab.symm]
  have hc : quadStep p s p.c = .failure := by cases s <;> simp [quadStep, p.ac.symm, p.bc.symm]
  rw [hb, hc]

theorem quad_succ (p : Ports n) (hn : 3 ≤ n) (s : Hits4) (next : StopNode Hits4)
    (hnext : quadStep p s p.a = next) (T : Nat) :
    successCount (quadStep p) (.active s) (T + 1) =
      treeWeight (quadStep p) successWeight next T +
        (n - 3) * successCount (quadStep p) (.active s) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (quadStep p) successWeight (quadStep p s e) T)).sum = _
  rw [quad_child_sum p hn s next hnext (fun y => treeWeight (quadStep p) successWeight y T)]
  simp [treeWeight_failure, successWeight, successCount]

theorem quad_three_eq_stage (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (quadStep p) (.active .three) T = successCount (stageStep p) (.active ()) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [quad_succ p hn .three .success (by simp [quadStep]) T, stage_success_succ p hn T, ih]
      simp [treeWeight_success, successWeight]

theorem quad_two_eq_triple (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (quadStep p) (.active .two) T = successCount (tripleStep p) (.active .one) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [quad_succ p hn .two (.active .three) (by simp [quadStep]) T, triple_one_succ p hn T, ih]
      change successCount (quadStep p) (.active .three) T + _ = _
      rw [quad_three_eq_stage p hn T, triple_two_eq_stage p hn T]

theorem quad_one_eq_triple (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (quadStep p) (.active .one) T = successCount (tripleStep p) (.active .zero) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [quad_succ p hn .one (.active .two) (by simp [quadStep]) T, triple_zero_succ p hn T, ih]
      change successCount (quadStep p) (.active .two) T + _ = _
      rw [quad_two_eq_triple p hn T]

theorem quad_zero_succ (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (quadStep p) (.active .zero) (T + 1) =
      successCount (tripleStep p) (.active .zero) T + (n - 3) * successCount (quadStep p) (.active .zero) T := by
  rw [quad_succ p hn .zero (.active .one) (by simp [quadStep]) T]
  change successCount (quadStep p) (.active .one) T + _ = _
  rw [quad_one_eq_triple p hn T]

/-- A single stage of `u` letters followed by a three-hit window of `v` letters. -/
theorem quad_concatenation_lower_bound (p : Ports n) (hn : 3 ≤ n) (u v : Nat) :
    successCount (stageStep p) (.active ()) u * successCount (tripleStep p) (.active .zero) v ≤
      successCount (quadStep p) (.active .zero) (u + v) := by
  induction u with
  | zero => simp [successCount, treeWeight, successWeight]
  | succ u ih =>
      have hpad : n ^ u * successCount (tripleStep p) (.active .zero) v ≤
          successCount (tripleStep p) (.active .zero) (u + v) := by
        simpa only [Nat.add_comm] using success_padding (tripleStep p) (.active .zero) v u
      calc
        successCount (stageStep p) (.active ()) (u + 1) * successCount (tripleStep p) (.active .zero) v =
          (n ^ u + (n - 3) * successCount (stageStep p) (.active ()) u) *
            successCount (tripleStep p) (.active .zero) v := by rw [stage_success_succ p hn u]
        _ = n ^ u * successCount (tripleStep p) (.active .zero) v +
              (n - 3) * (successCount (stageStep p) (.active ()) u *
                successCount (tripleStep p) (.active .zero) v) := by
              rw [Nat.add_mul]; ac_rfl
        _ ≤ successCount (tripleStep p) (.active .zero) (u + v) +
              (n - 3) * successCount (quadStep p) (.active .zero) (u + v) :=
          Nat.add_le_add hpad (Nat.mul_le_mul_left (n - 3) ih)
        _ = successCount (quadStep p) (.active .zero) ((u + 1) + v) := by
          rw [show (u + 1) + v = (u + v) + 1 by omega, quad_zero_succ p hn (u + v)]

/-- Four same-port hits within `8n` interactions have mass at least 1/256. -/
theorem quad_two_fifty_sixth (p : Ports n) (hn : 3 ≤ n) :
    n ^ (8 * n) ≤ 256 * successCount (quadStep p) (.active .zero) (8 * n) := by
  let s := successCount (stageStep p) (.active ()) (2 * n)
  let t := successCount (tripleStep p) (.active .zero) (6 * n)
  have hstage : n ^ (2 * n) ≤ 4 * s := single_stage_quarter p hn
  have htriple : n ^ (6 * n) ≤ 64 * t := triple_sixty_fourth p hn
  have hcat : s * t ≤ successCount (quadStep p) (.active .zero) (8 * n) := by
    have hh := quad_concatenation_lower_bound p hn (2 * n) (6 * n)
    simpa only [show 2 * n + 6 * n = 8 * n by omega] using hh
  calc
    n ^ (8 * n) = n ^ (2 * n) * n ^ (6 * n) := by
      rw [← Nat.pow_add, show 2 * n + 6 * n = 8 * n by omega]
    _ ≤ (4 * s) * (64 * t) := Nat.mul_le_mul hstage htriple
    _ = 256 * (s * t) := by ac_rfl
    _ ≤ 256 * successCount (quadStep p) (.active .zero) (8 * n) := Nat.mul_le_mul_left 256 hcat

end B9SpliceQuadHitCount
