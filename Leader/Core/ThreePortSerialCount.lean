import Leader.Core.FiniteUniformStoppingTree

set_option autoImplicit false

namespace ThreePortSerialCount

open FiniteUniformStoppingTree

/-!
Three fixed scheduler ports compete.  A successful two-stage word has A
as its first designated symbol and B as its second; both occurrences
consume real scheduler interactions.  The exact stopping-tree Bellman
calculation gives a quarter of the words within `2*n` for one stage, and
stopped-prefix composition gives a sixteenth within `4*n` for both.

The proofs below use the actual
project stopping-tree definitions and kernel-checked natural arithmetic.
-/

/-- Three distinct physical scheduler symbols, with no probability fields. -/
structure Ports (n : Nat) where
  a : Fin n
  b : Fin n
  c : Fin n
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c

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

/-- Exact sum with three distinct exceptional scheduler symbols. -/
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

/-- Exact concatenation of prefix and suffix scheduler trees. -/
theorem treeWeight_concat {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (w : StopNode S → Nat)
    (x : StopNode S) (u v : Nat) :
    treeWeight step w x (u + v) =
      treeWeight step (fun y => treeWeight step w y v) x u := by
  induction u generalizing x with
  | zero => simp only [Nat.zero_add, treeWeight]
  | succ u ih =>
      rw [show (u + 1) + v = (u + v) + 1 by omega]
      simp only [treeWeight]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))

/-- Append any suffix to a successful prefix; success is absorbing. -/
theorem success_padding {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (u v : Nat) :
    n ^ v * successCount step x u ≤ successCount step x (u + v) := by
  unfold successCount
  calc
    n ^ v * treeWeight step successWeight x u =
        treeWeight step (fun y => n ^ v * successWeight y) x u :=
      (treeWeight_mul_left step (n ^ v) successWeight x u).symm
    _ ≤ treeWeight step (fun y => treeWeight step successWeight y v) x u := by
      apply treeWeight_mono
      intro y
      cases y with
      | active s => simp [successWeight]
      | success => simp [treeWeight_success, successWeight]
      | failure => simp [successWeight]
    _ = treeWeight step successWeight x (u + v) :=
      (treeWeight_concat step successWeight x u v).symm

/-- One good port, two bad ports, and neutral self-loops. -/
def stageStep {n : Nat} (p : Ports n) (_ : Unit) (e : Fin n) :
    StopNode Unit :=
  if e = p.a then .success
  else if e = p.b then .failure
  else if e = p.c then .failure
  else .active ()

private theorem stage_child_sum {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Unit → Nat) :
    (List.ofFn (fun e : Fin n => w (stageStep p () e))).sum =
      w .success + w .failure + w .failure + (n - 3) * w (.active ()) := by
  have hs := sum_three p hn (fun e => w (stageStep p () e))
    (w (.active ())) (by
      intro e ha hb hc
      simp [stageStep, ha, hb, hc])
  simpa [stageStep, p.ab, p.ac, p.bc,
    p.ab.symm, p.ac.symm, p.bc.symm] using hs

private theorem stage_weight_succ {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Unit → Nat) (T : Nat) :
    treeWeight (stageStep p) w (.active ()) (T + 1) =
      n ^ T * w .success + n ^ T * w .failure + n ^ T * w .failure +
        (n - 3) * treeWeight (stageStep p) w (.active ()) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (stageStep p) w (stageStep p () e) T)).sum = _
  rw [stage_child_sum p hn (fun y => treeWeight (stageStep p) w y T)]
  simp only [treeWeight_success, treeWeight_failure]

theorem stage_success_succ {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (stageStep p) (.active ()) (T + 1) =
      n ^ T + (n - 3) * successCount (stageStep p) (.active ()) T := by
  simpa [successCount, successWeight] using
    stage_weight_succ p hn successWeight T

private theorem stage_failure_succ {n : Nat} (p : Ports n)
    (hn : 3 ≤ n) (T : Nat) :
    failureCount (stageStep p) (.active ()) (T + 1) =
      n ^ T + n ^ T + (n - 3) * failureCount (stageStep p) (.active ()) T := by
  simpa [failureCount, failureWeight] using
    stage_weight_succ p hn failureWeight T

/-- The two failure ports have exactly twice the good port's mass. -/
theorem stage_failure_twice {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    failureCount (stageStep p) (.active ()) T =
      2 * successCount (stageStep p) (.active ()) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [stage_failure_succ p hn T, stage_success_succ p hn T, ih,
        Nat.mul_add]
      have hx :
          (n - 3) * (2 * successCount (stageStep p) (.active ()) T) =
            2 * ((n - 3) * successCount (stageStep p) (.active ()) T) := by
        ac_rfl
      rw [hx]
      omega

/-- Each active interaction has exactly three terminal children. -/
private theorem stage_bellman {n : Nat} (p : Ports n) (hn : 3 ≤ n) :
    NatBellmanSuperSolution (stageStep p) 3
      (fun x => n * activeWeight x) := by
  refine ⟨by simp [activeWeight], by simp [activeWeight], ?_⟩
  intro s
  cases s
  have hs : (List.ofFn (fun e : Fin n => activeWeight (stageStep p () e))).sum =
      n - 3 := by
    simpa only [activeWeight, Nat.zero_add, Nat.mul_one] using
      stage_child_sum p hn activeWeight
  have hsplit : 3 + (n - 3) = n := by omega
  change 3 * n +
    (List.ofFn (fun e : Fin n => n * activeWeight (stageStep p () e))).sum ≤
      n * (n * 1)
  rw [Nat.mul_one, ofFn_sum_mul_left, hs,
    Nat.mul_comm 3 n, ← Nat.mul_add, hsplit]
  exact Nat.le_refl _

/-- A stronger division-free version of the requested one-stage bound. -/
theorem single_stage_scaled {n : Nat} (p : Ports n) (hn : 3 ≤ n) :
    5 * n ^ (2 * n) ≤
      18 * successCount (stageStep p) (.active ()) (2 * n) := by
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (stageStep p) 3 (fun x => n * activeWeight x)
    (stage_bellman p hn) (.active ()) (2 * n)
  have hcharge := horizon_mul_activeCount_le_truncatedActiveCostNumerator
    (stageStep p) (.active ()) (2 * n)
  have hscaled :
      n * (6 * activeCount (stageStep p) (.active ()) (2 * n)) ≤
        n * n ^ (2 * n) := by
    calc
      n * (6 * activeCount (stageStep p) (.active ()) (2 * n)) =
          3 * ((2 * n) * activeCount (stageStep p) (.active ()) (2 * n)) := by
        change n * ((3 * 2) * activeCount (stageStep p) (.active ()) (2 * n)) =
          3 * ((2 * n) * activeCount (stageStep p) (.active ()) (2 * n))
        ac_rfl
      _ ≤ 3 * truncatedActiveCostNumerator (stageStep p) (.active ()) (2 * n) :=
        Nat.mul_le_mul_left 3 hcharge
      _ ≤ n * n ^ (2 * n) := by
        simpa [activeWeight, Nat.mul_comm] using hcost
  have hmiss := Nat.le_of_mul_le_mul_left hscaled (show 0 < n by omega)
  have hparts := node_count_partition (stageStep p) (.active ()) (2 * n)
  rw [stage_failure_twice p hn (2 * n)] at hparts
  omega

/-- Within `2*n` interactions, at least one quarter of the scheduler words
have selected the good port before either competing port. -/
theorem single_stage_quarter {n : Nat} (p : Ports n) (hn : 3 ≤ n) :
    n ^ (2 * n) ≤ 4 * successCount (stageStep p) (.active ()) (2 * n) := by
  have h := single_stage_scaled p hn
  omega

/-- False: waiting for A. True: A occurred, now waiting for B.
The phase change consumes the A interaction; B is a later interaction. -/
def serialStep {n : Nat} (p : Ports n) : Bool → Fin n → StopNode Bool
  | false, e =>
      if e = p.a then .active true
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active false
  | true, e =>
      if e = p.b then .success
      else if e = p.a then .failure
      else if e = p.c then .failure
      else .active true

theorem serial_a_consumes_interaction {n : Nat} (p : Ports n) :
    serialStep p false p.a = .active true := by
  simp [serialStep]

theorem serial_b_finishes {n : Nat} (p : Ports n) :
    serialStep p true p.b = .success := by
  simp [serialStep]

private theorem serial_first_child_sum {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Bool → Nat) :
    (List.ofFn (fun e : Fin n => w (serialStep p false e))).sum =
      w (.active true) + w .failure + w .failure +
        (n - 3) * w (.active false) := by
  have hs := sum_three p hn (fun e => w (serialStep p false e))
    (w (.active false)) (by
      intro e ha hb hc
      simp [serialStep, ha, hb, hc])
  simpa [serialStep, p.ab, p.ac, p.bc,
    p.ab.symm, p.ac.symm, p.bc.symm] using hs

private theorem serial_second_child_sum {n : Nat} (p : Ports n) (hn : 3 ≤ n)
    (w : StopNode Bool → Nat) :
    (List.ofFn (fun e : Fin n => w (serialStep p true e))).sum =
      w .failure + w .success + w .failure +
        (n - 3) * w (.active true) := by
  have hs := sum_three p hn (fun e => w (serialStep p true e))
    (w (.active true)) (by
      intro e ha hb hc
      simp [serialStep, ha, hb, hc])
  simpa [serialStep, p.ab, p.ac, p.bc,
    p.ab.symm, p.ac.symm, p.bc.symm] using hs

theorem serial_first_succ {n : Nat} (p : Ports n) (hn : 3 ≤ n) (T : Nat) :
    successCount (serialStep p) (.active false) (T + 1) =
      successCount (serialStep p) (.active true) T +
        (n - 3) * successCount (serialStep p) (.active false) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (serialStep p) successWeight (serialStep p false e) T)).sum = _
  rw [serial_first_child_sum p hn
    (fun y => treeWeight (serialStep p) successWeight y T)]
  simp [treeWeight_failure, successWeight, successCount]

private theorem serial_second_succ {n : Nat} (p : Ports n)
    (hn : 3 ≤ n) (T : Nat) :
    successCount (serialStep p) (.active true) (T + 1) =
      n ^ T + (n - 3) * successCount (serialStep p) (.active true) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (serialStep p) successWeight (serialStep p true e) T)).sum = _
  rw [serial_second_child_sum p hn
    (fun y => treeWeight (serialStep p) successWeight y T)]
  simp [treeWeight_success, treeWeight_failure, successWeight, successCount]

/-- The single-stage count is independent of which distinct port is good. -/
theorem serial_second_eq_stage {n : Nat} (p : Ports n)
    (hn : 3 ≤ n) (T : Nat) :
    successCount (serialStep p) (.active true) T =
      successCount (stageStep p) (.active ()) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [serial_second_succ p hn T, stage_success_succ p hn T, ih]

theorem serial_one_step_zero {n : Nat} (p : Ports n) (hn : 3 ≤ n) :
    successCount (serialStep p) (.active false) 1 = 0 := by
  calc
    successCount (serialStep p) (.active false) 1 =
        successCount (serialStep p) (.active true) 0 +
          (n - 3) * successCount (serialStep p) (.active false) 0 :=
      serial_first_succ p hn 0
    _ = 0 := rfl

/-- Stopped-prefix concatenation, not multiplication of fixed-half events. -/
theorem serial_concatenation_lower_bound {n : Nat}
    (p : Ports n) (hn : 3 ≤ n) (u v : Nat) :
    successCount (stageStep p) (.active ()) u *
        successCount (stageStep p) (.active ()) v ≤
      successCount (serialStep p) (.active false) (u + v) := by
  induction u with
  | zero => simp [successCount, treeWeight, successWeight]
  | succ u ih =>
      have hpad :
          n ^ u * successCount (stageStep p) (.active ()) v ≤
            successCount (stageStep p) (.active ()) (u + v) := by
        simpa only [Nat.add_comm] using
          success_padding (stageStep p) (.active ()) v u
      calc
        successCount (stageStep p) (.active ()) (u + 1) *
            successCount (stageStep p) (.active ()) v =
          (n ^ u + (n - 3) * successCount (stageStep p) (.active ()) u) *
            successCount (stageStep p) (.active ()) v := by
              rw [stage_success_succ p hn u]
        _ = n ^ u * successCount (stageStep p) (.active ()) v +
              (n - 3) * (successCount (stageStep p) (.active ()) u *
                successCount (stageStep p) (.active ()) v) := by
              rw [Nat.add_mul]
              ac_rfl
        _ ≤ successCount (stageStep p) (.active ()) (u + v) +
              (n - 3) * successCount (serialStep p) (.active false) (u + v) :=
          Nat.add_le_add hpad (Nat.mul_le_mul_left (n - 3) ih)
        _ = successCount (serialStep p) (.active false) ((u + 1) + v) := by
          rw [show (u + 1) + v = (u + v) + 1 by omega,
            serial_first_succ p hn (u + v), serial_second_eq_stage p hn (u + v)]

/-- Two consecutive stage budgets preserve the constant success mass; the
second budget starts at the actual first-stage stopping time. -/
theorem serial_sixteenth {n : Nat} (p : Ports n) (hn : 3 ≤ n) :
    n ^ (4 * n) ≤
      16 * successCount (serialStep p) (.active false) (4 * n) := by
  let s := successCount (stageStep p) (.active ()) (2 * n)
  have hstage : n ^ (2 * n) ≤ 4 * s := single_stage_quarter p hn
  have hserial : s * s ≤
      successCount (serialStep p) (.active false) (4 * n) := by
    have hh := serial_concatenation_lower_bound p hn (2 * n) (2 * n)
    simpa only [show 2 * n + 2 * n = 4 * n by omega] using hh
  calc
    n ^ (4 * n) = n ^ (2 * n) * n ^ (2 * n) := by
      rw [← Nat.pow_add, show 2 * n + 2 * n = 4 * n by omega]
    _ ≤ (4 * s) * (4 * s) := Nat.mul_le_mul hstage hstage
    _ = 16 * (s * s) := by
      change (4 * s) * (4 * s) = (4 * 4) * (s * s)
      ac_rfl
    _ ≤ 16 * successCount (serialStep p) (.active false) (4 * n) :=
      Nat.mul_le_mul_left 16 hserial

/-- Entry point with exactly the physical triple's geometric hypotheses. -/
theorem physical_serial_sixteenth {n : Nat} (hn : 3 ≤ n)
    (A B C : Fin n) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    n ^ (4 * n) ≤ 16 * successCount
      (serialStep ⟨A, B, C, hAB, hAC, hBC⟩) (.active false) (4 * n) :=
  serial_sixteenth ⟨A, B, C, hAB, hAC, hBC⟩ hn

#print axioms ThreePortSerialCount.single_stage_scaled
#print axioms ThreePortSerialCount.single_stage_quarter
#print axioms ThreePortSerialCount.serial_concatenation_lower_bound
#print axioms ThreePortSerialCount.physical_serial_sixteenth

end ThreePortSerialCount
