import Leader.Wu.Safety.CorrectedFormulation

namespace PPLLFinalMissTreeAmplification

open PPLLResearchFormulation

set_option autoImplicit false

/-- Exact endpoint-failure numerator over the full directed-edge action tree. -/
noncomputable def finalMissTree {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (Safe : (Fin n -> Q) -> Prop) : (Fin n -> Q) -> Nat -> Nat
  | C, 0 => @ite Nat (Safe C) (Classical.propDecidable _) 0 1
  | C, t + 1 =>
      (List.ofFn (fun e => finalMissTree ring T Safe
        (localStep ring T C e) t)).sum

private theorem sum_ofFn_le {n : Nat}
    (f g : Fin n -> Nat) (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_eq {n : Nat}
    (f g : Fin n -> Nat) (hfg : forall i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  exact Nat.le_antisymm
    (sum_ofFn_le f g (fun i => Nat.le_of_eq (hfg i)))
    (sum_ofFn_le g f (fun i => Nat.le_of_eq (hfg i).symm))

private theorem sum_ofFn_const_zero (n : Nat) :
    (List.ofFn (fun _ : Fin n => 0)).sum = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]

private theorem sum_ofFn_mul_left {n : Nat}
    (a : Nat) (f : Fin n -> Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]

private theorem sum_ofFn_mul_right {n : Nat}
    (f : Fin n -> Nat) (a : Nat) :
    (List.ofFn (fun i => f i * a)).sum =
      (List.ofFn f).sum * a := by
  simpa [Nat.mul_comm] using sum_ofFn_mul_left a f

/-- Exact local closure for an endpoint predicate. -/
def LocalStepClosed {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (Safe : (Fin n -> Q) -> Prop) : Prop :=
  forall C, Safe C -> forall e, Safe (localStep ring T C e)

/-- Definition-1 safety supplies the local closure premise for every protocol. -/
theorem isSafe_localStepClosed (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y -> Bool) :
    LocalStepClosed ring P.transition
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) := by
  intro C hC e
  apply isSafe_closed P ring isLeader C hC
  exact ⟨e, localStep_eq_protocol_step P ring C e⟩

/-- An absorbing endpoint predicate has no later failing leaves. -/
theorem finalMissTree_zero_of_safe {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (Safe : (Fin n -> Q) -> Prop)
    (hclosed : LocalStepClosed ring T Safe)
    (C : Fin n -> Q) (hC : Safe C) (t : Nat) :
    finalMissTree ring T Safe C t = 0 := by
  induction t generalizing C with
  | zero => simp [finalMissTree, hC]
  | succ t ih =>
      rw [finalMissTree]
      have hzero :
          (List.ofFn (fun e => finalMissTree ring T Safe
            (localStep ring T C e) t)).sum =
          (List.ofFn (fun _ : Fin n => 0)).sum := by
        apply sum_ofFn_eq
        intro e
        exact ih _ (hclosed C hC e)
      rw [hzero, sum_ofFn_const_zero]

/-- A uniform scaled suffix bound multiplies through an arbitrary prefix. -/
theorem finalMissTree_add_scaled_le {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (Safe : (Fin n -> Q) -> Prop)
    (hclosed : LocalStepClosed ring T Safe)
    (a b q : Nat)
    (hblock : forall C : Fin n -> Q,
      q * finalMissTree ring T Safe C b <= n ^ b) :
    forall C : Fin n -> Q,
      q * finalMissTree ring T Safe C (a + b) <=
        finalMissTree ring T Safe C a * n ^ b := by
  intro C
  induction a generalizing C with
  | zero =>
      simp only [Nat.zero_add]
      by_cases hC : Safe C
      · rw [finalMissTree_zero_of_safe ring T Safe hclosed C hC b]
        simp [finalMissTree, hC]
      · simpa [finalMissTree, hC] using hblock C
  | succ a ih =>
      rw [Nat.succ_add, finalMissTree, finalMissTree]
      rw [← sum_ofFn_mul_left, ← sum_ofFn_mul_right]
      exact sum_ofFn_le _ _ (fun e => ih (localStep ring T C e))

/-- Pure-integer repeated-block amplification for endpoint failures. -/
theorem finalMissTree_repeatedBlock_scaled_le {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (Safe : (Fin n -> Q) -> Prop)
    (hclosed : LocalStepClosed ring T Safe)
    (q t : Nat)
    (hblock : forall C : Fin n -> Q,
      q * finalMissTree ring T Safe C t <= n ^ t) :
    forall k C,
      q ^ k * finalMissTree ring T Safe C (k * t) <= n ^ (k * t) := by
  intro k
  induction k with
  | zero =>
      intro C
      by_cases hC : Safe C <;> simp [finalMissTree, hC]
  | succ k ih =>
      intro C
      have hadd := finalMissTree_add_scaled_le
        ring T Safe hclosed (k * t) t q hblock C
      have hscaled := Nat.mul_le_mul_left (q ^ k) hadd
      have htail := Nat.mul_le_mul_right (n ^ t) (ih C)
      calc
        q ^ (k + 1) * finalMissTree ring T Safe C ((k + 1) * t) =
            q ^ k * (q * finalMissTree ring T Safe C (k * t + t)) := by
              rw [Nat.pow_succ, Nat.succ_mul]
              ac_rfl
        _ <= q ^ k *
            (finalMissTree ring T Safe C (k * t) * n ^ t) := hscaled
        _ = (q ^ k * finalMissTree ring T Safe C (k * t)) * n ^ t := by
              ac_rfl
        _ <= n ^ (k * t) * n ^ t := htail
        _ = n ^ ((k + 1) * t) := by
              rw [← Nat.pow_add, Nat.succ_mul]

/-- Eight-way block amplification at `log2 n + 1` blocks is at most `1/n`. -/
theorem finalMissTree_oneOverN_at_log2Blocks {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (Safe : (Fin n -> Q) -> Prop)
    (hclosed : LocalStepClosed ring T Safe)
    (t : Nat)
    (hblock : forall C : Fin n -> Q,
      8 * finalMissTree ring T Safe C t <= n ^ t) :
    let k := n.log2 + 1
    forall C : Fin n -> Q,
      n * finalMissTree ring T Safe C (k * t) <= n ^ (k * t) := by
  let k := n.log2 + 1
  dsimp only
  have hrepeat := finalMissTree_repeatedBlock_scaled_le
    ring T Safe hclosed 8 t hblock k
  have hn2pow : n < 2 ^ k := by
    simpa [k] using (Nat.lt_log2_self (n := n))
  have hpow : 2 ^ k <= 8 ^ k :=
    Nat.pow_le_pow_left (by omega) k
  have hn8 : n <= 8 ^ k := Nat.le_trans (Nat.le_of_lt hn2pow) hpow
  intro C
  exact Nat.le_trans (Nat.mul_le_mul_right
      (finalMissTree ring T Safe C (k * t)) hn8)
    (hrepeat C)


end PPLLFinalMissTreeAmplification
