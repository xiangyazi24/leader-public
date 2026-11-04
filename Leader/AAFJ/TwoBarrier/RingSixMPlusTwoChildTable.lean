import Leader.AAFJ.TwoBarrier.ColoredEndpointTerminals
import Leader.AAFJ.LeastNonDivisor

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.N6m2ColoredChildTable

open BarrierAlgebra
open PersistentBarrierService
open TwoEndpointServiceClock
open TwoEndpointColoredClock

instance instDecidablePreContact {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n) :
    Decidable (PreContact hk ring C b) := by
  unfold PreContact
  infer_instance

instance instDecidableContactAt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n) :
    Decidable (ContactAt hk ring C b) := by
  unfold ContactAt
  infer_instance

def N (m : Nat) : Nat := 6 * m + 2

def ring (m : Nat) : DirectedRing (N m) := ⟨by simp [N]⟩

private theorem hn3 {m : Nat} (hm : 1 ≤ m) : 2 < N m := by
  simp [N]
  omega

private theorem hk3 : 0 < 3 := by decide

def v (m a : Nat) (ha : a < N m) : Fin (N m) := ⟨a, ha⟩

def v0 (m : Nat) : Fin (N m) := v m 0 (by simp [N])
def v1 (m : Nat) : Fin (N m) := v m 1 (by simp [N])
def v2 (m : Nat) (hm : 1 ≤ m) : Fin (N m) := v m 2 (by simp [N]; omega)
def v3 (m : Nat) (hm : 1 ≤ m) : Fin (N m) := v m 3 (by simp [N]; omega)
def v4 (m : Nat) (hm : 1 ≤ m) : Fin (N m) := v m 4 (by simp [N]; omega)
def v5 (m : Nat) (hm : 1 ≤ m) : Fin (N m) := v m 5 (by simp [N]; omega)

def labelNat (i : Nat) : Nat :=
  if i = 0 then 0 else if i ≤ 3 then i - 1 else i + 1

def lab {m : Nat} (i : Fin (N m)) : Fin 3 :=
  ⟨labelNat i.val % 3, Nat.mod_lt _ (by decide)⟩

def base (l : Fin 3) (p h : Bool) : State 3 :=
  { bullet := false, leader := false, label := l, probe := p, phase := h }

def X0 {m : Nat} (_hm : 1 ≤ m) (i : Fin (N m)) : State 3 :=
  base (lab i) false (decide (i.val = 3))

def X1 {m : Nat} (_hm : 1 ≤ m) (i : Fin (N m)) : State 3 :=
  base (lab i) (decide (i.val = 1)) (decide (i.val = 0 ∨ i.val = 3))

def X2 {m : Nat} (_hm : 1 ≤ m) (i : Fin (N m)) : State 3 :=
  base (lab i) (decide (i.val = 2)) (decide (i.val = 0 ∨ i.val = 3))

def X3 {m : Nat} (_hm : 1 ≤ m) (i : Fin (N m)) : State 3 :=
  base (lab i) (decide (i.val = 3)) (decide (i.val = 0 ∨ i.val = 3))

private theorem rightNeighbor_val {m : Nat} (e : Fin (N m)) :
    ((ring m).rightNeighbor e).val = (e.val + 1) % N m := rfl

private theorem lab_barrier_iff
    {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔
      e.val = 0 ∨ e.val = 3 := by
  have hfin :
      (succLabel hk3 (lab e) = lab ((ring m).rightNeighbor e)) ↔
        ((labelNat e.val % 3 + 1) % 3 =
          labelNat ((e.val + 1) % N m) % 3) := by
    rw [Fin.ext_iff]
    rfl
  have hnum : ((labelNat e.val % 3 + 1) % 3 ≠
      labelNat ((e.val + 1) % N m) % 3) ↔ e.val = 0 ∨ e.val = 3 := by
    by_cases hnext : e.val + 1 < N m
    · rw [Nat.mod_eq_of_lt hnext]
      by_cases h0 : e.val = 0
      · simp [labelNat, h0]
      by_cases h1 : e.val = 1
      · simp [labelNat, h1]
      by_cases h2 : e.val = 2
      · simp [labelNat, h2]
      by_cases h3 : e.val = 3
      · simp [labelNat, h3]
      have h4 : 4 ≤ e.val := by omega
      rw [labelNat, if_neg h0, if_neg (by omega : ¬ e.val ≤ 3)]
      rw [labelNat, if_neg (by omega : e.val + 1 ≠ 0),
        if_neg (by omega : ¬ e.val + 1 ≤ 3)]
      simp only [Nat.add_mod, Nat.one_mod, Nat.mod_mod]
      simp [h3, Nat.add_assoc]
      exact h0
    · have heq : e.val + 1 = N m := by omega
      have heval : e.val = 6 * m + 1 := by simp [N] at heq; omega
      rw [heq, Nat.mod_self, heval]
      have hm6 : 6 ≤ 6 * m := by omega
      rw [labelNat, if_neg (by omega : 6 * m + 1 ≠ 0),
        if_neg (by omega : ¬ 6 * m + 1 ≤ 3)]
      simp [labelNat, Nat.add_mod, Nat.mul_mod]
      omega
  constructor
  · intro h
    exact hnum.mp (fun hn => h (hfin.mpr hn))
  · intro hp heq
    exact hnum.mpr hp (hfin.mp heq)

theorem X0_barrier_iff {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (X0 hm)) e ↔
      e.val = 0 ∨ e.val = 3 := by
  rw [barrierAt_labelsOf_iff]
  change succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔ _
  exact lab_barrier_iff hm e

theorem X1_barrier_iff {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (X1 hm)) e ↔
      e.val = 0 ∨ e.val = 3 := by
  rw [barrierAt_labelsOf_iff]
  change succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔ _
  exact lab_barrier_iff hm e

theorem X2_barrier_iff {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (X2 hm)) e ↔
      e.val = 0 ∨ e.val = 3 := by
  rw [barrierAt_labelsOf_iff]
  change succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔ _
  exact lab_barrier_iff hm e

theorem X3_barrier_iff {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (X3 hm)) e ↔
      e.val = 0 ∨ e.val = 3 := by
  rw [barrierAt_labelsOf_iff]
  change succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔ _
  exact lab_barrier_iff hm e

private theorem rn_v0 {m : Nat} :
    (ring m).rightNeighbor (v0 m) = v1 m := by
  apply Fin.ext
  simp [ring, v0, v1, v, N, DirectedRing.rightNeighbor]

private theorem rn_v1 {m : Nat} (hm : 1 ≤ m) :
    (ring m).rightNeighbor (v1 m) = v2 m hm := by
  apply Fin.ext
  simp [ring, v1, v2, v, N, DirectedRing.rightNeighbor] <;> omega

private theorem rn_v2 {m : Nat} (hm : 1 ≤ m) :
    (ring m).rightNeighbor (v2 m hm) = v3 m hm := by
  apply Fin.ext
  simp [ring, v2, v3, v, N, DirectedRing.rightNeighbor] <;> omega

private theorem rn_v3 {m : Nat} (hm : 1 ≤ m) :
    (ring m).rightNeighbor (v3 m hm) = v4 m hm := by
  apply Fin.ext
  simp [ring, v3, v4, v, N, DirectedRing.rightNeighbor] <;> omega

private theorem rn_v4 {m : Nat} (hm : 1 ≤ m) :
    (ring m).rightNeighbor (v4 m hm) = v5 m hm := by
  apply Fin.ext
  simp [ring, v4, v5, v, N, DirectedRing.rightNeighbor] <;> omega

def vlast (m : Nat) : Fin (N m) :=
  ⟨N m - 1, by simp [N]⟩

private theorem rn_vlast {m : Nat} :
    (ring m).rightNeighbor (vlast m) = v0 m := by
  apply Fin.ext
  simp [ring, vlast, v0, v, N, DirectedRing.rightNeighbor]

private theorem preContact_of_barrier_iff
    {m : Nat} (hm : 1 ≤ m) (C : Fin (N m) → State 3)
    (hbar : ∀ e, BarrierAt hk3 (ring m) (labelsOf C) e ↔
      e.val = 0 ∨ e.val = 3) :
    PreContact hk3 (ring m) C (v0 m) ∧
      PreContact hk3 (ring m) C (v3 m hm) := by
  constructor
  · refine ⟨(hbar (v0 m)).2 (Or.inl rfl), ?_, ?_⟩
    · rw [rn_v0, hbar]
      simp [v1, v]
    · intro e he
      have helast : e = vlast m :=
        rightNeighbor_injective (ring m) (he.trans rn_vlast.symm)
      rw [helast, hbar]
      simp [vlast, N]
      omega
  · refine ⟨(hbar (v3 m hm)).2 (Or.inr rfl), ?_, ?_⟩
    · rw [rn_v3 hm, hbar]
      simp [v4, v]
    · intro e he
      have hev2 : e = v2 m hm :=
        rightNeighbor_injective (ring m) (he.trans (rn_v2 hm).symm)
      rw [hev2, hbar]
      simp [v2, v]

theorem X0_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (X0 hm) (v0 m) ∧
      PreContact hk3 (ring m) (X0 hm) (v3 m hm) :=
  preContact_of_barrier_iff hm (X0 hm) (X0_barrier_iff hm)

theorem X1_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (X1 hm) (v0 m) ∧
      PreContact hk3 (ring m) (X1 hm) (v3 m hm) :=
  preContact_of_barrier_iff hm (X1 hm) (X1_barrier_iff hm)

theorem X2_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (X2 hm) (v0 m) ∧
      PreContact hk3 (ring m) (X2 hm) (v3 m hm) :=
  preContact_of_barrier_iff hm (X2 hm) (X2_barrier_iff hm)

theorem X3_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (X3 hm) (v0 m) ∧
      PreContact hk3 (ring m) (X3 hm) (v3 m hm) :=
  preContact_of_barrier_iff hm (X3 hm) (X3_barrier_iff hm)

private theorem trans_X0_zero {m : Nat} (hm : 1 ≤ m) :
    transition hk3 (X0 hm (v0 m)) (X0 hm ((ring m).rightNeighbor (v0 m))) =
      (X1 hm (v0 m), X1 hm (v1 m)) := by
  rw [rn_v0]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    X0, X1, base, v0, v1, v, lab, labelNat, succLabel]

private theorem trans_X1_one {m : Nat} (hm : 1 ≤ m) :
    transition hk3 (X1 hm (v1 m)) (X1 hm ((ring m).rightNeighbor (v1 m))) =
      (X2 hm (v1 m), X2 hm (v2 m hm)) := by
  rw [rn_v1 hm]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    X1, X2, base, v0, v1, v2, v3, v, lab, labelNat, succLabel]

private theorem trans_X2_two {m : Nat} (hm : 1 ≤ m) :
    transition hk3 (X2 hm (v2 m hm)) (X2 hm ((ring m).rightNeighbor (v2 m hm))) =
      (X3 hm (v2 m hm), X3 hm (v3 m hm)) := by
  rw [rn_v2 hm]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    X2, X3, base, v0, v2, v3, v, lab, labelNat, succLabel]

theorem raw_X0_zero {m : Nat} (hm : 1 ≤ m) :
    (protocol 3 hk3).step (ring m) (X0 hm) (v0 m) = X1 hm := by
  funext i
  simp only [PopulationProtocol.step, protocol, trans_X0_zero hm]
  rw [rn_v0]
  by_cases hi0 : i = v0 m
  · subst i; simp [X1]
  by_cases hi1 : i = v1 m
  · subst i; simp [X1, v0, v1, v, Fin.ext_iff] <;> omega
  have hi0v : i.val ≠ 0 := by
    intro h; apply hi0; apply Fin.ext; simpa [v0, v] using h
  have hi1v : i.val ≠ 1 := by
    intro h; apply hi1; apply Fin.ext; simpa [v1, v] using h
  simp [hi0, hi1, hi0v, hi1v, X0, X1]

theorem raw_X1_one {m : Nat} (hm : 1 ≤ m) :
    (protocol 3 hk3).step (ring m) (X1 hm) (v1 m) = X2 hm := by
  funext i
  simp only [PopulationProtocol.step, protocol, trans_X1_one hm]
  rw [rn_v1 hm]
  by_cases hi1 : i = v1 m
  · subst i; simp [X2, v1, v2, v]
  by_cases hi2 : i = v2 m hm
  · subst i; simp [X2, v1, v2, v, Fin.ext_iff] <;> omega
  have hi1v : i.val ≠ 1 := by
    intro h; apply hi1; apply Fin.ext; simpa [v1, v] using h
  have hi2v : i.val ≠ 2 := by
    intro h; apply hi2; apply Fin.ext; simpa [v2, v] using h
  simp [hi1, hi2, hi1v, hi2v, X1, X2]

theorem raw_X2_two {m : Nat} (hm : 1 ≤ m) :
    (protocol 3 hk3).step (ring m) (X2 hm) (v2 m hm) = X3 hm := by
  funext i
  simp only [PopulationProtocol.step, protocol, trans_X2_two hm]
  rw [rn_v2 hm]
  by_cases hi2 : i = v2 m hm
  · subst i; simp [X3, v2, v3, v]
  by_cases hi3 : i = v3 m hm
  · subst i; simp [X3, v2, v3, v, Fin.ext_iff] <;> omega
  have hi2v : i.val ≠ 2 := by
    intro h; apply hi2; apply Fin.ext; simpa [v2, v] using h
  have hi3v : i.val ≠ 3 := by
    intro h; apply hi3; apply Fin.ext; simpa [v3, v] using h
  simp [hi2, hi3, hi2v, hi3v, X2, X3]

private theorem raw_step_eq_self_of_transition
    {m : Nat} (C : Fin (N m) → State 3) (e : Fin (N m))
    (htrans : transition hk3 (C e) (C ((ring m).rightNeighbor e)) =
      (C e, C ((ring m).rightNeighbor e))) :
    (protocol 3 hk3).step (ring m) C e = C := by
  funext i
  simp only [PopulationProtocol.step, protocol, htrans]
  by_cases hie : i = e
  · simp [hie]
  by_cases hir : i = (ring m).rightNeighbor e
  · subst i
    simp [rightNeighbor_ne_self (ring m) (by simp [N]) e]
  simp [hie, hir]

theorem raw_X0_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h3 : e ≠ v3 m hm) :
    (protocol 3 hk3).step (ring m) (X0 hm) e = X0 hm := by
  apply raw_step_eq_self_of_transition
  have he0 : e.val ≠ 0 := by
    intro h; apply h0; apply Fin.ext; simpa [v0, v] using h
  have he3 : e.val ≠ 3 := by
    intro h; apply h3; apply Fin.ext; simpa [v3, v] using h
  have hnb : ¬ IsBarrier hk3 (X0 hm e)
      (X0 hm ((ring m).rightNeighbor e)) := by
    intro h
    have hb : BarrierAt hk3 (ring m) (labelsOf (X0 hm)) e :=
      (barrierAt_labelsOf_iff hk3 (ring m) (X0 hm) e).2 h
    exact ((X0_barrier_iff hm e).1 hb).elim he0 he3
  rw [transition_of_nonbarrier hk3 _ _ hnb]
  simp [nonBarrierStep, X0, base]

theorem raw_X1_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h1 : e ≠ v1 m) (h3 : e ≠ v3 m hm) :
    (protocol 3 hk3).step (ring m) (X1 hm) e = X1 hm := by
  apply raw_step_eq_self_of_transition
  by_cases h0 : e = v0 m
  · subst e
    rw [rn_v0]
    simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
      X1, base, v0, v1, v3, v, lab, labelNat, succLabel]
  · have he0 : e.val ≠ 0 := by
      intro h; apply h0; apply Fin.ext; simpa [v0, v] using h
    have he1 : e.val ≠ 1 := by
      intro h; apply h1; apply Fin.ext; simpa [v1, v] using h
    have he3 : e.val ≠ 3 := by
      intro h; apply h3; apply Fin.ext; simpa [v3, v] using h
    have hnb : ¬ IsBarrier hk3 (X1 hm e)
        (X1 hm ((ring m).rightNeighbor e)) := by
      intro h
      have hb : BarrierAt hk3 (ring m) (labelsOf (X1 hm)) e :=
        (barrierAt_labelsOf_iff hk3 (ring m) (X1 hm) e).2 h
      exact ((X1_barrier_iff hm e).1 hb).elim he0 he3
    rw [transition_of_nonbarrier hk3 _ _ hnb]
    simp [nonBarrierStep, X1, base, he1]

theorem raw_X2_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h2 : e ≠ v2 m hm) (h3 : e ≠ v3 m hm) :
    (protocol 3 hk3).step (ring m) (X2 hm) e = X2 hm := by
  apply raw_step_eq_self_of_transition
  have he0 : e.val ≠ 0 := by
    intro h; apply h0; apply Fin.ext; simpa [v0, v] using h
  have he2 : e.val ≠ 2 := by
    intro h; apply h2; apply Fin.ext; simpa [v2, v] using h
  have he3 : e.val ≠ 3 := by
    intro h; apply h3; apply Fin.ext; simpa [v3, v] using h
  have hnb : ¬ IsBarrier hk3 (X2 hm e)
      (X2 hm ((ring m).rightNeighbor e)) := by
    intro h
    have hb : BarrierAt hk3 (ring m) (labelsOf (X2 hm)) e :=
      (barrierAt_labelsOf_iff hk3 (ring m) (X2 hm) e).2 h
    exact ((X2_barrier_iff hm e).1 hb).elim he0 he3
  rw [transition_of_nonbarrier hk3 _ _ hnb]
  simp [nonBarrierStep, X2, base, he2]

theorem raw_X3_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h3 : e ≠ v3 m hm) :
    (protocol 3 hk3).step (ring m) (X3 hm) e = X3 hm := by
  apply raw_step_eq_self_of_transition
  have he0 : e.val ≠ 0 := by
    intro h; apply h0; apply Fin.ext; simpa [v0, v] using h
  have he3 : e.val ≠ 3 := by
    intro h; apply h3; apply Fin.ext; simpa [v3, v] using h
  have hnb : ¬ IsBarrier hk3 (X3 hm e)
      (X3 hm ((ring m).rightNeighbor e)) := by
    intro h
    have hb : BarrierAt hk3 (ring m) (labelsOf (X3 hm)) e :=
      (barrierAt_labelsOf_iff hk3 (ring m) (X3 hm) e).2 h
    exact ((X3_barrier_iff hm e).1 hb).elim he0 he3
  rw [transition_of_nonbarrier hk3 _ _ hnb]
  simp [nonBarrierStep, X3, base, he3]

def st0 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := X0 hm, rear := v0 m, front := v3 m hm,
    ne := by simp [v0, v3, v, Fin.ext_iff]
    rearPre := (X0_preContacts hm).1
    frontPre := (X0_preContacts hm).2 }

def st1 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := X1 hm, rear := v0 m, front := v3 m hm,
    ne := by simp [v0, v3, v, Fin.ext_iff]
    rearPre := (X1_preContacts hm).1
    frontPre := (X1_preContacts hm).2 }

def st2 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := X2 hm, rear := v0 m, front := v3 m hm,
    ne := by simp [v0, v3, v, Fin.ext_iff]
    rearPre := (X2_preContacts hm).1
    frontPre := (X2_preContacts hm).2 }

def st3 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := X3 hm, rear := v0 m, front := v3 m hm,
    ne := by simp [v0, v3, v, Fin.ext_iff]
    rearPre := (X3_preContacts hm).1
    frontPre := (X3_preContacts hm).2 }

theorem colored_X0_zero {m : Nat} (hm : 1 ≤ m) :
    coloredStep (hn3 hm) (st0 hm) (v0 m) = .active (st1 hm) := by
  classical
  simp only [coloredStep, st0, raw_X0_zero hm, (X1_preContacts hm).1,
    (X1_preContacts hm).2, ↓reduceDIte]
  rfl

theorem colored_X1_one {m : Nat} (hm : 1 ≤ m) :
    coloredStep (hn3 hm) (st1 hm) (v1 m) = .active (st2 hm) := by
  classical
  simp only [coloredStep, st1, raw_X1_one hm, (X2_preContacts hm).1,
    (X2_preContacts hm).2, ↓reduceDIte]
  rfl

theorem colored_X2_two {m : Nat} (hm : 1 ≤ m) :
    coloredStep (hn3 hm) (st2 hm) (v2 m hm) = .active (st3 hm) := by
  classical
  simp only [coloredStep, st2, raw_X2_two hm, (X3_preContacts hm).1,
    (X3_preContacts hm).2, ↓reduceDIte]
  rfl

theorem colored_X0_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h3 : e ≠ v3 m hm) :
    coloredStep (hn3 hm) (st0 hm) e = .active (st0 hm) := by
  classical
  simp [coloredStep, st0, raw_X0_quiet hm e h0 h3,
    (X0_preContacts hm).1, (X0_preContacts hm).2]

theorem colored_X1_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h1 : e ≠ v1 m) (h3 : e ≠ v3 m hm) :
    coloredStep (hn3 hm) (st1 hm) e = .active (st1 hm) := by
  classical
  simp [coloredStep, st1, raw_X1_quiet hm e h1 h3,
    (X1_preContacts hm).1, (X1_preContacts hm).2]

theorem colored_X2_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h2 : e ≠ v2 m hm) (h3 : e ≠ v3 m hm) :
    coloredStep (hn3 hm) (st2 hm) e = .active (st2 hm) := by
  classical
  simp [coloredStep, st2, raw_X2_quiet hm e h0 h2 h3,
    (X2_preContacts hm).1, (X2_preContacts hm).2]

theorem colored_X3_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h3 : e ≠ v3 m hm) :
    coloredStep (hn3 hm) (st3 hm) e = .active (st3 hm) := by
  classical
  simp [coloredStep, st3, raw_X3_quiet hm e h0 h3,
    (X3_preContacts hm).1, (X3_preContacts hm).2]

def F3 {m : Nat} (hm : 1 ≤ m) : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) (X3 hm) (v3 m hm)

def F0 {m : Nat} (hm : 1 ≤ m) : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) (X0 hm) (v3 m hm)

def F1 {m : Nat} (hm : 1 ≤ m) : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) (X1 hm) (v3 m hm)

def F2 {m : Nat} (hm : 1 ≤ m) : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) (X2 hm) (v3 m hm)

private theorem trans_X3_three {m : Nat} (hm : 1 ≤ m) :
    transition hk3 (X3 hm (v3 m hm))
      (X3 hm ((ring m).rightNeighbor (v3 m hm))) =
      ({ X3 hm (v3 m hm) with leader := true, probe := false },
       { X3 hm (v4 m hm) with
          label := succLabel hk3 (X3 hm (v3 m hm)).label,
          phase := false, bullet := false }) := by
  rw [rn_v3 hm]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    X3, base, v0, v3, v4, v, lab, labelNat, succLabel]

/-- The front terminal at `X3` performs probe-to-leader birth before advancing. -/
theorem F3_birth_before_front {m : Nat} (hm : 1 ≤ m) :
    (F3 hm (v3 m hm)).leader = true ∧
      (F3 hm (v3 m hm)).probe = false ∧
      (F3 hm (v3 m hm)).phase = true := by
  simp only [F3, PopulationProtocol.step, protocol, trans_X3_three hm]
  simp [X3, base, v3, v4, v, Fin.ext_iff]

private theorem front_labels_eq_F3 {m : Nat} (hm : 1 ≤ m) :
    labelsOf (F0 hm) = labelsOf (F3 hm) ∧
      labelsOf (F1 hm) = labelsOf (F3 hm) ∧
      labelsOf (F2 hm) = labelsOf (F3 hm) := by
  constructor
  · funext i
    simp only [labelsOf, F0, F3, PopulationProtocol.step, protocol]
    rw [rn_v3 hm]
    by_cases hi3 : i = v3 m hm
    · subst i; simp [transition, barrierStep, probeHitsBarrier, IsBarrier,
        X0, X3, base, v0, v3, v4, v, lab, labelNat, succLabel]
    by_cases hi4 : i = v4 m hm
    · subst i; simp [transition, barrierStep, probeHitsBarrier, IsBarrier,
        X0, X3, base, v0, v3, v4, v, lab, labelNat, succLabel]
    simp [hi3, hi4, X0, X1, X2, X3, base]
  constructor
  · funext i
    simp only [labelsOf, F1, F3, PopulationProtocol.step, protocol]
    rw [rn_v3 hm]
    by_cases hi3 : i = v3 m hm
    · subst i; simp [transition, barrierStep, probeHitsBarrier, IsBarrier,
        X1, X3, base, v0, v3, v4, v, lab, labelNat, succLabel]
    by_cases hi4 : i = v4 m hm
    · subst i; simp [transition, barrierStep, probeHitsBarrier, IsBarrier,
        X1, X3, base, v0, v3, v4, v, lab, labelNat, succLabel]
    simp [hi3, hi4, X0, X1, X2, X3, base]
  · funext i
    simp only [labelsOf, F2, F3, PopulationProtocol.step, protocol]
    rw [rn_v3 hm]
    by_cases hi3 : i = v3 m hm
    · subst i; simp [transition, barrierStep, probeHitsBarrier, IsBarrier,
        X2, X3, base, v0, v3, v4, v, lab, labelNat, succLabel]
    by_cases hi4 : i = v4 m hm
    · subst i; simp [transition, barrierStep, probeHitsBarrier, IsBarrier,
        X2, X3, base, v0, v3, v4, v, lab, labelNat, succLabel]
    simp [hi3, hi4, X0, X1, X2, X3, base]

private theorem F3_at_other {m : Nat} (hm : 1 ≤ m) (i : Fin (N m))
    (hi3 : i ≠ v3 m hm) (hi4 : i ≠ v4 m hm) : F3 hm i = X3 hm i := by
  simp only [F3, PopulationProtocol.step, protocol, trans_X3_three hm]
  rw [rn_v3 hm]
  simp [hi3, hi4]

private theorem F3_at_v3 {m : Nat} (hm : 1 ≤ m) :
    F3 hm (v3 m hm) = { X3 hm (v3 m hm) with leader := true, probe := false } := by
  simp only [F3, PopulationProtocol.step, protocol, trans_X3_three hm]
  rw [rn_v3 hm]
  simp

private theorem F3_at_v4 {m : Nat} (hm : 1 ≤ m) :
    F3 hm (v4 m hm) =
      { X3 hm (v4 m hm) with
        label := succLabel hk3 (X3 hm (v3 m hm)).label,
        phase := false, bullet := false } := by
  simp only [F3, PopulationProtocol.step, protocol, trans_X3_three hm]
  rw [rn_v3 hm]
  simp [v3, v4, v, Fin.ext_iff]

private theorem F3_barrier_zero {m : Nat} (hm : 1 ≤ m) :
    BarrierAt hk3 (ring m) (labelsOf (F3 hm)) (v0 m) := by
  rw [barrierAt_labelsOf_iff, rn_v0, F3_at_other hm, F3_at_other hm]
  · change succLabel hk3 (lab (v0 m)) ≠ lab (v1 m)
    have h := lab_barrier_iff hm (v0 m)
    rw [rn_v0] at h
    exact h.2 (Or.inl rfl)
  all_goals simp [v0, v1, v3, v4, v, Fin.ext_iff]

private theorem F3_not_barrier_one {m : Nat} (hm : 1 ≤ m) :
    ¬ BarrierAt hk3 (ring m) (labelsOf (F3 hm)) (v1 m) := by
  rw [barrierAt_labelsOf_iff, rn_v1 hm, F3_at_other hm, F3_at_other hm]
  · change ¬ succLabel hk3 (lab (v1 m)) ≠ lab (v2 m hm)
    have h := lab_barrier_iff hm (v1 m)
    rw [rn_v1 hm] at h
    exact not_congr h |>.2 (by simp [v1, v])
  all_goals simp [v1, v2, v3, v4, v, Fin.ext_iff]

private theorem F3_not_barrier_three {m : Nat} (hm : 1 ≤ m) :
    ¬ BarrierAt hk3 (ring m) (labelsOf (F3 hm)) (v3 m hm) := by
  rw [barrierAt_labelsOf_iff, rn_v3 hm, F3_at_v3 hm, F3_at_v4 hm]
  simp [IsBarrier, X3, base, succLabel, v0, v3, v4, v, lab, labelNat,
    Fin.ext_iff]

private theorem F3_not_barrier_last {m : Nat} (hm : 1 ≤ m) :
    ¬ BarrierAt hk3 (ring m) (labelsOf (F3 hm)) (vlast m) := by
  rw [barrierAt_labelsOf_iff, rn_vlast, F3_at_other hm, F3_at_other hm]
  · change ¬ succLabel hk3 (lab (vlast m)) ≠ lab (v0 m)
    have h := lab_barrier_iff hm (vlast m)
    rw [rn_vlast] at h
    exact not_congr h |>.2 (by
      simp [vlast, N]
      omega)
  all_goals simp [vlast, v0, v3, v4, v, N, Fin.ext_iff] <;> omega

theorem F3_rear_pre {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (F3 hm) (v0 m) := by
  refine ⟨F3_barrier_zero hm, ?_, ?_⟩
  · simpa [rn_v0] using F3_not_barrier_one hm
  · intro e he
    have helast : e = vlast m :=
      rightNeighbor_injective (ring m) (he.trans rn_vlast.symm)
    simpa [helast] using F3_not_barrier_last hm

theorem F3_front_not_pre {m : Nat} (hm : 1 ≤ m) :
    ¬ PreContact hk3 (ring m) (F3 hm) (v3 m hm) := by
  intro h
  exact F3_not_barrier_three hm h.1

theorem F3_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (F3 hm) (v3 m hm) := by
  intro h
  exact F3_not_barrier_three hm h.1

private theorem F0_rear_pre {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (F0 hm) (v0 m) := by
  unfold PreContact
  rw [(front_labels_eq_F3 hm).1]
  exact F3_rear_pre hm

private theorem F1_rear_pre {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (F1 hm) (v0 m) := by
  unfold PreContact
  rw [(front_labels_eq_F3 hm).2.1]
  exact F3_rear_pre hm

private theorem F2_rear_pre {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (F2 hm) (v0 m) := by
  unfold PreContact
  rw [(front_labels_eq_F3 hm).2.2]
  exact F3_rear_pre hm

private theorem F0_front_not_pre {m : Nat} (hm : 1 ≤ m) :
    ¬ PreContact hk3 (ring m) (F0 hm) (v3 m hm) := by
  unfold PreContact
  rw [(front_labels_eq_F3 hm).1]
  exact F3_front_not_pre hm

private theorem F1_front_not_pre {m : Nat} (hm : 1 ≤ m) :
    ¬ PreContact hk3 (ring m) (F1 hm) (v3 m hm) := by
  unfold PreContact
  rw [(front_labels_eq_F3 hm).2.1]
  exact F3_front_not_pre hm

private theorem F2_front_not_pre {m : Nat} (hm : 1 ≤ m) :
    ¬ PreContact hk3 (ring m) (F2 hm) (v3 m hm) := by
  unfold PreContact
  rw [(front_labels_eq_F3 hm).2.2]
  exact F3_front_not_pre hm

private theorem F0_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (F0 hm) (v3 m hm) := by
  unfold ContactAt
  rw [(front_labels_eq_F3 hm).1]
  exact F3_front_not_contact hm

private theorem F1_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (F1 hm) (v3 m hm) := by
  unfold ContactAt
  rw [(front_labels_eq_F3 hm).2.1]
  exact F3_front_not_contact hm

private theorem F2_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (F2 hm) (v3 m hm) := by
  unfold ContactAt
  rw [(front_labels_eq_F3 hm).2.2]
  exact F3_front_not_contact hm

theorem colored_X0_three {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st0 hm) (v3 m hm) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F0 hm := by
  classical
  simp only [coloredStep, st0, show
    (protocol 3 hk3).step (ring m) (X0 hm) (v3 m hm) = F0 hm from rfl]
  simp [F0_rear_pre hm, F0_front_not_pre hm, F0_front_not_contact hm]

theorem colored_X1_three {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st1 hm) (v3 m hm) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F1 hm := by
  classical
  simp only [coloredStep, st1, show
    (protocol 3 hk3).step (ring m) (X1 hm) (v3 m hm) = F1 hm from rfl]
  simp [F1_rear_pre hm, F1_front_not_pre hm, F1_front_not_contact hm]

theorem colored_X2_three {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) (v3 m hm) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F2 hm := by
  classical
  simp only [coloredStep, st2, show
    (protocol 3 hk3).step (ring m) (X2 hm) (v3 m hm) = F2 hm from rfl]
  simp [F2_rear_pre hm, F2_front_not_pre hm, F2_front_not_contact hm]

/-- The `X3,e=3` child is a genuine front terminal whose literal post-state
records the probe-to-leader birth. -/
theorem colored_X3_three {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m), coloredStep (hn3 hm) (st3 hm) (v3 m hm) = PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F3 hm := by
  classical
  simp only [coloredStep, st3, show
    (protocol 3 hk3).step (ring m) (X3 hm) (v3 m hm) = F3 hm from rfl]
  simp [F3_rear_pre hm, F3_front_not_pre hm, F3_front_not_contact hm]

def R2 {m : Nat} (hm : 1 ≤ m) : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) (X2 hm) (v0 m)

def R3 {m : Nat} (hm : 1 ≤ m) : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) (X3 hm) (v0 m)

private theorem trans_X2_zero {m : Nat} (hm : 1 ≤ m) :
    transition hk3 (X2 hm (v0 m)) (X2 hm ((ring m).rightNeighbor (v0 m))) =
      (X2 hm (v0 m),
       { X2 hm (v1 m) with
          label := succLabel hk3 (X2 hm (v0 m)).label,
          phase := false, bullet := false }) := by
  rw [rn_v0]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    X2, base, v0, v1, v3, v, lab, labelNat, succLabel]

private theorem trans_X3_zero {m : Nat} (hm : 1 ≤ m) :
    transition hk3 (X3 hm (v0 m)) (X3 hm ((ring m).rightNeighbor (v0 m))) =
      (X3 hm (v0 m),
       { X3 hm (v1 m) with
          label := succLabel hk3 (X3 hm (v0 m)).label,
          phase := false, bullet := false }) := by
  rw [rn_v0]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    X3, base, v0, v1, v3, v, lab, labelNat, succLabel]

private theorem rear_labels_eq {m : Nat} (hm : 1 ≤ m) :
    labelsOf (R2 hm) = labelsOf (R3 hm) := by
  funext i
  simp only [labelsOf, R2, R3, PopulationProtocol.step, protocol,
    trans_X2_zero hm, trans_X3_zero hm]
  rw [rn_v0]
  by_cases hi0 : i = v0 m
  · subst i; simp [X2, X3, base]
  by_cases hi1 : i = v1 m
  · subst i; simp [X2, X3, base, v0, v1, v, Fin.ext_iff]
  simp [hi0, hi1, X2, X3, base]

private theorem R2_at_other {m : Nat} (hm : 1 ≤ m) (i : Fin (N m))
    (hi0 : i ≠ v0 m) (hi1 : i ≠ v1 m) : R2 hm i = X2 hm i := by
  simp only [R2, PopulationProtocol.step, protocol, trans_X2_zero hm]
  rw [rn_v0]
  simp [hi0, hi1]

private theorem R2_at_v0 {m : Nat} (hm : 1 ≤ m) :
    R2 hm (v0 m) = X2 hm (v0 m) := by
  simp only [R2, PopulationProtocol.step, protocol, trans_X2_zero hm]
  rw [rn_v0]
  simp

private theorem R2_at_v1 {m : Nat} (hm : 1 ≤ m) :
    R2 hm (v1 m) =
      { X2 hm (v1 m) with
        label := succLabel hk3 (X2 hm (v0 m)).label,
        phase := false, bullet := false } := by
  simp only [R2, PopulationProtocol.step, protocol, trans_X2_zero hm]
  rw [rn_v0]
  simp [v0, v1, v, Fin.ext_iff]

private theorem R2_not_barrier_zero {m : Nat} (hm : 1 ≤ m) :
    ¬ BarrierAt hk3 (ring m) (labelsOf (R2 hm)) (v0 m) := by
  rw [barrierAt_labelsOf_iff, rn_v0, R2_at_v0 hm, R2_at_v1 hm]
  simp [IsBarrier, X2, base, succLabel, v0, v1, v, lab, labelNat,
    Fin.ext_iff]

private theorem R2_not_barrier_two {m : Nat} (hm : 1 ≤ m) :
    ¬ BarrierAt hk3 (ring m) (labelsOf (R2 hm)) (v2 m hm) := by
  rw [barrierAt_labelsOf_iff, rn_v2 hm, R2_at_other hm, R2_at_other hm]
  · change ¬ succLabel hk3 (lab (v2 m hm)) ≠ lab (v3 m hm)
    have h := lab_barrier_iff hm (v2 m hm)
    rw [rn_v2 hm] at h
    exact not_congr h |>.2 (by simp [v2, v])
  all_goals simp [v0, v1, v2, v3, v, Fin.ext_iff]

private theorem R2_barrier_three {m : Nat} (hm : 1 ≤ m) :
    BarrierAt hk3 (ring m) (labelsOf (R2 hm)) (v3 m hm) := by
  rw [barrierAt_labelsOf_iff, rn_v3 hm, R2_at_other hm, R2_at_other hm]
  · change succLabel hk3 (lab (v3 m hm)) ≠ lab (v4 m hm)
    have h := lab_barrier_iff hm (v3 m hm)
    rw [rn_v3 hm] at h
    exact h.2 (Or.inr rfl)
  all_goals simp [v0, v1, v3, v4, v, Fin.ext_iff]

private theorem R2_not_barrier_four {m : Nat} (hm : 1 ≤ m) :
    ¬ BarrierAt hk3 (ring m) (labelsOf (R2 hm)) (v4 m hm) := by
  rw [barrierAt_labelsOf_iff, rn_v4 hm, R2_at_other hm, R2_at_other hm]
  · change ¬ succLabel hk3 (lab (v4 m hm)) ≠ lab (v5 m hm)
    have h := lab_barrier_iff hm (v4 m hm)
    rw [rn_v4 hm] at h
    exact not_congr h |>.2 (by simp [v4, v])
  all_goals simp [v0, v1, v4, v5, v, Fin.ext_iff]

private theorem R2_rear_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (R2 hm) (v0 m) := by
  intro h
  exact R2_not_barrier_zero hm h.1

private theorem R2_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (R2 hm) (v3 m hm) := by
  rintro ⟨_, hright | ⟨e, he, hleft⟩⟩
  · rw [rn_v3 hm] at hright
    exact R2_not_barrier_four hm hright
  · have hev2 : e = v2 m hm :=
      rightNeighbor_injective (ring m) (he.trans (rn_v2 hm).symm)
    exact R2_not_barrier_two hm (by simpa [hev2] using hleft)

private theorem R3_rear_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (R3 hm) (v0 m) := by
  unfold ContactAt
  rw [← rear_labels_eq hm]
  exact R2_rear_not_contact hm

private theorem R3_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (R3 hm) (v3 m hm) := by
  unfold ContactAt
  rw [← rear_labels_eq hm]
  exact R2_front_not_contact hm

theorem colored_X2_zero {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) (v0 m) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.rearAdvance ∧ p.config = R2 hm := by
  classical
  simp only [coloredStep, st2, show
    (protocol 3 hk3).step (ring m) (X2 hm) (v0 m) = R2 hm from rfl]
  have hnpre : ¬ PreContact hk3 (ring m) (R2 hm) (v0 m) := by
    intro h; exact R2_not_barrier_zero hm h.1
  simp [hnpre, R2_rear_not_contact hm, R2_front_not_contact hm]

theorem colored_X3_zero {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st3 hm) (v0 m) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.rearAdvance ∧ p.config = R3 hm := by
  classical
  simp only [coloredStep, st3, show
    (protocol 3 hk3).step (ring m) (X3 hm) (v0 m) = R3 hm from rfl]
  have hnpre : ¬ PreContact hk3 (ring m) (R3 hm) (v0 m) := by
    intro h
    have hb : BarrierAt hk3 (ring m) (labelsOf (R2 hm)) (v0 m) := by
      rw [rear_labels_eq hm]
      exact h.1
    exact R2_not_barrier_zero hm hb
  simp [hnpre, R3_rear_not_contact hm, R3_front_not_contact hm]

/-- Complete colored child partition of `X0`. -/
theorem X0_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v0 m ∧ coloredStep (hn3 hm) (st0 hm) e = .active (st1 hm)) ∨
    (e = v3 m hm ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st0 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F0 hm) ∨
    (e ≠ v0 m ∧ e ≠ v3 m hm ∧
      coloredStep (hn3 hm) (st0 hm) e = .active (st0 hm)) := by
  by_cases h0 : e = v0 m
  · left; subst e; exact ⟨rfl, colored_X0_zero hm⟩
  by_cases h3 : e = v3 m hm
  · right; left; subst e; exact ⟨rfl, colored_X0_three hm⟩
  exact Or.inr (Or.inr ⟨h0, h3, colored_X0_quiet hm e h0 h3⟩)

/-- Complete colored child partition of `X1`. -/
theorem X1_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v1 m ∧ coloredStep (hn3 hm) (st1 hm) e = .active (st2 hm)) ∨
    (e = v3 m hm ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st1 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F1 hm) ∨
    (e ≠ v1 m ∧ e ≠ v3 m hm ∧
      coloredStep (hn3 hm) (st1 hm) e = .active (st1 hm)) := by
  by_cases h1 : e = v1 m
  · left; subst e; exact ⟨rfl, colored_X1_one hm⟩
  by_cases h3 : e = v3 m hm
  · right; left; subst e; exact ⟨rfl, colored_X1_three hm⟩
  exact Or.inr (Or.inr ⟨h1, h3, colored_X1_quiet hm e h1 h3⟩)

/-- Complete colored child partition of `X2`. -/
theorem X2_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v0 m ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.rearAdvance ∧ p.config = R2 hm) ∨
    (e = v2 m hm ∧ coloredStep (hn3 hm) (st2 hm) e = .active (st3 hm)) ∨
    (e = v3 m hm ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F2 hm) ∨
    (e ≠ v0 m ∧ e ≠ v2 m hm ∧ e ≠ v3 m hm ∧
      coloredStep (hn3 hm) (st2 hm) e = .active (st2 hm)) := by
  by_cases h0 : e = v0 m
  · left; subst e; exact ⟨rfl, colored_X2_zero hm⟩
  by_cases h2 : e = v2 m hm
  · right; left; subst e; exact ⟨rfl, colored_X2_two hm⟩
  by_cases h3 : e = v3 m hm
  · right; right; left; subst e; exact ⟨rfl, colored_X2_three hm⟩
  exact Or.inr (Or.inr (Or.inr ⟨h0, h2, h3,
    colored_X2_quiet hm e h0 h2 h3⟩))

/-- Complete colored child partition of `X3`.  Its front terminal retains the
birth-before-front post-configuration proved by `F3_birth_before_front`. -/
theorem X3_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v0 m ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st3 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.rearAdvance ∧ p.config = R3 hm) ∨
    (e = v3 m hm ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st3 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F3 hm) ∨
    (e ≠ v0 m ∧ e ≠ v3 m hm ∧
      coloredStep (hn3 hm) (st3 hm) e = .active (st3 hm)) := by
  by_cases h0 : e = v0 m
  · left; subst e; exact ⟨rfl, colored_X3_zero hm⟩
  by_cases h3 : e = v3 m hm
  · right; left; subst e; exact ⟨rfl, colored_X3_three hm⟩
  exact Or.inr (Or.inr ⟨h0, h3, colored_X3_quiet hm e h0 h3⟩)

end AAFJPK.N6m2ColoredChildTable
