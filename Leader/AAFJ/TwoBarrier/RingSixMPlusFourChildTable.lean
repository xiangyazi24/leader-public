import Leader.AAFJ.TwoBarrier.ColoredEndpointTerminals
import Leader.AAFJ.MultiBarrier.SixHitContactBlock
import Leader.AAFJ.NonbarrierWord

set_option autoImplicit false
set_option Elab.async false

/-!
# The explicit `n = 6m+4` two-barrier producer

This file records the literal semantic child table for the original journal
`P₃` transition.  The rear tag is edge `0`, the front tag is edge `2`, and the
initial charged support is exactly `{0,2}`.  The only live path before contact
is

`S0 --0--> S1 --1--> S2 --0--> H`.

At every live state edge `2` is the unique front-advance exit.  Every remaining
edge is a physical identity.  The contact state `H` has charged support
exactly `{1,2}`.  No scheduler counting is done here.
-/

namespace AAFJPK.N6m4ColoredChildTable

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

def N (m : Nat) : Nat := 6 * m + 4

def ring (m : Nat) : DirectedRing (N m) := ⟨by simp [N]⟩

private theorem hn3 {m : Nat} (hm : 1 ≤ m) : 2 < N m := by
  simp [N]

private theorem hk3 : 0 < 3 := by decide

def v (m a : Nat) (ha : a < N m) : Fin (N m) := ⟨a, ha⟩

def v0 (m : Nat) : Fin (N m) := v m 0 (by simp [N])
def v1 (m : Nat) : Fin (N m) := v m 1 (by simp [N])
def v2 (m : Nat) : Fin (N m) := v m 2 (by simp [N])
def v3 (m : Nat) : Fin (N m) := v m 3 (by simp [N])
def v4 (m : Nat) (hm : 1 ≤ m) : Fin (N m) := v m 4 (by simp [N]; omega)

def vlast (m : Nat) : Fin (N m) := ⟨N m - 1, by simp [N]⟩

/-- Labels `0,2,0,2,0,1,2,...`; the two defects are at edges 0 and 2. -/
def labelNat (i : Nat) : Nat :=
  if i = 0 then 0
  else if i = 1 then 2
  else if i = 2 then 0
  else i - 1

def lab {m : Nat} (i : Fin (N m)) : Fin 3 :=
  ⟨labelNat i.val % 3, Nat.mod_lt _ (by decide)⟩

def base (l : Fin 3) (p h : Bool) : State 3 :=
  { bullet := false, leader := false, label := l, probe := p, phase := h }

/-- Initial full configuration: only the front-tail phase at vertex 2 is set. -/
def S0 {m : Nat} (i : Fin (N m)) : State 3 :=
  base (lab i) false (decide (i.val = 2))

/-- After the cold rear hit: rear and front phases are set, probe at vertex 1. -/
def S1 {m : Nat} (i : Fin (N m)) : State 3 :=
  base (lab i) (decide (i.val = 1))
    (decide (i.val = 0 ∨ i.val = 2))

/-- After moving the probe across edge 1: its unique location is vertex 2. -/
def S2 {m : Nat} (i : Fin (N m)) : State 3 :=
  base (lab i) (decide (i.val = 2))
    (decide (i.val = 0 ∨ i.val = 2))

/-- The physical contact child obtained by advancing rear edge 0 from `S2`. -/
def H {m : Nat} : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) S2 (v0 m)

private theorem rn_v0 {m : Nat} :
    (ring m).rightNeighbor (v0 m) = v1 m := by
  apply Fin.ext
  simp [ring, v0, v1, v, N, DirectedRing.rightNeighbor]

private theorem rn_v1 {m : Nat} :
    (ring m).rightNeighbor (v1 m) = v2 m := by
  apply Fin.ext
  simp [ring, v1, v2, v, N, DirectedRing.rightNeighbor]

private theorem rn_v2 {m : Nat} :
    (ring m).rightNeighbor (v2 m) = v3 m := by
  apply Fin.ext
  simp [ring, v2, v3, v, N, DirectedRing.rightNeighbor]

private theorem rn_v3 {m : Nat} (hm : 1 ≤ m) :
    (ring m).rightNeighbor (v3 m) = v4 m hm := by
  apply Fin.ext
  simp [ring, v3, v4, v, N, DirectedRing.rightNeighbor]
  omega

private theorem rn_vlast {m : Nat} :
    (ring m).rightNeighbor (vlast m) = v0 m := by
  apply Fin.ext
  simp [ring, vlast, v0, v, N, DirectedRing.rightNeighbor]

private theorem lab_barrier_iff {m : Nat} (hm : 1 ≤ m)
    (e : Fin (N m)) :
    succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔
      e.val = 0 ∨ e.val = 2 := by
  have hfin :
      (succLabel hk3 (lab e) = lab ((ring m).rightNeighbor e)) ↔
        ((labelNat e.val % 3 + 1) % 3 =
          labelNat ((e.val + 1) % N m) % 3) := by
    rw [Fin.ext_iff]
    rfl
  have hnum : ((labelNat e.val % 3 + 1) % 3 ≠
      labelNat ((e.val + 1) % N m) % 3) ↔
      e.val = 0 ∨ e.val = 2 := by
    by_cases hnext : e.val + 1 < N m
    · rw [Nat.mod_eq_of_lt hnext]
      by_cases h0 : e.val = 0
      · simp [labelNat, h0]
      by_cases h1 : e.val = 1
      · simp [labelNat, h1]
      by_cases h2 : e.val = 2
      · simp [labelNat, h2]
      have h3 : 3 ≤ e.val := by omega
      rw [labelNat, if_neg h0, if_neg h1, if_neg h2]
      rw [labelNat, if_neg (by omega : e.val + 1 ≠ 0),
        if_neg (by omega : e.val + 1 ≠ 1),
        if_neg (by omega : e.val + 1 ≠ 2)]
      have hcancel : e.val - 1 + 1 = e.val := by omega
      have hnextcancel : e.val + 1 - 1 = e.val := by omega
      have hmod : ((e.val - 1) % 3 + 1) % 3 = e.val % 3 := by
        calc
          ((e.val - 1) % 3 + 1) % 3 =
              ((e.val - 1) + 1) % 3 := by
                symm
                simpa using Nat.add_mod (e.val - 1) 1 3
          _ = e.val % 3 := congrArg (fun x => x % 3) hcancel
      rw [hnextcancel, hmod]
      simp [h0, h2]
    · have heq : e.val + 1 = N m := by omega
      have heval : e.val = 6 * m + 3 := by simp [N] at heq; omega
      rw [heq, Nat.mod_self, heval]
      rw [labelNat, if_neg (by omega : 6 * m + 3 ≠ 0),
        if_neg (by omega : 6 * m + 3 ≠ 1),
        if_neg (by omega : 6 * m + 3 ≠ 2)]
      simp [labelNat, Nat.add_mod, Nat.mul_mod]
  constructor
  · intro h
    exact hnum.mp (fun hn => h (hfin.mpr hn))
  · intro hp heq
    exact hnum.mpr hp (hfin.mp heq)

private theorem live_barrier_iff {m : Nat} (hm : 1 ≤ m)
    (C : Fin (N m) → State 3)
    (hl : labelsOf C = labelsOf (S0 (m := m))) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf C) e ↔
      e.val = 0 ∨ e.val = 2 := by
  rw [hl, barrierAt_labelsOf_iff]
  change succLabel hk3 (lab e) ≠ lab ((ring m).rightNeighbor e) ↔ _
  exact lab_barrier_iff hm e

private theorem labels_S1 {m : Nat} :
    labelsOf (S1 (m := m)) = labelsOf (S0 (m := m)) := by
  rfl

private theorem labels_S2 {m : Nat} :
    labelsOf (S2 (m := m)) = labelsOf (S0 (m := m)) := by
  rfl

theorem S0_support {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (S0 (m := m))) e ↔
      e = v0 m ∨ e = v2 m := by
  rw [live_barrier_iff hm S0 rfl]
  simp [v0, v2, v, Fin.ext_iff]

theorem S1_support {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (S1 (m := m))) e ↔
      e = v0 m ∨ e = v2 m := by
  rw [live_barrier_iff hm S1 labels_S1]
  simp [v0, v2, v, Fin.ext_iff]

theorem S2_support {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (S2 (m := m))) e ↔
      e = v0 m ∨ e = v2 m := by
  rw [live_barrier_iff hm S2 labels_S2]
  simp [v0, v2, v, Fin.ext_iff]

private theorem preContacts_of_support {m : Nat} (hm : 1 ≤ m)
    (C : Fin (N m) → State 3)
    (hs : ∀ e, BarrierAt hk3 (ring m) (labelsOf C) e ↔
      e = v0 m ∨ e = v2 m) :
    PreContact hk3 (ring m) C (v0 m) ∧
      PreContact hk3 (ring m) C (v2 m) := by
  constructor
  · refine ⟨(hs (v0 m)).2 (Or.inl rfl), ?_, ?_⟩
    · rw [rn_v0, hs]
      simp [v0, v1, v2, v, Fin.ext_iff]
    · intro e he
      have helast : e = vlast m :=
        rightNeighbor_injective (ring m) (he.trans rn_vlast.symm)
      rw [helast, hs]
      simp [vlast, v0, v2, v, N, Fin.ext_iff]
  · refine ⟨(hs (v2 m)).2 (Or.inr rfl), ?_, ?_⟩
    · rw [rn_v2, hs]
      simp [v0, v2, v3, v, Fin.ext_iff]
    · intro e he
      have hev1 : e = v1 m :=
        rightNeighbor_injective (ring m) (he.trans rn_v1.symm)
      rw [hev1, hs]
      simp [v0, v1, v2, v, Fin.ext_iff]

theorem S0_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (S0 (m := m)) (v0 m) ∧
      PreContact hk3 (ring m) (S0 (m := m)) (v2 m) :=
  preContacts_of_support hm S0 (S0_support hm)

theorem S1_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (S1 (m := m)) (v0 m) ∧
      PreContact hk3 (ring m) (S1 (m := m)) (v2 m) :=
  preContacts_of_support hm S1 (S1_support hm)

theorem S2_preContacts {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (S2 (m := m)) (v0 m) ∧
      PreContact hk3 (ring m) (S2 (m := m)) (v2 m) :=
  preContacts_of_support hm S2 (S2_support hm)

private theorem trans_S0_zero {m : Nat} :
    transition hk3 (S0 (v0 m)) (S0 ((ring m).rightNeighbor (v0 m))) =
      (S1 (v0 m), S1 (v1 m)) := by
  rw [rn_v0]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    S0, S1, base, v0, v1, v, lab, labelNat, succLabel]

private theorem trans_S1_one {m : Nat} :
    transition hk3 (S1 (v1 m)) (S1 ((ring m).rightNeighbor (v1 m))) =
      (S2 (v1 m), S2 (v2 m)) := by
  rw [rn_v1]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    S1, S2, base, v0, v1, v2, v, lab, labelNat, succLabel]

private theorem trans_S2_zero {m : Nat} :
    transition hk3 (S2 (v0 m)) (S2 ((ring m).rightNeighbor (v0 m))) =
      (S2 (v0 m),
       { S2 (v1 m) with
         label := succLabel hk3 (S2 (v0 m)).label
         phase := false
         bullet := false }) := by
  rw [rn_v0]
  simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
    S2, base, v0, v1, v2, v, lab, labelNat, succLabel]

theorem raw_S0_zero {m : Nat} :
    (protocol 3 hk3).step (ring m) S0 (v0 m) = S1 := by
  funext i
  simp only [PopulationProtocol.step, protocol, trans_S0_zero]
  rw [rn_v0]
  by_cases hi0 : i = v0 m
  · subst i; simp [S1]
  by_cases hi1 : i = v1 m
  · subst i; simp [S1, v0, v1, v, Fin.ext_iff]
  have hi0v : i.val ≠ 0 := by
    intro h; apply hi0; apply Fin.ext; simpa [v0, v] using h
  have hi1v : i.val ≠ 1 := by
    intro h; apply hi1; apply Fin.ext; simpa [v1, v] using h
  simp [hi0, hi1, hi0v, hi1v, S0, S1]

theorem raw_S1_one {m : Nat} :
    (protocol 3 hk3).step (ring m) S1 (v1 m) = S2 := by
  funext i
  simp only [PopulationProtocol.step, protocol, trans_S1_one]
  rw [rn_v1]
  by_cases hi1 : i = v1 m
  · subst i; simp [S2, v1, v2, v]
  by_cases hi2 : i = v2 m
  · subst i; simp [S2, v1, v2, v, Fin.ext_iff]
  have hi1v : i.val ≠ 1 := by
    intro h; apply hi1; apply Fin.ext; simpa [v1, v] using h
  have hi2v : i.val ≠ 2 := by
    intro h; apply hi2; apply Fin.ext; simpa [v2, v] using h
  simp [hi1, hi2, hi1v, hi2v, S1, S2]

theorem raw_S2_zero {m : Nat} :
    (protocol 3 hk3).step (ring m) S2 (v0 m) = H := rfl

private theorem raw_step_eq_self_of_transition {m : Nat}
    (C : Fin (N m) → State 3) (e : Fin (N m))
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

theorem raw_S0_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h2 : e ≠ v2 m) :
    (protocol 3 hk3).step (ring m) S0 e = S0 := by
  apply raw_step_eq_self_of_transition
  have hnb : ¬ IsBarrier hk3 (S0 e) (S0 ((ring m).rightNeighbor e)) := by
    intro h
    have hb := (barrierAt_labelsOf_iff hk3 (ring m) S0 e).2 h
    exact (S0_support hm e).1 hb |>.elim h0 h2
  rw [transition_of_nonbarrier hk3 _ _ hnb]
  simp [nonBarrierStep, S0, base]

theorem raw_S1_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h1 : e ≠ v1 m) (h2 : e ≠ v2 m) :
    (protocol 3 hk3).step (ring m) S1 e = S1 := by
  apply raw_step_eq_self_of_transition
  by_cases h0 : e = v0 m
  · subst e
    rw [rn_v0]
    simp [transition, barrierStep, nonBarrierStep, probeHitsBarrier, IsBarrier,
      S1, base, v0, v1, v2, v, lab, labelNat, succLabel]
  · have hnb : ¬ IsBarrier hk3 (S1 e) (S1 ((ring m).rightNeighbor e)) := by
      intro h
      have hb := (barrierAt_labelsOf_iff hk3 (ring m) S1 e).2 h
      exact (S1_support hm e).1 hb |>.elim h0 h2
    rw [transition_of_nonbarrier hk3 _ _ hnb]
    have he1 : e.val ≠ 1 := by
      intro h; apply h1; apply Fin.ext; simpa [v1, v] using h
    simp [nonBarrierStep, S1, base, he1]

theorem raw_S2_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h2 : e ≠ v2 m) :
    (protocol 3 hk3).step (ring m) S2 e = S2 := by
  apply raw_step_eq_self_of_transition
  have hnb : ¬ IsBarrier hk3 (S2 e) (S2 ((ring m).rightNeighbor e)) := by
    intro h
    have hb := (barrierAt_labelsOf_iff hk3 (ring m) S2 e).2 h
    exact (S2_support hm e).1 hb |>.elim h0 h2
  rw [transition_of_nonbarrier hk3 _ _ hnb]
  have he2 : e.val ≠ 2 := by
    intro h; apply h2; apply Fin.ext; simpa [v2, v] using h
  simp [nonBarrierStep, S2, base, he2]

private theorem H_at_other {m : Nat} (i : Fin (N m))
    (hi0 : i ≠ v0 m) (hi1 : i ≠ v1 m) : H i = S2 i := by
  simp only [H, PopulationProtocol.step, protocol, trans_S2_zero]
  rw [rn_v0]
  simp [hi0, hi1]

private theorem H_at_v0 {m : Nat} : H (v0 m) = S2 (v0 m) := by
  simp only [H, PopulationProtocol.step, protocol, trans_S2_zero]
  rw [rn_v0]
  simp

private theorem H_at_v1 {m : Nat} :
    H (v1 m) =
      { S2 (v1 m) with
        label := succLabel hk3 (S2 (v0 m)).label
        phase := false
        bullet := false } := by
  simp only [H, PopulationProtocol.step, protocol, trans_S2_zero]
  rw [rn_v0]
  simp [v0, v1, v, Fin.ext_iff]

/-- The rear advance transfers the charge from edge 0 to edge 1 and preserves 2. -/
private theorem H_labels_advance {m : Nat} (hm : 1 ≤ m) :
    labelsOf H = advanceLabels hk3 (ring m) (labelsOf S2) (v0 m) := by
  apply labelsOf_step_eq_advance_of_ready hk3 (ring m) (by simp [N])
  refine ⟨?_, ?_, ?_⟩
  · exact (barrierAt_labelsOf_iff hk3 (ring m) S2 (v0 m)).1
      ((S2_support hm (v0 m)).2 (Or.inl rfl))
  · simp [S2, base, v0, v2, v, Fin.ext_iff]
  · rw [rn_v0]
    simp [S2, base, v1, v2, v, Fin.ext_iff]

private theorem S2_defect_v0 {m : Nat} :
    defect hk3 (ring m) (labelsOf S2) (v0 m) = (1 : Fin 3) := by
  unfold defect
  rw [rn_v0]
  apply Fin.ext
  simp [labelsOf, S2, base, v0, v1, v, lab, labelNat, succLabel]

private theorem S2_defect_v1 {m : Nat} :
    defect hk3 (ring m) (labelsOf S2) (v1 m) = (0 : Fin 3) := by
  unfold defect
  rw [rn_v1]
  apply Fin.ext
  simp [labelsOf, S2, base, v1, v2, v, lab, labelNat, succLabel]

private theorem S2_defect_v2 {m : Nat} :
    defect hk3 (ring m) (labelsOf S2) (v2 m) = (1 : Fin 3) := by
  unfold defect
  rw [rn_v2]
  apply Fin.ext
  simp [labelsOf, S2, base, v2, v3, v, lab, labelNat, succLabel]

private theorem S2_defect_v3 {m : Nat} (hm : 1 ≤ m) :
    defect hk3 (ring m) (labelsOf S2) (v3 m) = (0 : Fin 3) := by
  unfold defect
  rw [rn_v3 hm]
  apply Fin.ext
  simp [labelsOf, S2, base, v3, v4, v, lab, labelNat, succLabel]

theorem H_support {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf H) e ↔
      e = v1 m ∨ e = v2 m := by
  rw [H_labels_advance hm]
  by_cases he0 : e = v0 m
  · subst e
    constructor
    · intro h
      exact (advance_repairs_edge hk3 (ring m) (by simp [N])
        (labelsOf S2) (v0 m) h).elim
    · rintro (h | h) <;>
        simp [v0, v1, v2, v, Fin.ext_iff] at h
  by_cases he1 : e = v1 m
  · subst e
    constructor
    · intro _; exact Or.inl rfl
    · intro _
      unfold BarrierAt
      rw [← rn_v0, defect_advance_edgePlus hk3 (ring m) (by simp [N])]
      rw [rn_v0, S2_defect_v0, S2_defect_v1]
      decide
  · have hdef := defect_advance_other hk3 (ring m) (labelsOf S2)
        (v0 m) e he0 (by simpa [rn_v0] using he1)
    unfold BarrierAt
    rw [hdef]
    change BarrierAt hk3 (ring m) (labelsOf S2) e ↔ _
    rw [S2_support hm]
    simp [he0, he1]

theorem H_rear_not_pre {m : Nat} (hm : 1 ≤ m) :
    ¬ PreContact hk3 (ring m) H (v0 m) := by
  intro h
  exact (H_support hm (v0 m)).1 h.1 |>.elim
    (by simp [v0, v1, v, Fin.ext_iff])
    (by simp [v0, v2, v, Fin.ext_iff])

theorem H_rear_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) H (v0 m) := by
  rintro ⟨hbar, _⟩
  exact (H_support hm (v0 m)).1 hbar |>.elim
    (by simp [v0, v1, v, Fin.ext_iff])
    (by simp [v0, v2, v, Fin.ext_iff])

theorem H_front_contact {m : Nat} (hm : 1 ≤ m) :
    ContactAt hk3 (ring m) H (v2 m) := by
  refine ⟨(H_support hm (v2 m)).2 (Or.inr rfl), ?_⟩
  right
  refine ⟨v1 m, rn_v1, ?_⟩
  exact (H_support hm (v1 m)).2 (Or.inl rfl)

def st0 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := S0, rear := v0 m, front := v2 m
    ne := by simp [v0, v2, v, Fin.ext_iff]
    rearPre := (S0_preContacts hm).1
    frontPre := (S0_preContacts hm).2 }

def st1 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := S1, rear := v0 m, front := v2 m
    ne := by simp [v0, v2, v, Fin.ext_iff]
    rearPre := (S1_preContacts hm).1
    frontPre := (S1_preContacts hm).2 }

def st2 {m : Nat} (hm : 1 ≤ m) : ActivePair hk3 (ring m) :=
  { config := S2, rear := v0 m, front := v2 m
    ne := by simp [v0, v2, v, Fin.ext_iff]
    rearPre := (S2_preContacts hm).1
    frontPre := (S2_preContacts hm).2 }

theorem colored_S0_zero {m : Nat} (hm : 1 ≤ m) :
    coloredStep (hn3 hm) (st0 hm) (v0 m) = .active (st1 hm) := by
  classical
  simp only [coloredStep, st0, raw_S0_zero, (S1_preContacts hm).1,
    (S1_preContacts hm).2, ↓reduceDIte]
  rfl

theorem colored_S1_one {m : Nat} (hm : 1 ≤ m) :
    coloredStep (hn3 hm) (st1 hm) (v1 m) = .active (st2 hm) := by
  classical
  simp only [coloredStep, st1, raw_S1_one, (S2_preContacts hm).1,
    (S2_preContacts hm).2, ↓reduceDIte]
  rfl

theorem colored_S2_zero {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) (v0 m) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.contact ∧ p.config = H := by
  classical
  simp only [coloredStep, st2, raw_S2_zero]
  simp [H_rear_not_pre hm, H_rear_not_contact hm, H_front_contact hm]

def F0 {m : Nat} : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) S0 (v2 m)

def F1 {m : Nat} : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) S1 (v2 m)

def F2 {m : Nat} : Fin (N m) → State 3 :=
  (protocol 3 hk3).step (ring m) S2 (v2 m)

private theorem F0_labels {m : Nat} (hm : 1 ≤ m) :
    labelsOf (F0 (m := m)) =
      advanceLabels hk3 (ring m) (labelsOf (S0 (m := m))) (v2 m) := by
  apply labelsOf_step_eq_advance_of_ready hk3 (ring m) (by simp [N])
  refine ⟨?_, ?_, ?_⟩
  · exact (barrierAt_labelsOf_iff hk3 (ring m) S0 (v2 m)).1
      ((S0_support hm (v2 m)).2 (Or.inr rfl))
  · simp [S0, base, v2, v, Fin.ext_iff]
  · rw [rn_v2]
    simp [S0, base]

private theorem F1_labels {m : Nat} (hm : 1 ≤ m) :
    labelsOf (F1 (m := m)) =
      advanceLabels hk3 (ring m) (labelsOf (S1 (m := m))) (v2 m) := by
  apply labelsOf_step_eq_advance_of_ready hk3 (ring m) (by simp [N])
  refine ⟨?_, ?_, ?_⟩
  · exact (barrierAt_labelsOf_iff hk3 (ring m) S1 (v2 m)).1
      ((S1_support hm (v2 m)).2 (Or.inr rfl))
  · simp [S1, base, v0, v2, v, Fin.ext_iff]
  · rw [rn_v2]
    simp [S1, base, v0, v2, v3, v, Fin.ext_iff]

private theorem F2_labels {m : Nat} (hm : 1 ≤ m) :
    labelsOf (F2 (m := m)) =
      advanceLabels hk3 (ring m) (labelsOf (S2 (m := m))) (v2 m) := by
  apply labelsOf_step_eq_advance_of_ready hk3 (ring m) (by simp [N])
  refine ⟨?_, ?_, ?_⟩
  · exact (barrierAt_labelsOf_iff hk3 (ring m) S2 (v2 m)).1
      ((S2_support hm (v2 m)).2 (Or.inr rfl))
  · simp [S2, base, v0, v2, v, Fin.ext_iff]
  · rw [rn_v2]
    simp [S2, base, v0, v2, v3, v, Fin.ext_iff]

private theorem front_labels_eq {m : Nat} (hm : 1 ≤ m) :
    labelsOf (F0 (m := m)) = labelsOf (F1 (m := m)) ∧
      labelsOf (F1 (m := m)) = labelsOf (F2 (m := m)) := by
  rw [F0_labels hm, F1_labels hm, F2_labels hm, labels_S1, labels_S2]
  exact ⟨rfl, rfl⟩

private theorem F2_support {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    BarrierAt hk3 (ring m) (labelsOf (F2 (m := m))) e ↔
      e = v0 m ∨ e = v3 m := by
  rw [F2_labels hm]
  by_cases he2 : e = v2 m
  · subst e
    constructor
    · intro h
      exact (advance_repairs_edge hk3 (ring m) (by simp [N])
        (labelsOf S2) (v2 m) h).elim
    · rintro (h | h) <;>
        simp [v0, v2, v3, v, Fin.ext_iff] at h
  by_cases he3 : e = v3 m
  · subst e
    constructor
    · intro _; exact Or.inr rfl
    · intro _
      unfold BarrierAt
      rw [← rn_v2, defect_advance_edgePlus hk3 (ring m) (by simp [N])]
      rw [rn_v2, S2_defect_v2, S2_defect_v3 hm]
      decide
  · have hdef := defect_advance_other hk3 (ring m) (labelsOf S2)
        (v2 m) e he2 (by simpa [rn_v2] using he3)
    unfold BarrierAt
    rw [hdef]
    change BarrierAt hk3 (ring m) (labelsOf S2) e ↔ _
    rw [S2_support hm]
    simp [he2, he3]

private theorem front_rear_pre {m : Nat} (hm : 1 ≤ m) :
    PreContact hk3 (ring m) (F2 (m := m)) (v0 m) := by
  refine ⟨(F2_support hm (v0 m)).2 (Or.inl rfl), ?_, ?_⟩
  · rw [rn_v0, F2_support hm]
    simp [v0, v1, v3, v, Fin.ext_iff]
  · intro e he
    have helast : e = vlast m :=
      rightNeighbor_injective (ring m) (he.trans rn_vlast.symm)
    rw [helast, F2_support hm]
    simp [vlast, v0, v3, v, N, Fin.ext_iff]
    omega

private theorem front_front_not_pre {m : Nat} (hm : 1 ≤ m) :
    ¬ PreContact hk3 (ring m) (F2 (m := m)) (v2 m) := by
  intro h
  exact (F2_support hm (v2 m)).1 h.1 |>.elim
    (by simp [v0, v2, v, Fin.ext_iff])
    (by simp [v2, v3, v, Fin.ext_iff])

private theorem front_front_not_contact {m : Nat} (hm : 1 ≤ m) :
    ¬ ContactAt hk3 (ring m) (F2 (m := m)) (v2 m) := by
  rintro ⟨hbar, _⟩
  exact (F2_support hm (v2 m)).1 hbar |>.elim
    (by simp [v0, v2, v, Fin.ext_iff])
    (by simp [v2, v3, v, Fin.ext_iff])

private theorem front_facts_of_labels {m : Nat} (hm : 1 ≤ m)
    (F : Fin (N m) → State 3)
    (hl : labelsOf F = labelsOf (F2 (m := m))) :
    PreContact hk3 (ring m) F (v0 m) ∧
      ¬ PreContact hk3 (ring m) F (v2 m) ∧
      ¬ ContactAt hk3 (ring m) F (v2 m) := by
  constructor
  · unfold PreContact
    rw [hl]
    exact front_rear_pre hm
  constructor
  · unfold PreContact
    rw [hl]
    exact front_front_not_pre hm
  · unfold ContactAt
    rw [hl]
    exact front_front_not_contact hm

theorem colored_S0_two {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st0 hm) (v2 m) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F0 := by
  classical
  simp only [coloredStep, st0, show
    (protocol 3 hk3).step (ring m) S0 (v2 m) = F0 from rfl]
  have h := front_facts_of_labels hm F0
    ((front_labels_eq hm).1.trans (front_labels_eq hm).2)
  simp [h.1, h.2.1, h.2.2]

theorem colored_S1_two {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st1 hm) (v2 m) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F1 := by
  classical
  simp only [coloredStep, st1, show
    (protocol 3 hk3).step (ring m) S1 (v2 m) = F1 from rfl]
  have h := front_facts_of_labels hm F1 (front_labels_eq hm).2
  simp [h.1, h.2.1, h.2.2]

theorem colored_S2_two {m : Nat} (hm : 1 ≤ m) :
    ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) (v2 m) =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F2 := by
  classical
  simp only [coloredStep, st2, show
    (protocol 3 hk3).step (ring m) S2 (v2 m) = F2 from rfl]
  have h := front_facts_of_labels hm F2 rfl
  simp [h.1, h.2.1, h.2.2]

theorem colored_S0_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h2 : e ≠ v2 m) :
    coloredStep (hn3 hm) (st0 hm) e = .active (st0 hm) := by
  classical
  simp [coloredStep, st0, raw_S0_quiet hm e h0 h2,
    (S0_preContacts hm).1, (S0_preContacts hm).2]

theorem colored_S1_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h1 : e ≠ v1 m) (h2 : e ≠ v2 m) :
    coloredStep (hn3 hm) (st1 hm) e = .active (st1 hm) := by
  classical
  simp [coloredStep, st1, raw_S1_quiet hm e h1 h2,
    (S1_preContacts hm).1, (S1_preContacts hm).2]

theorem colored_S2_quiet {m : Nat} (hm : 1 ≤ m) (e : Fin (N m))
    (h0 : e ≠ v0 m) (h2 : e ≠ v2 m) :
    coloredStep (hn3 hm) (st2 hm) e = .active (st2 hm) := by
  classical
  simp [coloredStep, st2, raw_S2_quiet hm e h0 h2,
    (S2_preContacts hm).1, (S2_preContacts hm).2]

/-- Complete selected-edge classification at the initial live state. -/
theorem S0_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v0 m ∧ coloredStep (hn3 hm) (st0 hm) e = .active (st1 hm)) ∨
    (e = v2 m ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st0 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F0) ∨
    (e ≠ v0 m ∧ e ≠ v2 m ∧
      coloredStep (hn3 hm) (st0 hm) e = .active (st0 hm)) := by
  by_cases h0 : e = v0 m
  · left; subst e; exact ⟨rfl, colored_S0_zero hm⟩
  by_cases h2 : e = v2 m
  · right; left; subst e; exact ⟨rfl, colored_S0_two hm⟩
  exact Or.inr (Or.inr ⟨h0, h2, colored_S0_quiet hm e h0 h2⟩)

/-- Complete selected-edge classification after the rear probe is launched. -/
theorem S1_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v1 m ∧ coloredStep (hn3 hm) (st1 hm) e = .active (st2 hm)) ∨
    (e = v2 m ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st1 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F1) ∨
    (e ≠ v1 m ∧ e ≠ v2 m ∧
      coloredStep (hn3 hm) (st1 hm) e = .active (st1 hm)) := by
  by_cases h1 : e = v1 m
  · left; subst e; exact ⟨rfl, colored_S1_one hm⟩
  by_cases h2 : e = v2 m
  · right; left; subst e; exact ⟨rfl, colored_S1_two hm⟩
  exact Or.inr (Or.inr ⟨h1, h2, colored_S1_quiet hm e h1 h2⟩)

/-- Complete selected-edge classification immediately before contact. -/
theorem S2_child_partition {m : Nat} (hm : 1 ≤ m) (e : Fin (N m)) :
    (e = v0 m ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.contact ∧ p.config = H) ∨
    (e = v2 m ∧ ∃ p : TerminalPayload hk3 (ring m),
      coloredStep (hn3 hm) (st2 hm) e =
        PayloadFiniteStoppingTree.PayloadNode.success p ∧
      p.kind = TerminalKind.frontAdvance ∧ p.config = F2) ∨
    (e ≠ v0 m ∧ e ≠ v2 m ∧
      coloredStep (hn3 hm) (st2 hm) e = .active (st2 hm)) := by
  by_cases h0 : e = v0 m
  · left; subst e; exact ⟨rfl, colored_S2_zero hm⟩
  by_cases h2 : e = v2 m
  · right; left; subst e; exact ⟨rfl, colored_S2_two hm⟩
  exact Or.inr (Or.inr ⟨h0, h2, colored_S2_quiet hm e h0 h2⟩)

/-! ## The fixed continuation from the contact child -/

/-- The actual six scheduler selections used after reaching `H`. -/
def adjacentDropWord (m : Nat) : List (Fin (N m)) :=
  [v1 m, v2 m, v1 m, v2 m, v3 m, v2 m]

/-- The list presentation is definitionally the repository's literal
`[a,b,a,b,c,b]` service block. -/
theorem rawRun_adjacentDropWord {m : Nat} :
    OriginalNonbarrierWord.rawRun hk3 (ring m) H (adjacentDropWord m) =
      contactService6 hk3 (ring m) H (v1 m) (v2 m) := by
  simp only [adjacentDropWord, OriginalNonbarrierWord.rawRun,
    contactService6, contactService3]
  rw [rn_v2]

/-- The fixed six-interaction continuation strictly lowers the barrier count
from the concrete contact state `H`. -/
theorem adjacentDropWord_strict {m : Nat} (hm : 1 ≤ m) :
    barrierCount hk3 (ring m)
        (labelsOf
          (OriginalNonbarrierWord.rawRun hk3 (ring m) H
            (adjacentDropWord m))) <
      barrierCount hk3 (ring m) (labelsOf H) := by
  rw [rawRun_adjacentDropWord]
  exact OriginalFull3.six_hit_drops_of_exact_adjacent
    hk3 (ring m) (hn3 hm) H (v1 m) (v2 m) rn_v1 (H_support hm)

end AAFJPK.N6m4ColoredChildTable
