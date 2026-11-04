import Leader.Wu.Splice.GarbageCount
import Leader.Wu.Splice.ComposedEvents

set_option autoImplicit false

/-! # ShapeClear is preserved by every leaderless safe V10e service

`ShapeClear C` (no victim cell, every predecessor settled) is exactly `garbageCount C = 0`.
Since the garbage count never increases under a leaderless `SpliceSafeV7` service
(`B9SpliceGarbageCount.stepV10e_garbageCount_le`), `ShapeClear` is preserved. -/

namespace B9SpliceShapeClear

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10e B9SpliceGarbageCount B9SpliceComposedEvents

variable {n psi width kappa tau : Nat}

theorem garbage_eq_zero_iff (u : R1AgentStateV6 psi kappa tau) :
    garbage u = 0 ↔
      (role u.carrier ≠ .victimArmed ∧
        (role u.carrier = .predecessorArmed → u.carrier.repairPending = false)) := by
  unfold garbage
  constructor
  · intro h
    by_cases hg : role u.carrier = .victimArmed ∨
        (role u.carrier = .predecessorArmed ∧ u.carrier.repairPending = true)
    · rw [if_pos hg] at h
      exact absurd h (by decide)
    · refine ⟨fun hv => hg (Or.inl hv), fun hp => ?_⟩
      cases hpend : u.carrier.repairPending
      · rfl
      · exact absurd (Or.inr ⟨hp, hpend⟩) hg
  · intro h
    have hg : ¬ (role u.carrier = .victimArmed ∨
        (role u.carrier = .predecessorArmed ∧ u.carrier.repairPending = true)) := by
      intro hor
      rcases hor with hv | ⟨hp, hpend⟩
      · exact h.1 hv
      · rw [h.2 hp] at hpend
        exact absurd hpend (by decide)
    rw [if_neg hg]

theorem sum_ofFn_eq_zero_iff {m : Nat} (f : Fin m → Nat) :
    (List.ofFn f).sum = 0 ↔ ∀ i, f i = 0 := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero, List.sum_nil, true_iff]
    intro i
    exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons]
    constructor
    · intro h i
      have h0 : f 0 = 0 := by omega
      have hrest : (List.ofFn (fun j : Fin m => f j.succ)).sum = 0 := by omega
      refine Fin.cases h0 (fun j => ?_) i
      exact (ih (fun j : Fin m => f j.succ)).1 hrest j
    · intro h
      have h0 := h 0
      have hrest : (List.ofFn (fun j : Fin m => f j.succ)).sum = 0 :=
        (ih (fun j : Fin m => f j.succ)).2 (fun j => h j.succ)
      omega

theorem shapeClear_iff_garbageCount_zero (C : R1ConfigV6 n psi kappa tau) :
    ShapeClear C ↔ garbageCount C = 0 := by
  unfold garbageCount ShapeClear
  rw [sum_ofFn_eq_zero_iff]
  constructor
  · intro h i
    exact (garbage_eq_zero_iff (C i)).2 ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => ((garbage_eq_zero_iff (C i)).1 (h i)).1,
      fun i => ((garbage_eq_zero_iff (C i)).1 (h i)).2⟩

/-- ShapeClear is preserved by every leaderless `SpliceSafeV7` V10e service. -/
theorem stepV10e_preserves_shapeClear
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) (hSC : ShapeClear C) :
    ShapeClear (stepV10e hpsi hwidth hle ring C e) := by
  by_cases hne : ring.rightNeighbor e = e
  · rw [stepV10e_self hpsi hwidth hle ring C e hne]
    exact hSC
  · have hle' := stepV10e_garbageCount_le hpsi hwidth hle ring C e hne hlead hS
    have h0 := (shapeClear_iff_garbageCount_zero C).1 hSC
    exact (shapeClear_iff_garbageCount_zero _).2 (by omega)

end B9SpliceShapeClear
