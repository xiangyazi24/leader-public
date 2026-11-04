import Leader.Wu.Splice.HoldRepairFollowUp

set_option autoImplicit false
set_option Elab.async false

/-! # V10j with-leader global progress

`globalProgressWithin3J`: on every ring of size at least two and from every `SpliceSafeV7g` configuration, with or
without leaders, some edge reaches a physical service or strictly lowers `controllerPotentialV6` within three
consecutive services of that edge.  The row theorem (`row_progress_or_hold`) gives progress or a stall shape on
each edge, and the stall shapes cannot cover the ring (`ring_not_all_hold`). -/

namespace B9SpliceV10jGlobalProgress

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j B9SpliceV10jHoldRing B9SpliceV10eRowPotential
  B9SpliceV10jRowProgress B9SpliceV10jFollowUp B9SpliceV10hControllerRowsSafe B9SpliceV10hWholeStepSafe
  B9SpliceV10eTransparency

variable {n psi width kappa tau : Nat}

/-- `m` consecutive V10j services of the same edge. -/
noncomputable def serveIterJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (e : Fin n) : Nat → R1ConfigV6 n psi kappa tau → R1ConfigV6 n psi kappa tau
  | 0, C => C
  | m + 1, C => stepV10j hpsi hwidth hle ring (serveIterJ hpsi hwidth hle ring e m C) e

theorem rightNeighbor_ne_of_two_le (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem writeAt_writeAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (p q : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) :
    writeAt ring (writeAt ring C e p) e q = writeAt ring C e q := by
  funext i
  unfold writeAt
  by_cases h1 : i = e
  · simp [h1]
  · by_cases h2 : i = ring.rightNeighbor e
    · simp [h1, h2]
    · simp [h1, h2]

theorem serveIterJ_eq (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e) :
    ∀ m, serveIterJ hpsi hwidth hle ring e m C =
      writeAt ring C e (iterRow hpsi hwidth hle m (C e, C (ring.rightNeighbor e))) := by
  intro m
  induction m with
  | zero => exact (writeAt_self ring C e).symm
  | succ m ih =>
      show stepV10j hpsi hwidth hle ring (serveIterJ hpsi hwidth hle ring e m C) e = _
      unfold stepV10j
      rw [if_neg hself, ih, writeAt_e, writeAt_j ring C e _ hself, writeAt_writeAt, iterRow_succ]

theorem physical_of_row (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (p q : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau)
    (h : PhysRow hpsi hwidth hle p.1 p.2 q) :
    PhysicalServiceAt hpsi hwidth hle ring (writeAt ring C e p) (writeAt ring C e q) e := by
  unfold PhysicalServiceAt
  dsimp only
  rw [writeAt_e, writeAt_e, writeAt_j ring C e p hself, writeAt_j ring C e q hself]
  exact h

theorem drop_of_row (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (q : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau)
    (h : wsum q < wsum (C e, C (ring.rightNeighbor e))) :
    controllerPotentialV6 (writeAt ring C e q) < controllerPotentialV6 C := by
  apply potential_drop_two ring C _ e (ring.rightNeighbor e) (Ne.symm hself)
  · intro i h1 h2; exact writeAt_other ring C e q i h1 h2
  · rw [writeAt_e, writeAt_j ring C e q hself]
    exact h

theorem globalProgressWithin3J (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hS : SpliceSafeV7g hpsi ring C) :
    ∃ e : Fin n, ∃ m, m < 3 ∧
      (PhysicalServiceAt hpsi hwidth hle ring
          (serveIterJ hpsi hwidth hle ring e m C) (serveIterJ hpsi hwidth hle ring e (m + 1) C) e ∨
        controllerPotentialV6 (serveIterJ hpsi hwidth hle ring e (m + 1) C) < controllerPotentialV6 C) := by
  classical
  let e0 : Fin n := ⟨0, by omega⟩
  apply Classical.byContradiction
  intro hno
  apply ring_not_all_hold ring C hS.2 e0
  intro x
  have hself := rightNeighbor_ne_of_two_le ring hn x
  rcases row_progress_or_hold hpsi hwidth hle (C x) (C (ring.rightNeighbor x)) (hS.2.1 x) (hS.2.1 _) with hp | hh
  · exfalso
    apply hno
    obtain ⟨m, hm, hpd⟩ := hp
    refine ⟨x, m, hm, ?_⟩
    rw [serveIterJ_eq hpsi hwidth hle ring C x hself m, serveIterJ_eq hpsi hwidth hle ring C x hself (m + 1)]
    rcases hpd with hph | hdr
    · exact Or.inl (physical_of_row hpsi hwidth hle ring C x hself _ _ hph)
    · exact Or.inr (drop_of_row ring C x hself _ hdr)
  · exact hh

end B9SpliceV10jGlobalProgress
