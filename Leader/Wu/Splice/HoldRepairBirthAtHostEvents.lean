import Leader.Wu.Splice.HoldRepairK2Observation
import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor

set_option autoImplicit false
set_option Elab.async false

/-! # Under V10j a leader is born only at a physical service with a host birth event

`stepV10j_birth_needs_event`: for every configuration and served edge, with or without leaders, if a cell that is
not a leader becomes a leader, then the service is physical and the host `birthEvent` of the served pair (on its
physical bases) is true.  Consequently, along a composed V10j run in which no physical service has a birth
event (`NoHostBirthAlongJ`), no cell ever becomes a leader (`leaders_antitone_of_noHostBirth`): the set of leaders
can only shrink.  This is the no-birth transfer from host events to the composed system. -/

namespace B9SpliceV10jBirthOnlyAtHostEvents

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency B9SpliceV10ePhysicalIsB7Step
  B9SpliceV10jRowProgress B9SpliceV10jProjection B9SpliceV10jK2Observation

variable {n psi width kappa tau : Nat}

/-- The K2 shadow row never creates a leader. -/
theorem shadowRow_no_creation (a b : AgentState 1) :
    ((K2BirthDispatcher.shadowRow a b).1.leader = true → a.leader = true) ∧
    ((K2BirthDispatcher.shadowRow a b).2.leader = true → b.leader = true) := by
  unfold K2BirthDispatcher.shadowRow
  dsimp only
  have hsa : (K2OutputSafety.signalView a).leader = a.leader := rfl
  have hsb : (K2OutputSafety.signalView b).leader = b.leader := rfl
  by_cases hboth : (K2OutputSafety.signalView a).leader = true ∧ (K2OutputSafety.signalView b).leader = true
  · rw [if_pos hboth]
    refine ⟨fun h => ?_, fun _ => hsb ▸ hboth.2⟩
    simp at h
  · rw [if_neg hboth]
    have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation (by decide : (1 : Nat) > 0)
      (K2OutputSafety.signalView a) (K2OutputSafety.signalView b)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases ha : a.leader
      · have := hk.1 (by rw [hsa, ha]); rw [this] at h; exact absurd h (by decide)
      · rfl
    · cases hb : b.leader
      · have := hk.2 (by rw [hsb, hb]); rw [this] at h; exact absurd h (by decide)
      · rfl

/-- Without a birth event the host row creates no leader. -/
theorem row_no_creation_of_no_birth (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hn : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle l r = false) :
    ((BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.leader = true → l.core.core.leader = true) ∧
    ((BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.leader = true → r.core.core.leader = true) := by
  have hobs := BirthShortDoneTerminalObserver.observe_row_of_no_birth hpsi hwidth hle l r hn
  have h1 := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.leader) hobs
  have h2 := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader) hobs
  simp only at h1 h2
  have hs := shadowRow_no_creation (ExpiringK2Projection.observeCell l) (ExpiringK2Projection.observeCell r)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have ho : (ExpiringK2Projection.observeCell (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1).leader = true := h
    rw [h1] at ho
    exact hs.1 ho
  · have ho : (ExpiringK2Projection.observeCell (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2).leader = true := h
    rw [h2] at ho
    exact hs.2 ho

theorem stepV10j_birth_needs_event (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (hbefore : (C i).carrier.splice.base.core.core.leader = false)
    (hafter : (stepV10j hpsi hwidth hle ring C e i).carrier.splice.base.core.core.leader = true) :
    PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e ∧
    BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = true := by
  classical
  by_cases hphys : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e
  · refine ⟨hphys, ?_⟩
    cases hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base
    · exfalso
      have hno := row_no_creation_of_no_birth hpsi hwidth hle _ _ hb
      have hp := hphys
      unfold PhysicalServiceAt at hp
      dsimp only at hp
      by_cases hie : i = e
      · subst hie
        rw [hp.1] at hafter
        have := hno.1 hafter
        rw [hbefore] at this
        exact absurd this (by decide)
      · by_cases hij : i = ring.rightNeighbor e
        · subst hij
          rw [hp.2] at hafter
          have := hno.2 hafter
          rw [hbefore] at this
          exact absurd this (by decide)
        · rw [stepV10j_other hpsi hwidth hle ring C e i hie hij, hbefore] at hafter
          exact absurd hafter (by decide)
    · rfl
  · exfalso
    have := stepV10j_leaders_of_not_physical hpsi hwidth hle ring C e hphys i
    rw [hafter, hbefore] at this
    exact absurd this (by decide)

/-- No physical service along the word has a host birth event. -/
def NoHostBirthAlongJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      (PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e →
        BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
          (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = false) ∧
      NoHostBirthAlongJ hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring C e) es

/-- Along such a word no cell becomes a leader. -/
theorem leaders_antitone_of_noHostBirth (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ (C : R1ConfigV6 n psi kappa tau), NoHostBirthAlongJ hpsi hwidth hle ring C w →
      ∀ i, (C i).carrier.splice.base.core.core.leader = false →
        ((w.foldl (stepV10j hpsi hwidth hle ring) C) i).carrier.splice.base.core.core.leader = false := by
  induction w with
  | nil => intro C _ i hi; exact hi
  | cons e w ih =>
      intro C hnb i hi
      apply ih _ hnb.2 i
      cases h : (stepV10j hpsi hwidth hle ring C e i).carrier.splice.base.core.core.leader
      · rfl
      · obtain ⟨hp, hb⟩ := stepV10j_birth_needs_event hpsi hwidth hle ring C e i hi h
        rw [hnb.1 hp] at hb
        exact absurd hb (by decide)

end B9SpliceV10jBirthOnlyAtHostEvents
