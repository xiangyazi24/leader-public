import Leader.Wu.Splice.HoldRepairFirstRow
import Leader.Wu.Splice.HoldRepairK2Observation

set_option autoImplicit false
set_option Elab.async false

/-! # V10j is the bare host while the controller is quiet

`neutral_row`: on a served pair of controller-neutral cells (role none, not pending, no ticket) whose left cell is not a
leader, if the host row does not relabel the right follower (`rightFollowerRelabelledV7` false), the V10j row is the
host row with neutral controllers.  `step_lift`: on the neutral lift of a bare host configuration the V10j service is
the neutral lift of the host step, under the same two conditions at the served pair.  `run_lift`: along a word on
which every service satisfies them (`QuietAlong`), the composed V10j run is the neutral lift of the bare host run,
letter by letter.  This is the regime of the slowest leaderless starts found by
`run/verification/probes/V10jWorstBirthKind.lean` (no prepared danger, no controller mark and no non-physical service
before the first birth, identical first-birth letters). -/

namespace B9SpliceV10jQuiescence

open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jRowProgress B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency B9SpliceV10ePhysicalIsB7Step

variable {n psi width kappa tau : Nat}

def Neutral (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .none ∧ u.carrier.repairPending = false ∧ u.acquireTicket = false

/-- The host write with neutral controllers. -/
def quietWrite (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  (⟨(ordinaryRow hpsi hwidth hle l.carrier r.carrier).1, false⟩,
    ⟨(ordinaryRow hpsi hwidth hle l.carrier r.carrier).2, false⟩)

theorem notRF_of_neutral (u : R1AgentStateV6 psi kappa tau) (h : Neutral u) : ¬ ReservedFrontHoldGuard u.carrier := by
  intro hc; have := hc.1; rw [h.1] at this; cases this

theorem physicalHold_quiet (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : Neutral l) (hr : Neutral r)
    (hrel : rightFollowerRelabelledV7 r.carrier (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 = false) :
    physicalHoldV6 hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r := by
  unfold physicalHoldV6 quietWrite
  dsimp only
  rw [hrel, if_neg (by decide), hl.2.2, hr.2.2]

theorem ordinaryHost_quiet (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hrel : rightFollowerRelabelledV7 r.carrier (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 = false) :
    ordinaryHostWriteV7 hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r := by
  unfold ordinaryHostWriteV7 quietWrite
  dsimp only
  rw [hrel, if_neg (by decide)]
  rfl

theorem rowV7_quiet (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : Neutral l) (hr : Neutral r)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hrel : rightFollowerRelabelledV7 r.carrier (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 = false) :
    rowV7 hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r := by
  classical
  have hlr := hl.1
  have hrr := hr.1
  have hfL : ¬ HostFenceShapeV7 l := fun h => by have := h.2.2; rw [hl.2.2] at this; cases this
  have hfR : ¬ HostFenceShapeV7 r := fun h => by have := h.2.2; rw [hr.2.2] at this; cases this
  have hRF := notRF_of_neutral r hr
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi l r := fun h => hRF h.2.2.2.1
  have hA : ¬ ArmAGuard hpsi hwidth hle l.carrier r.carrier := fun h => hdel h.2.2.2.2
  have hB : ¬ ArmBGuard l.carrier r.carrier := fun h => by have := h.2.2.1; rw [hrr] at this; cases this
  have hDel : ¬ DeleteGuard hpsi hwidth hle l.carrier r.carrier := fun h => hdel h.2.2.2.2
  have hPH : ¬ PendingHoldGuard hpsi hwidth hle l.carrier r.carrier := fun h => hdel h.2.2.2.2
  have hPA : ¬ PendingAbortGuard hpsi hwidth hle l.carrier r.carrier := fun h => by
    have := h.1; rw [hlr] at this; cases this
  have hMC : ¬ MoveCommitGuard l.carrier r.carrier := fun h => by have := h.1; rw [hlr] at this; cases this
  have hMS : ¬ MoveStopGuardV3 hpsi l.carrier r.carrier := fun h => by have := h.1; rw [hlr] at this; cases this
  have hSK : ¬ MoveSeekGuardV3 hpsi l.carrier r.carrier := fun h => by have := h.1; rw [hlr] at this; cases this
  have hSKH : ¬ MoveSeekHoldGuardV3 l.carrier r.carrier := fun h => by have := h.1; rw [hlr] at this; cases this
  have hPOA : ¬ PendingOwnerAbortGuardV3 l.carrier r.carrier := fun h => by
    have := h.1; rw [hrr] at this; cases this
  have hPP : ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) := fun h => by
    have := h.1; rw [hlr] at this; cases this
  have hMAL : ¬ MoveAcquireLegacyGuardV6 l r := fun h => hRF h.1.2.2.2
  have hMAA : ¬ MoveAcquireAbortGuardV3 l.carrier r.carrier := fun h => by
    have := h.1; rw [hlr] at this; cases this
  have hORF : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := fun h => hRF h.1
  have hRFH : ¬ ReservedFrontHoldGuard l.carrier := notRF_of_neutral l hl
  have hVR : ¬ VictimRightScrubGuardV6 r := fun h => by have := h.1; rw [hrr] at this; cases this
  have hVL : ¬ VictimLeftScrubGuardV6 l := fun h => by have := h.1; rw [hlr] at this; cases this
  have hFR : ¬ FrontRightScrubGuardV6 r := fun h => by have := h.1; rw [hrr] at this; cases this
  have hML : ¬ MalformedLeftPendingGuardV6 l := fun h => by have := h.1; rw [hl.2.1] at this; cases this
  have hMR : ¬ MalformedRightPendingGuardV6 r := fun h => by have := h.1; rw [hr.2.1] at this; cases this
  have hpl : ¬ role l.carrier = .predecessorArmed := by rw [hlr]; decide
  have hlf : ¬ role l.carrier = .front := by rw [hlr]; decide
  have hmk : ¬ MarkedHoldGuardV6 l r := by
    rintro (h | ⟨h, _⟩)
    · exact h hlr
    · exact h hrr
  rw [rowV7.eq_1, if_neg hfL, if_neg hfR, if_neg hmaf, if_neg hA, if_neg hB, if_neg hDel, if_neg hPH, if_neg hPA,
    if_neg hMC, if_neg hMS, if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL, if_neg hMAA, if_neg hORF,
    if_neg hRFH, if_neg hVR, if_neg hVL, if_neg hFR, if_neg hML, if_neg hMR, if_neg hpl, if_neg hlf, if_neg hmk]
  exact ordinaryHost_quiet hpsi hwidth hle l r hrel

theorem neutral_row (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : Neutral l) (hr : Neutral r)
    (hlead : l.carrier.splice.base.core.core.leader = false)
    (hrel : rightFollowerRelabelledV7 r.carrier (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 = false) :
    rowV10j hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r := by
  classical
  have hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice := fun h => by
    have := h.1; rw [hlead] at this; cases this
  have hRF := notRF_of_neutral r hr
  have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := fun h => hRF h.1
  have hD2 : ¬ OrphanVictimGuard l r := fun h => by have := h.1; rw [hr.1] at this; cases this
  have hD3 : ¬ OwnedPendingVictimGuard l r := fun h => by have := h.1; rw [hl.1] at this; cases this
  have hD4 : ¬ OwnerlessPendingPredGuard l r := fun h => by have := h.2.1; rw [hr.1] at this; cases this
  have hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r := fun h => by have := h.1.2.2; rw [hl.2.2] at this; cases this
  have hBF : ¬ HostFenceBusyFrontGuardV9 hpsi l r := fun h => by have := h.1.2.2; rw [hl.2.2] at this; cases this
  have hSP8 : ¬ RightStalePredecessorHoldGuardV8 l r := fun h => by
    have := h.2.2.2.1; rw [hr.1] at this; cases this
  have h7 := rowV7_quiet hpsi hwidth hle l r hl hr hdel hrel
  have hb : rowV10b hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r := by
    rw [rowV10b.eq_1, if_neg hHO, rowV9.eq_1, if_neg hBF, rowV8.eq_1, if_neg hSP8, h7]
  have hstut : physicalHoldV6 hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r :=
    physicalHold_quiet hpsi hwidth hle l r hl hr hrel
  have hc : rowV10c hpsi hwidth hle l r = (l, r) ∨ rowV10c hpsi hwidth hle l r = quietWrite hpsi hwidth hle l r := by
    rw [rowV10c.eq_1]
    by_cases hZR : ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r
    · rw [if_pos hZR]; exact Or.inl rfl
    · rw [if_neg hZR]; exact Or.inr hb
  have hdg : rowV10dg hpsi hwidth hle l r = rowV10c hpsi hwidth hle l r := by
    rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4]
  rw [rowV10j.eq_1, if_neg hdel]
  have hg := rowV10g.eq_1 hpsi hwidth hle l r
  dsimp only at hg
  rw [hg]
  by_cases hq : rowV10dg hpsi hwidth hle l r = (l, r)
  · rw [if_pos hq]
    have h0 : ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) := fun h => by
      have := h.1; rw [hl.1] at this; cases this
    have h1 : ¬ VictimRightScrubGuardV6 r := fun h => by have := h.1; rw [hr.1] at this; cases this
    have h2 : ¬ FrontRightScrubGuardV6 r := fun h => by have := h.1; rw [hr.1] at this; cases this
    have h3 : ¬ MalformedRightPendingGuardV6 r := fun h => by have := h.1; rw [hr.2.1] at this; cases this
    have h4 : ¬ role r.carrier = .predecessorArmed := by rw [hr.1]; decide
    rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    exact hstut
  · rw [if_neg hq, hdg]
    rcases hc with h | h
    · rw [hdg] at hq; exact absurd h hq
    · exact h

/-! ## Configurations -/

/-- A bare host configuration with every controller field neutral. -/
def lift (B : Fin n → ExpiringAgentState psi kappa tau) : R1ConfigV6 n psi kappa tau :=
  fun i => ⟨⟨⟨B i, .none⟩, false⟩, false⟩

/-- The two conditions of `neutral_row` at the served pair of a bare configuration. -/
def QuietAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (B : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) : Prop :=
  (B e).core.core.leader = false ∧
  rightFollowerRelabelledV7 (lift B (ring.rightNeighbor e)).carrier
    (ordinaryRow hpsi hwidth hle (lift B e).carrier (lift B (ring.rightNeighbor e)).carrier).2 = false

theorem eq_lift_cell (u : R1AgentStateV6 psi kappa tau) (h : Neutral u) :
    u = ⟨⟨⟨u.carrier.splice.base, .none⟩, false⟩, false⟩ := by
  obtain ⟨⟨⟨b, ro⟩, p⟩, t⟩ := u
  obtain ⟨h1, h2, h3⟩ := h
  change ro = .none at h1
  change p = false at h2
  change t = false at h3
  subst h1; subst h2; subst h3
  rfl

theorem step_lift (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) (hn : 2 ≤ n)
    (B : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) (hq : QuietAt hpsi hwidth hle ring B e) :
    stepV10j hpsi hwidth hle ring (lift B) e =
      lift (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring B e) := by
  classical
  have hself := B9SpliceV10jGlobalProgress.rightNeighbor_ne_of_two_le ring hn e
  have hrow := neutral_row hpsi hwidth hle (lift B e) (lift B (ring.rightNeighbor e)) ⟨rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl⟩ hq.1 hq.2
  have hstep : stepV10j hpsi hwidth hle ring (lift B) e =
      writeAt ring (lift B) e (quietWrite hpsi hwidth hle (lift B e) (lift B (ring.rightNeighbor e))) := by
    unfold stepV10j; rw [if_neg hself, hrow]
  rw [hstep]
  generalize hD : writeAt ring (lift B) e (quietWrite hpsi hwidth hle (lift B e) (lift B (ring.rightNeighbor e))) = D
  have hneu : ∀ i, Neutral (D i) := by
    intro i
    rw [← hD]
    by_cases hie : i = e
    · rw [hie, writeAt_e]; exact ⟨rfl, rfl, rfl⟩
    · by_cases hij : i = ring.rightNeighbor e
      · rw [hij, writeAt_j ring _ e _ hself]; exact ⟨rfl, rfl, rfl⟩
      · rw [writeAt_other ring _ e _ i hie hij]; exact ⟨rfl, rfl, rfl⟩
  have hphys : PhysicalServiceAt hpsi hwidth hle ring (lift B) D e := by
    rw [← hD]
    unfold PhysicalServiceAt
    dsimp only
    rw [writeAt_e, writeAt_j ring _ e _ hself]
    exact ⟨rfl, rfl⟩
  have hother : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → (D i).carrier.splice.base = (lift B i).carrier.splice.base := by
    intro i hie hij
    rw [← hD, writeAt_other ring _ e _ i hie hij]
  have hproj := physicalService_is_hostStep hpsi hwidth hle ring (lift B) D e hphys hother
  have hlift : D = lift (physicalProj D) := by
    funext i
    exact eq_lift_cell (D i) (hneu i)
  rw [hlift, hproj]
  rfl

/-- Every service of the word is quiet on the bare host run. -/
def QuietAlong (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    (Fin n → ExpiringAgentState psi kappa tau) → List (Fin n) → Prop
  | _, [] => True
  | B, e :: es => QuietAt hpsi hwidth hle ring B e ∧
      QuietAlong hpsi hwidth hle ring (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring B e) es

theorem run_lift (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) (hn : 2 ≤ n) :
    ∀ (w : List (Fin n)) (B : Fin n → ExpiringAgentState psi kappa tau), QuietAlong hpsi hwidth hle ring B w →
      w.foldl (stepV10j hpsi hwidth hle ring) (lift B) =
        lift (w.foldl (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring) B)
  | [], _, _ => rfl
  | e :: es, B, h => by
      show es.foldl (stepV10j hpsi hwidth hle ring) (stepV10j hpsi hwidth hle ring (lift B) e) =
        lift (es.foldl (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring)
          (BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring B e))
      rw [step_lift hpsi hwidth hle ring hn B e h.1]
      exact run_lift hpsi hwidth hle ring hn es _ h.2

end B9SpliceV10jQuiescence
