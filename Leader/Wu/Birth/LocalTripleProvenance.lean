import Leader.Wu.Birth.LocalTripleEntryNoGain
import Leader.Wu.Birth.IncreaseOrCapPhysicalFire
import Leader.Wu.Birth.ControlledReacquireContract


namespace BirthB1Local3Provenance


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthShortWaitProjection
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation
open BirthB1ReacquireReentryMass


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


private theorem prefixEndpoint_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u v : List (Fin n)) :
    prefixEndpoint hpsi h2 ring C (u ++ v) =
      prefixEndpoint hpsi h2 ring
        (prefixEndpoint hpsi h2 ring C u) v := by
  simp [prefixEndpoint, BirthPhaseGenericRenewal.rawEndpoint,
    List.foldl_append]


/-- One actual tracked p0 count fire.  The last strict inequality is the
new provenance datum; the preceding fields are its existing physical/raw
transport support. -/
def RawTrackedP0FireAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  exists S : Fin n -> AgentState 2,
    exists hl : (raw (C anchor)).label.val < 2,
    exists hr : (raw (C (ring.rightNeighbor anchor))).label.val < 2,
      RowProjection2 hpsi h2 kappa tau ring C anchor /\
      WaitKey.ofState (waitPrefixProject (raw (C anchor)) hl) =
        WaitKey.ofState (S (p0 hn)) /\
      WaitKey.ofState
          (waitPrefixProject
            (raw (C (ring.rightNeighbor anchor))) hr) =
        WaitKey.ofState (S (p1 hn)) /\
      (S (p1 hn)).count <
        (BirthWaitClockMass.RawRing.rawStep
          (w := 2) (n := n) (by omega : 2 < n)
          (by decide : 2 <= 2) kappa S
          (p0 hn) (p1 hn)).count


theorem rawTrackedP0FireAt_strict
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (h : RawTrackedP0FireAt
      hpsi h2 hn kappa tau ring anchor C) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2
          hpsi h2 ring C anchor) := by
  rcases h with ⟨S, hl, hr, hproj, hk0, hk1, hraw⟩
  exact BirthPhaseB3PhysicalFireIdentification.strictAnchorOfRawFire
    hpsi h2 hn kappa tau ring anchor C S
      hl hr hproj hk0 hk1 hraw


/-- The strengthened entry event remembers one counted physical anchor row
whose raw p0->p1 service really increments the tracked responder. -/
def TrackedP0FireWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (D : FC n psi kappa tau) (post : List (Fin n)) : Prop :=
  exists before tail,
    post = before ++ (anchor :: tail) /\
      RawTrackedP0FireAt hpsi h2 hn kappa tau ring anchor
        (prefixEndpoint hpsi h2 ring D before)


/-- Current counted entry arm plus the one missing service-fire witness. -/
def TrackedEntryEventAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (D : FC n psi kappa tau) (post : List (Fin n)) : Prop :=
  actualEventBitAt h2 hn kappa tau ring anchor D post = 1 /\
    (exists entryPre entryTail,
      post = entryPre ++ entryTail /\
        OrderedWaitEntry2At hn ring anchor
          (prefixEndpoint hpsi h2 ring D entryPre)) /\
    TrackedP0FireWithin
      hpsi h2 hn kappa tau ring anchor D post


/-- Provenance lemma: a strengthened counted entry exposes a literal prefix
ending in the tracked p0 row, and that row strictly increments shortCountAt. -/
theorem trackedEntryEvent_provenance
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (D : FC n psi kappa tau) (post : List (Fin n))
    (h : TrackedEntryEventAt
      hpsi h2 hn kappa tau ring anchor D post) :
    exists before tail,
      post = before ++ (anchor :: tail) /\
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
          (prefixEndpoint hpsi h2 ring D before) <
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring
            (prefixEndpoint hpsi h2 ring D before) anchor) := by
  rcases h.2.2 with ⟨before, tail, hpost, hfire⟩
  exact ⟨before, tail, hpost,
    rawTrackedP0FireAt_strict
      hpsi h2 hn kappa tau ring anchor _ hfire⟩


/-- C<=D is supplied at controlled entrance.  This is the weakest extra
prefix law needed afterward: from D to immediately before a certified tracked
p0 fire, the tracked count does not regress. -/
def ControlledExitPrefixNonRegression
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C ->
    forall entrance : List (Fin n),
      BirthPhaseWait2BlockProgress.target
        hpsi h2 kappa ring C entrance = false ->
      BirthB4ReacquireMonoDecision.ControlledEntranceSuccess
        hpsi h2 hn kappa tau ring anchor Controlled C entrance ->
      let D := prefixEndpoint hpsi h2 ring C entrance
      forall rest : List (Fin n),
        RawTrackedP0FireAt hpsi h2 hn kappa tau ring anchor
            (prefixEndpoint hpsi h2 ring D rest) ->
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor D <=
            BirthPhaseWait2BlockProgress.shortCountAt ring anchor
              (prefixEndpoint hpsi h2 ring D rest)


/-- Controlled entrance + prefix non-regression + tracked service provenance
is exactly the strict-count entry arm of Local3EventHitResolves. -/
theorem controlled_entry_arm_resolves
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (hnonreg : ControlledExitPrefixNonRegression
      hpsi h2 hn kappa tau ring anchor Controlled)
    (C : FC n psi kappa tau)
    (hR : BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C)
    (entrance exit post : List (Fin n))
    (htf : BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C entrance = false)
    (hent : BirthB4ReacquireMonoDecision.ControlledEntranceSuccess
      hpsi h2 hn kappa tau ring anchor Controlled C entrance)
    (hevent : TrackedEntryEventAt
      hpsi h2 hn kappa tau ring anchor
        (prefixEndpoint hpsi h2 ring C (entrance ++ exit)) post) :
    exists hit tail, post = hit ++ tail /\
      BirthPhaseB3ReacquireEvent.Resolves
        hpsi h2 kappa ring anchor C
          ((entrance ++ exit) ++ hit) := by
  let D := prefixEndpoint hpsi h2 ring C entrance
  have hc := hent
  unfold BirthB4ReacquireMonoDecision.ControlledEntranceSuccess at hc
  rw [htf] at hc
  simp only [Bool.false_eq_true, false_or] at hc
  change BirthB4ReacquireMonoDecision.ControlledReacquire
      hpsi h2 hn kappa tau ring anchor Controlled D /\
    BirthPhaseWait2BlockProgress.rank kappa ring anchor D <=
      BirthPhaseWait2BlockProgress.rank kappa ring anchor C at hc
  have hCD :=
    (BirthPhaseWait2BlockProgress.rank_le_iff_shortCount_le
      kappa ring anchor C D).1 hc.2
  rcases hevent.2.2 with ⟨before, tail, hpost, hfire⟩
  have hstate :
      prefixEndpoint hpsi h2 ring
          (prefixEndpoint hpsi h2 ring C (entrance ++ exit)) before =
        prefixEndpoint hpsi h2 ring D (exit ++ before) := by
    calc
      _ = prefixEndpoint hpsi h2 ring
          (prefixEndpoint hpsi h2 ring D exit) before := by
        rw [prefixEndpoint_append]
      _ = prefixEndpoint hpsi h2 ring D (exit ++ before) :=
        (prefixEndpoint_append hpsi h2 ring D exit before).symm
  have hfire' : RawTrackedP0FireAt
      hpsi h2 hn kappa tau ring anchor
        (prefixEndpoint hpsi h2 ring D (exit ++ before)) := by
    rw [← hstate]
    exact hfire
  have hDP := hnonreg C hR entrance htf hent
    (exit ++ before) hfire'
  have hstrict := rawTrackedP0FireAt_strict
    hpsi h2 hn kappa tau ring anchor _ hfire'
  have htotal := Nat.lt_of_le_of_lt (Nat.le_trans hCD hDP) hstrict
  refine ⟨before ++ [anchor], tail, ?_, ?_⟩
  · calc
      post = before ++ (anchor :: tail) := hpost
      _ = (before ++ [anchor]) ++ tail := by
        simp [List.append_assoc]
  · unfold BirthPhaseB3ReacquireEvent.Resolves
    right
    change BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (prefixEndpoint hpsi h2 ring C
          ((entrance ++ exit) ++ (before ++ [anchor])))
    have hend :
        prefixEndpoint hpsi h2 ring C
            ((entrance ++ exit) ++ (before ++ [anchor])) =
          BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring
            (prefixEndpoint hpsi h2 ring D (exit ++ before)) anchor := by
      rw [prefixEndpoint_append]
      rw [prefixEndpoint_append]
      rw [hstate]
      rfl
    rw [hend]
    exact htotal


end BirthB1Local3Provenance


#print axioms BirthB1Local3Provenance.rawTrackedP0FireAt_strict
#print axioms BirthB1Local3Provenance.trackedEntryEvent_provenance
#print axioms BirthB1Local3Provenance.controlled_entry_arm_resolves
