import Leader.L3.Grant.DrainWarmStageMarks
import Leader.L3.Grant.DrainWarmQuota
import Leader.L3.Grant.DrainProducer

/-!
# The certified all-label warm and marked grant-drain stage

One original physical state has one
permanent ledger and at most one original warm certificate per identity.
Every edge advances the same source and both ghosts.  The subtype below
contains only reachable configurations with the inductively maintained
host soundness, warm/cold-mark alignment, and quota caps.

No independence of scheduler clocks is assumed, no grant is created by
a ghost, and no quota is restarted at the first cooling edge.
-/

namespace L3.GrantDrainEntrance

open Classical
open L3.GrantDrainShared
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The exact three persistent alignment obligations plus both global
quota caps, on one synchronized joint state.  An absent warm certificate
means the initial identity was cold or ungranted, not that the grant
necessarily retired. -/
def GrantDrainWarmCostAligned
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring) : Prop :=
  (∀ (i g : Fin n),
    (z.ledger.grantLabels i).host = some g →
      z.ledger.physical.grant g = true) ∧
  (∀ i : Fin n,
    match z.warm.warmLabels i with
    | none =>
        (z.ledger.grantLabels i).host ≠ none →
          (z.ledger.grantLabels i).mark ≠ .unmarked
    | some cert =>
        (cert.label.warm = true →
          cert.label.host = (z.ledger.grantLabels i).host) ∧
        (cert.label.warm = false →
          (z.ledger.grantLabels i).host ≠ none →
            (z.ledger.grantLabels i).mark ≠ .unmarked)) ∧
  (∀ (i : Fin n)
    (cert : GrantDrainWarmCertified (Scratch := Scratch) ring),
    z.warm.warmLabels i = some cert →
      grantDrainWarmCertifiedRank ring cert + 2 * n ≤ 8 * n) ∧
  (∀ i : Fin n, (z.ledger.grantLabels i).remaining ≤ 2 * n)

/-- Exact initial physical hosts are genuine old grants. -/
private theorem grantDrainWarmCostInitialHostSound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (y : GrantDrainState n Scratch) :
    ∀ (i g : Fin n),
      (grantDrainLedgerInitial ring y i).host = some g →
        y.grant g = true := by
  intro i g hh
  by_cases hg : y.grant i = true
  · have he : i = g := by
      simpa [grantDrainLedgerInitial, hg] using hh
    rw [← he]
    exact hg
  · have hf : y.grant i = false := by
      cases ht : y.grant i with
      | false => rfl
      | true => exact False.elim (hg ht)
    simp [grantDrainLedgerInitial, hf] at hh

/-- Every initially granted, nonwarm root already has the
C_native-observed weak/strong/terminal mark, including the held
and leader-hosted initial cases. -/
private theorem grantDrainWarmCostInitialPhase
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native) :
    ∀ i : Fin n,
      match (grantDrainWarmAllCertifiedEntrance
        ring hn y hC).warmLabels i with
      | none =>
          (grantDrainLedgerInitial ring y i).host ≠ none →
            (grantDrainLedgerInitial ring y i).mark ≠ .unmarked
      | some cert =>
          (cert.label.warm = true →
            cert.label.host =
              (grantDrainLedgerInitial ring y i).host) ∧
          (cert.label.warm = false →
            (grantDrainLedgerInitial ring y i).host ≠ none →
              (grantDrainLedgerInitial ring y i).mark ≠ .unmarked) := by
  intro i
  by_cases hi : grantDrainWarmAt y i = true ∧ y.grant i = true
  · simp only [grantDrainWarmAllCertifiedEntrance, dif_pos hi]
    constructor
    · intro _
      change some i = (grantDrainLedgerInitial ring y i).host
      simp [grantDrainLedgerInitial, hi.2]
    · intro hcold
      change true = false at hcold
      cases hcold
  · simp only [grantDrainWarmAllCertifiedEntrance, dif_neg hi]
    intro hlive
    by_cases hg : y.grant i = true
    · have hcold : grantDrainWarmAt y i = false := by
        cases hw : grantDrainWarmAt y i with
        | false => rfl
        | true => exact False.elim (hi ⟨hw, hg⟩)
      exact grantDrainWarmStageColdInitialMarked
        ring y i hC hg hcold
    · have hf : y.grant i = false := by
        cases ht : y.grant i with
        | false => rfl
        | true => exact False.elim (hg ht)
      simp [grantDrainLedgerInitial, hf] at hlive

/-- Six warm credits plus two locked credits have a true
8n cap at the original entrance, for EVERY present certificate. -/
private theorem grantDrainWarmCostInitialRankCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native) :
    ∀ (i : Fin n)
      (cert : GrantDrainWarmCertified (Scratch := Scratch) ring),
      (grantDrainWarmAllCertifiedEntrance
        ring hn y hC).warmLabels i = some cert →
      grantDrainWarmCertifiedRank ring cert + 2 * n ≤ 8 * n := by
  intro i cert hc
  by_cases hi : grantDrainWarmAt y i = true ∧ y.grant i = true
  · have he : cert =
        grantDrainWarmCertifiedEntrance
          ring hn y i hC hi.1 hi.2 := by
      simpa only [grantDrainWarmAllCertifiedEntrance, dif_pos hi,
        Option.some.injEq] using hc.symm
    rw [he]
    have hCap := grantDrainWarmCertifiedEntranceRankCap
      ring hn y i hC hi.1 hi.2
    omega
  · have hn : False := by
      simp only [grantDrainWarmAllCertifiedEntrance, dif_neg hi] at hc
      cases hc
    exact False.elim hn

/-- All four initial alignment facts follow from the same source
state and the originally allocated n immutable grant labels. -/
theorem grantDrainWarmCostAlignedInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native) :
    GrantDrainWarmCostAligned ring
      (grantDrainWarmStageJointInitial ring hn y hC) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact grantDrainWarmCostInitialHostSound ring y
  · exact grantDrainWarmCostInitialPhase ring hn y hC
  · exact grantDrainWarmCostInitialRankCap ring hn y hC
  · intro i
    exact grantDrainWarmQuotaLedgerCap ring y i


/-- Physical source grant soundness of every surviving ledger host is
inherited by the exact old-token source row. -/
private theorem grantDrainWarmCostSoundNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (hSound : ∀ (i g : Fin n),
      (z.ledger.grantLabels i).host = some g →
        z.ledger.physical.grant g = true)
    (e : Fin n) :
    ∀ (i g : Fin n),
      (grantDrainLedgerStep ring fresh update z.ledger.physical e
        (z.ledger.grantLabels i)).host = some g →
      (grantDrainStep ring fresh update z.ledger.physical e).grant g =
        true := by
  intro i g hNext
  have hOldLive :
      (z.ledger.grantLabels i).host ≠ none := by
    intro hNone
    have hRet := grantDrainLedgerStep_retired_absorbing
      ring fresh update z.ledger.physical e
      (z.ledger.grantLabels i) hNone
    rw [hRet] at hNext
    cases hNext
  cases hOldHost : (z.ledger.grantLabels i).host with
  | none =>
      exact False.elim (hOldLive hOldHost)
  | some p =>
      exact grantDrainWeakSurvivingHostGrant
        ring hn fresh update z.ledger.physical e
        (z.ledger.grantLabels i) p g
        hOldHost (hSound i p hOldHost) hNext

/-- If a new ledger host survives, its OLD immutable identity
was alive before the selected edge. -/
private theorem grantDrainWarmCostPreviousHost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hNext :
      (grantDrainLedgerStep ring fresh update s e label).host ≠ none) :
    label.host ≠ none := by
  intro hNone
  have hRet := grantDrainLedgerStep_retired_absorbing
    ring fresh update s e label hNone
  exact hNext hRet

/-- A certified warm origin is on the identical source physical
state as the persistent ledger label at that identity. -/
private theorem grantDrainWarmCostCertifiedPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (i : Fin n)
    (cert : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hCert : z.warm.warmLabels i = some cert) :
    cert.state = z.ledger.physical :=
  (z.warm.statesAgree i cert hCert).trans z.physicalEq

/-- All three possible progress modes:
  * initially absent certificate: inherited marked ledger;
  * still warm certificate: host/ledger transport on the SAME edge;
  * first cooling edge: surviving ledger becomes marked at once.
In the third case physical grant soundness supplies the post-state
grant required by the genuine cooling-mark theorem. -/
private theorem grantDrainWarmCostPhaseNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (hPhase :
      ∀ i : Fin n,
        match z.warm.warmLabels i with
        | none =>
            (z.ledger.grantLabels i).host ≠ none →
              (z.ledger.grantLabels i).mark ≠ .unmarked
        | some cert =>
            (cert.label.warm = true →
              cert.label.host = (z.ledger.grantLabels i).host) ∧
            (cert.label.warm = false →
              (z.ledger.grantLabels i).host ≠ none →
                (z.ledger.grantLabels i).mark ≠ .unmarked))
    (e : Fin n)
    (hSoundNext :
      ∀ (i g : Fin n),
        (grantDrainLedgerStep ring fresh update z.ledger.physical e
          (z.ledger.grantLabels i)).host = some g →
        (grantDrainStep ring fresh update z.ledger.physical e).grant g =
          true) :
    ∀ i : Fin n,
      match (grantDrainWarmStageJointNext
        ring hn fresh update z e).warm.warmLabels i with
      | none =>
          ((grantDrainWarmStageJointNext
            ring hn fresh update z e).ledger.grantLabels i).host ≠
              none →
          ((grantDrainWarmStageJointNext
            ring hn fresh update z e).ledger.grantLabels i).mark ≠
              .unmarked
      | some cert =>
          (cert.label.warm = true →
            cert.label.host =
              ((grantDrainWarmStageJointNext
                ring hn fresh update z e).ledger.grantLabels i).host) ∧
          (cert.label.warm = false →
            ((grantDrainWarmStageJointNext
              ring hn fresh update z e).ledger.grantLabels i).host ≠
                none →
            ((grantDrainWarmStageJointNext
              ring hn fresh update z e).ledger.grantLabels i).mark ≠
                .unmarked) := by
  intro i
  cases hOld : z.warm.warmLabels i with
  | none =>
      have hNextNone :
          (grantDrainWarmStageJointNext
            ring hn fresh update z e).warm.warmLabels i = none := by
        change (z.warm.warmLabels i).map
          (fun cert => grantDrainWarmCertifiedNext
            ring hn fresh update cert e) = none
        rw [hOld]
        rfl
      rw [hNextNone]
      change
        (grantDrainLedgerStep ring fresh update
          z.ledger.physical e (z.ledger.grantLabels i)).host ≠ none →
        (grantDrainLedgerStep ring fresh update
          z.ledger.physical e (z.ledger.grantLabels i)).mark ≠
            .unmarked
      intro hLive
      have hOldPhase := hPhase i
      simp only [hOld] at hOldPhase
      have hWasLive := grantDrainWarmCostPreviousHost
        ring fresh update z.ledger.physical e
        (z.ledger.grantLabels i) hLive
      exact grantDrainWarmStageMarkedPersists
        ring fresh update z.ledger.physical e
        (z.ledger.grantLabels i) (hOldPhase hWasLive)
  | some cert =>
      have hNextSome :
          (grantDrainWarmStageJointNext
            ring hn fresh update z e).warm.warmLabels i =
            some (grantDrainWarmCertifiedNext
              ring hn fresh update cert e) := by
        change (z.warm.warmLabels i).map
          (fun w => grantDrainWarmCertifiedNext
            ring hn fresh update w e) = _
        rw [hOld]
        rfl
      rw [hNextSome]
      change
        ((grantDrainWarmCertifiedNext ring hn fresh update cert e).label.warm =
            true →
          (grantDrainWarmCertifiedNext ring hn fresh update cert e).label.host =
            (grantDrainLedgerStep ring fresh update z.ledger.physical e
              (z.ledger.grantLabels i)).host) ∧
        ((grantDrainWarmCertifiedNext ring hn fresh update cert e).label.warm =
            false →
          (grantDrainLedgerStep ring fresh update z.ledger.physical e
            (z.ledger.grantLabels i)).host ≠ none →
          (grantDrainLedgerStep ring fresh update z.ledger.physical e
            (z.ledger.grantLabels i)).mark ≠ .unmarked)
      have hOldPhase := hPhase i
      simp only [hOld] at hOldPhase
      have hCertifiedState :=
        grantDrainWarmCostCertifiedPhysical ring z i cert hOld
      constructor
      · intro hNextWarm
        have hOldWarm : cert.label.warm = true :=
          grantDrainD6HostNextWarmOld
            ring fresh update cert.state e cert.label hNextWarm
        have hHostsOld := hOldPhase.1 hOldWarm
        have hReal :
            ∀ g : Fin n, cert.label.host = some g →
              cert.state.grant g = true := by
          intro g hg
          exact cert.coherent g hOldWarm hg
        have hStep :=
          grantDrainWarmQuotaHostStep
            ring fresh update cert.state e cert.label
            (z.ledger.grantLabels i) hHostsOld hReal
        have hNextLabel :
            (grantDrainWarmCertifiedNext ring hn fresh update cert e).label.host =
              (grantDrainWarmLabelStep ring fresh update cert.state e
                cert.label).host := rfl
        rw [hNextLabel, hCertifiedState]
        rw [hCertifiedState] at hStep
        exact hStep
      · intro hNextCold hLive
        cases hOldWarm : cert.label.warm with
        | false =>
            have hWasLive := grantDrainWarmCostPreviousHost
              ring fresh update z.ledger.physical e
              (z.ledger.grantLabels i) hLive
            exact grantDrainWarmStageMarkedPersists
              ring fresh update z.ledger.physical e
              (z.ledger.grantLabels i)
              (hOldPhase.2 hOldWarm hWasLive)
        | true =>
            have hHostsOld := hOldPhase.1 hOldWarm
            have hReal :
                ∀ g : Fin n, cert.label.host = some g →
                  cert.state.grant g = true := by
              intro g hg
              exact cert.coherent g hOldWarm hg
            have hStep :=
              grantDrainWarmQuotaHostStep
                ring fresh update cert.state e cert.label
                (z.ledger.grantLabels i) hHostsOld hReal
            rw [hCertifiedState] at hStep
            cases hNewHost :
                (grantDrainLedgerStep ring fresh update
                  z.ledger.physical e (z.ledger.grantLabels i)).host with
            | none =>
                exact False.elim (hLive hNewHost)
            | some g =>
                have hWarmNewHost :
                    (grantDrainWarmLabelStep ring fresh update
                      cert.state e cert.label).host = some g := by
                  rw [hCertifiedState]
                  exact hStep.trans hNewHost
                have hPostGrant :
                    (grantDrainStep ring fresh update cert.state e).grant
                      g = true := by
                  rw [hCertifiedState]
                  exact hSoundNext i g hNewHost
                have hNewCold :
                    (grantDrainWarmLabelStep ring fresh update
                      cert.state e cert.label).warm = false :=
                  hNextCold
                have hFirst := grantDrainWarmStageFirstCoolingMarked
                  ring hn fresh update cert.state e cert.label
                  (z.ledger.grantLabels i) g cert.clean
                  hOldWarm hHostsOld hReal hNewCold hWarmNewHost hPostGrant
                rw [hCertifiedState] at hFirst
                exact hFirst

/-- Every warm certificate's 6n rank cap is preserved by its
literal certified step, including the warm-to-cold edge. -/
private theorem grantDrainWarmCostRanksNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (hCaps :
      ∀ (i : Fin n)
        (cert : GrantDrainWarmCertified (Scratch := Scratch) ring),
        z.warm.warmLabels i = some cert →
          grantDrainWarmCertifiedRank ring cert + 2 * n ≤ 8 * n)
    (e : Fin n) :
    ∀ (i : Fin n)
      (cert : GrantDrainWarmCertified (Scratch := Scratch) ring),
      (grantDrainWarmStageJointNext
        ring hn fresh update z e).warm.warmLabels i = some cert →
        grantDrainWarmCertifiedRank ring cert + 2 * n ≤ 8 * n := by
  intro i cert hc
  cases hOld : z.warm.warmLabels i with
  | none =>
      have hNone :
          (grantDrainWarmStageJointNext
            ring hn fresh update z e).warm.warmLabels i = none := by
        change (z.warm.warmLabels i).map
          (fun w => grantDrainWarmCertifiedNext
            ring hn fresh update w e) = none
        rw [hOld]
        rfl
      rw [hNone] at hc
      cases hc
  | some old =>
      have hNew :
          cert = grantDrainWarmCertifiedNext
            ring hn fresh update old e := by
        change (z.warm.warmLabels i).map
          (fun w => grantDrainWarmCertifiedNext
            ring hn fresh update w e) = some cert at hc
        rw [hOld] at hc
        exact (Option.some.inj hc).symm
      rw [hNew]
      have hCap := hCaps i old hOld
      have hDrop :=
        grantDrainWarmCertifiedRankNonincrease
          ring hn fresh update old e
      omega

/-- All source alignment invariants are genuinely closed under the
same chosen scheduler letter; there is no post-cut quota reset. -/
theorem grantDrainWarmCostAlignedNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (e : Fin n)
    (h : GrantDrainWarmCostAligned ring z) :
    GrantDrainWarmCostAligned ring
      (grantDrainWarmStageJointNext ring hn fresh update z e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact grantDrainWarmCostSoundNext
      ring hn fresh update z h.1 e
  · exact grantDrainWarmCostPhaseNext
      ring hn fresh update z h.2.1 e
      (grantDrainWarmCostSoundNext ring hn fresh update z h.1 e)
  · exact grantDrainWarmCostRanksNext
      ring hn fresh update z h.2.2.1 e
  · intro i
    change (grantDrainLedgerStep ring fresh update
      z.ledger.physical e (z.ledger.grantLabels i)).remaining ≤ 2 * n
    exact grantDrainLedgerStep_quota_le_double
      ring fresh update z.ledger.physical e (z.ledger.grantLabels i)


/-- Every genuinely reachable joint state satisfies the closed
alignment certificates. No arbitrary off-trajectory ghost is used. -/
theorem grantDrainWarmCostAlignedOfReachable
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmStageJoint (Scratch := Scratch) ring)
    (hReach :
      GrantDrainBranchReachable
        (grantDrainWarmStageJointNext ring hn fresh update)
        (grantDrainWarmStageJointInitial ring hn y hC) z) :
    GrantDrainWarmCostAligned ring z := by
  obtain ⟨word, hWord⟩ := hReach
  have hRun :
      ∀ (w : List (Fin n))
        (v : GrantDrainWarmStageJoint (Scratch := Scratch) ring),
        GrantDrainWarmCostAligned ring v →
        GrantDrainWarmCostAligned ring
          (w.foldl (grantDrainWarmStageJointNext
            ring hn fresh update) v) := by
    intro w
    induction w with
    | nil =>
        intro v hv
        exact hv
    | cons e rest ih =>
        intro v hv
        exact ih
          (grantDrainWarmStageJointNext ring hn fresh update v e)
          (grantDrainWarmCostAlignedNext
            ring hn fresh update v e hv)
  rw [hWord]
  exact hRun word (grantDrainWarmStageJointInitial ring hn y hC)
    (grantDrainWarmCostAlignedInitial ring hn y hC)

/-- The real reachable carrier used by the generic n-label tail. -/
abbrev GrantDrainWarmCostCarrier
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native) : Type :=
  { z : GrantDrainWarmStageJoint (Scratch := Scratch) ring //
    GrantDrainBranchReachable
      (grantDrainWarmStageJointNext ring hn fresh update)
      (grantDrainWarmStageJointInitial ring hn y hC) z }

/-- A reachable prefix advances all n labels on exactly the same
physical edge. The reachable proof prevents fabricated ghost inputs. -/
noncomputable def grantDrainWarmCostNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (e : Fin n) :
    GrantDrainWarmCostCarrier ring hn fresh update y hC := by
  refine ⟨grantDrainWarmStageJointNext
    ring hn fresh update z.val e, ?_⟩
  exact grantDrainBranchReachableStep
    (grantDrainWarmStageJointNext ring hn fresh update)
    (grantDrainWarmStageJointInitial ring hn y hC)
    z.val e z.property

/-- Initial state, with no arbitrary prehistory and no reset. -/
noncomputable def grantDrainWarmCostInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native) :
    GrantDrainWarmCostCarrier ring hn fresh update y hC := by
  refine ⟨grantDrainWarmStageJointInitial ring hn y hC, ?_⟩
  exact grantDrainBranchReachableInitial
    (grantDrainWarmStageJointNext ring hn fresh update)
    (grantDrainWarmStageJointInitial ring hn y hC)

/-- The closed invariants available at every such reachable state. -/
private theorem grantDrainWarmCostCarrierAligned
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC) :
    GrantDrainWarmCostAligned ring z.val :=
  grantDrainWarmCostAlignedOfReachable
    ring hn fresh update y hC z.val z.property


/-- At EVERY reachable prefix, an actually warm certificate has the
same immutable host as the full-label ancestry and the old ledger.
In particular coalescence does not manufacture a new certificate. -/
theorem grantDrainWarmCostLiveFullHostEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (word : List (Fin n))
    (hWord : z.val =
      grantDrainWarmStageJointRun ring hn fresh update
        (grantDrainWarmStageJointInitial ring hn y hC) word)
    (i : Fin n)
    (cert : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hPresent : z.val.warm.warmLabels i = some cert)
    (hWarm : cert.label.warm = true) :
    cert.label.host =
      (sharedGrantFaithfulGhost ring hn fresh update y).grantHost
        i word.reverse := by
  have hAligned := grantDrainWarmCostCarrierAligned
    ring hn fresh update y hC z
  have hPhase := hAligned.2.1 i
  simp only [hPresent] at hPhase
  have hSource := hPhase.1 hWarm
  have hLedger :
      z.val.ledger =
        grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring y) word := by
    rw [hWord]
    exact grantDrainWarmStageJointLedgerWord
      ring hn fresh update word
      (grantDrainWarmStageJointInitial ring hn y hC)
  rw [hLedger] at hSource
  exact hSource.trans
    (sharedGrantFaithfulMarkFullHostEq
      ring hn fresh update y word i).symm

/-- A retired source label contributes exactly zero; no forged
unmarked remaining field is interpreted as a surviving quota. -/
def grantDrainWarmCostLedgerQuota
    {n : Nat} (label : GrantDrainLedgerLabel n) : Nat :=
  if label.host = none then 0 else label.remaining

/-- One unified quota per ORIGINAL identity: warm rank plus 2n
if warm, persistent ledger remaining after cooling, and zero
after retirement or when the initial certificate was absent. -/
def grantDrainWarmCostQuota
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (i : Fin n)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC) : Nat :=
  match z.val.warm.warmLabels i with
  | none => grantDrainWarmCostLedgerQuota (z.val.ledger.grantLabels i)
  | some cert =>
      grantDrainWarmStageCombinedQuota ring cert
        (z.val.ledger.grantLabels i)

/-- The scheduler letter is selected predictably using the OLD
current label state, never future information. -/
def grantDrainWarmCostChosen
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (i : Fin n)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC) : Fin n :=
  match z.val.warm.warmLabels i with
  | none =>
      grantDrainWarmStageColdChosen ring
        z.val.ledger.physical (z.val.ledger.grantLabels i)
  | some cert =>
      if cert.label.warm then grantDrainWarmCertifiedChosen ring cert
      else grantDrainWarmStageColdChosen ring
        z.val.ledger.physical (z.val.ledger.grantLabels i)

/-- The raw ledger contribution is at most its remaining counter,
whether retired or still hosted. -/
private theorem grantDrainWarmCostLedgerQuotaLeRemaining
    {n : Nat} (label : GrantDrainLedgerLabel n) :
    grantDrainWarmCostLedgerQuota label ≤ label.remaining := by
  unfold grantDrainWarmCostLedgerQuota
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- Cold, already-marked ledger quotas are pathwise nonincreasing,
even when their host retires on the selected edge. -/
private theorem grantDrainWarmCostLedgerMono
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (e : Fin n)
    (hMarked : label.host ≠ none → label.mark ≠ .unmarked) :
    grantDrainWarmCostLedgerQuota
      (grantDrainLedgerStep ring fresh update s e label) ≤
    grantDrainWarmCostLedgerQuota label := by
  cases hHost : label.host with
  | none =>
      have hRet := grantDrainLedgerStep_retired_absorbing
        ring fresh update s e label hHost
      simp [grantDrainWarmCostLedgerQuota, hHost, hRet]
  | some g =>
      have hLive : label.host ≠ none := by
        rw [hHost]
        intro hh
        cases hh
      have hOldMark := hMarked hLive
      have hDec := grantDrainLedgerStep_remaining_nonincrease
        ring fresh update s e label hOldMark
      have hNext := grantDrainWarmCostLedgerQuotaLeRemaining
        (grantDrainLedgerStep ring fresh update s e label)
      have hOld :
          grantDrainWarmCostLedgerQuota label = label.remaining := by
        simp [grantDrainWarmCostLedgerQuota, hHost]
      rw [hOld]
      exact Nat.le_trans hNext hDec

/-- A live marked label loses at least one remaining unit on its
OLD nominated edge, including weak marks and final retirement. -/
private theorem grantDrainWarmCostHitSpent
    (n : Nat) (label : GrantDrainLedgerLabel n)
    (newHost : Option (Fin n)) (newMark : GrantDrainMark)
    (held : Bool)
    (hMarked : label.mark ≠ .unmarked) :
    grantDrainLedgerRemainingNext n label
      newHost newMark true held ≤ label.remaining - 1 := by
  cases newHost with
  | none =>
      simp [grantDrainLedgerRemainingNext]
  | some g =>
      change min
        (if label.mark = .unmarked then
          grantDrainLedgerQuotaCap n newMark held
         else label.remaining - 1)
        (grantDrainLedgerQuotaCap n newMark held) ≤
          label.remaining - 1
      rw [if_neg hMarked]
      exact Nat.min_le_left _ _

/-- The cold ledger branch pays one unit on its predictable chosen
edge, without a separate warm certificate. -/
private theorem grantDrainWarmCostLedgerChosenDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (hMarked : label.host ≠ none → label.mark ≠ .unmarked)
    (hPositive : 0 < grantDrainWarmCostLedgerQuota label) :
    grantDrainWarmCostLedgerQuota
      (grantDrainLedgerStep ring fresh update s
        (grantDrainWarmStageColdChosen ring s label) label) + 1 ≤
    grantDrainWarmCostLedgerQuota label := by
  cases hHost : label.host with
  | none =>
      have hz : grantDrainWarmCostLedgerQuota label = 0 := by
        simp [grantDrainWarmCostLedgerQuota, hHost]
      rw [hz] at hPositive
      omega
  | some g =>
      have hLive : label.host ≠ none := by
        rw [hHost]
        intro hh
        cases hh
      have hHit := grantDrainWarmStageColdChosenHits
        ring hn s label g hHost
      have hSpent :
          (grantDrainLedgerStep ring fresh update s
            (grantDrainWarmStageColdChosen ring s label) label).remaining ≤
          label.remaining - 1 := by
        change grantDrainLedgerRemainingNext n label
          (grantDrainLedgerHost ring fresh s
            (grantDrainWarmStageColdChosen ring s label) label.host)
          (grantDrainLedgerMarkNext ring fresh update s
            (grantDrainWarmStageColdChosen ring s label) label)
          (grantDrainLedgerNominatedHit ring s
            (grantDrainWarmStageColdChosen ring s label) label.host)
          (grantDrainLedgerHeld
            (grantDrainStep ring fresh update s
              (grantDrainWarmStageColdChosen ring s label))
            (grantDrainLedgerHost ring fresh s
              (grantDrainWarmStageColdChosen ring s label) label.host)) ≤
          label.remaining - 1
        rw [hHit]
        exact grantDrainWarmCostHitSpent n label _ _ _ (hMarked hLive)
      have hNext := grantDrainWarmCostLedgerQuotaLeRemaining
        (grantDrainLedgerStep ring fresh update s
          (grantDrainWarmStageColdChosen ring s label) label)
      have hOld :
          grantDrainWarmCostLedgerQuota label = label.remaining := by
        simp [grantDrainWarmCostLedgerQuota, hHost]
      have hOldPositive : 0 < label.remaining := by
        rw [hOld] at hPositive
        exact hPositive
      rw [hOld]
      omega


/-- Every reachable original identity has a nonincreasing combined
quota on EVERY selected edge. There is no reset at first cooling. -/
theorem grantDrainWarmCostQuotaNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (i e : Fin n) :
    grantDrainWarmCostQuota ring hn fresh update y hC i
      (grantDrainWarmCostNext ring hn fresh update y hC z e) ≤
    grantDrainWarmCostQuota ring hn fresh update y hC i z := by
  have hAligned := grantDrainWarmCostCarrierAligned
    ring hn fresh update y hC z
  have hPhase := hAligned.2.1 i
  cases hw : z.val.warm.warmLabels i with
  | none =>
      have hNextNone :
          (grantDrainWarmCostNext
            ring hn fresh update y hC z e).val.warm.warmLabels i =
            none := by
        change (z.val.warm.warmLabels i).map
          (fun w => grantDrainWarmCertifiedNext
            ring hn fresh update w e) = none
        rw [hw]
        rfl
      change
        (match (grantDrainWarmCostNext
          ring hn fresh update y hC z e).val.warm.warmLabels i with
         | none => grantDrainWarmCostLedgerQuota
             ((grantDrainWarmCostNext
               ring hn fresh update y hC z e).val.ledger.grantLabels i)
         | some cert => grantDrainWarmStageCombinedQuota ring cert
             ((grantDrainWarmCostNext
               ring hn fresh update y hC z e).val.ledger.grantLabels i)) ≤
        (match z.val.warm.warmLabels i with
         | none => grantDrainWarmCostLedgerQuota
             (z.val.ledger.grantLabels i)
         | some cert => grantDrainWarmStageCombinedQuota ring cert
             (z.val.ledger.grantLabels i))
      rw [hNextNone, hw]
      change grantDrainWarmCostLedgerQuota
          (grantDrainLedgerStep ring fresh update
            z.val.ledger.physical e (z.val.ledger.grantLabels i)) ≤
        grantDrainWarmCostLedgerQuota (z.val.ledger.grantLabels i)
      simp only [hw] at hPhase
      exact grantDrainWarmCostLedgerMono
        ring fresh update z.val.ledger.physical
        (z.val.ledger.grantLabels i) e hPhase
  | some cert =>
      have hNextSome :
          (grantDrainWarmCostNext
            ring hn fresh update y hC z e).val.warm.warmLabels i =
            some (grantDrainWarmCertifiedNext
              ring hn fresh update cert e) := by
        change (z.val.warm.warmLabels i).map
          (fun w => grantDrainWarmCertifiedNext
            ring hn fresh update w e) = _
        rw [hw]
        rfl
      change
        (match (grantDrainWarmCostNext
          ring hn fresh update y hC z e).val.warm.warmLabels i with
         | none => grantDrainWarmCostLedgerQuota
             ((grantDrainWarmCostNext
               ring hn fresh update y hC z e).val.ledger.grantLabels i)
         | some w => grantDrainWarmStageCombinedQuota ring w
             ((grantDrainWarmCostNext
               ring hn fresh update y hC z e).val.ledger.grantLabels i)) ≤
        (match z.val.warm.warmLabels i with
         | none => grantDrainWarmCostLedgerQuota
             (z.val.ledger.grantLabels i)
         | some w => grantDrainWarmStageCombinedQuota ring w
             (z.val.ledger.grantLabels i))
      rw [hNextSome, hw]
      change
        grantDrainWarmStageCombinedQuota ring
          (grantDrainWarmCertifiedNext ring hn fresh update cert e)
          (grantDrainLedgerStep ring fresh update
            z.val.ledger.physical e (z.val.ledger.grantLabels i)) ≤
        grantDrainWarmStageCombinedQuota ring cert
          (z.val.ledger.grantLabels i)
      have hState := grantDrainWarmCostCertifiedPhysical
        ring z.val i cert hw
      rw [← hState]
      simp only [hw] at hPhase
      cases hWarm : cert.label.warm with
      | true =>
          exact grantDrainWarmStageActiveNonincrease
            ring hn fresh update cert
            (z.val.ledger.grantLabels i) e hWarm
      | false =>
          exact grantDrainWarmStageColdMarkedNonincrease
            ring hn fresh update cert
            (z.val.ledger.grantLabels i) e hWarm
            (hPhase.2 hWarm)

/-- A live original label has a predictable nominated edge; its
combined warm-or-marked quota drops strictly there, even for WEAK. -/
theorem grantDrainWarmCostQuotaDrop
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (i : Fin n)
    (hp : 0 < grantDrainWarmCostQuota
      ring hn fresh update y hC i z) :
    grantDrainWarmCostQuota ring hn fresh update y hC i
      (grantDrainWarmCostNext ring hn fresh update y hC z
        (grantDrainWarmCostChosen ring hn fresh update y hC i z)) +
        1 ≤
    grantDrainWarmCostQuota ring hn fresh update y hC i z := by
  have hAligned := grantDrainWarmCostCarrierAligned
    ring hn fresh update y hC z
  have hPhase := hAligned.2.1 i
  cases hw : z.val.warm.warmLabels i with
  | none =>
      have hChosen :
          grantDrainWarmCostChosen ring hn fresh update y hC i z =
          grantDrainWarmStageColdChosen ring z.val.ledger.physical
            (z.val.ledger.grantLabels i) := by
        simp [grantDrainWarmCostChosen, hw]
      have hNextNone :
          (grantDrainWarmCostNext ring hn fresh update y hC z
            (grantDrainWarmCostChosen
              ring hn fresh update y hC i z)).val.warm.warmLabels i =
                none := by
        change (z.val.warm.warmLabels i).map
          (fun w => grantDrainWarmCertifiedNext ring hn fresh update w
            (grantDrainWarmCostChosen ring hn fresh update y hC i z)) =
              none
        rw [hw]
        rfl
      have hPositive :
          0 < grantDrainWarmCostLedgerQuota
            (z.val.ledger.grantLabels i) := by
        simpa [grantDrainWarmCostQuota, hw] using hp
      simp only [hw] at hPhase
      change
        (match (grantDrainWarmCostNext ring hn fresh update y hC z
            (grantDrainWarmCostChosen
              ring hn fresh update y hC i z)).val.warm.warmLabels i with
         | none => grantDrainWarmCostLedgerQuota
             ((grantDrainWarmCostNext ring hn fresh update y hC z
               (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.ledger.grantLabels i)
         | some w => grantDrainWarmStageCombinedQuota ring w
             ((grantDrainWarmCostNext ring hn fresh update y hC z
               (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.ledger.grantLabels i)) +
               1 ≤
        (match z.val.warm.warmLabels i with
         | none => grantDrainWarmCostLedgerQuota (z.val.ledger.grantLabels i)
         | some w => grantDrainWarmStageCombinedQuota ring w
             (z.val.ledger.grantLabels i))
      rw [hNextNone, hw]
      change grantDrainWarmCostLedgerQuota
          (grantDrainLedgerStep ring fresh update z.val.ledger.physical
            (grantDrainWarmCostChosen ring hn fresh update y hC i z)
            (z.val.ledger.grantLabels i)) + 1 ≤
        grantDrainWarmCostLedgerQuota (z.val.ledger.grantLabels i)
      rw [hChosen]
      exact grantDrainWarmCostLedgerChosenDrop
        ring hn fresh update z.val.ledger.physical
        (z.val.ledger.grantLabels i) hPhase hPositive
  | some cert =>
      simp only [hw] at hPhase
      have hState := grantDrainWarmCostCertifiedPhysical
        ring z.val i cert hw
      cases hWarm : cert.label.warm with
      | true =>
          have hEdge :
              grantDrainWarmCostChosen ring hn fresh update y hC i z =
                grantDrainWarmCertifiedChosen ring cert := by
            simp [grantDrainWarmCostChosen, hw, hWarm]
          have hNextSome :
              (grantDrainWarmCostNext ring hn fresh update y hC z
                (grantDrainWarmCostChosen
                  ring hn fresh update y hC i z)).val.warm.warmLabels i =
                some (grantDrainWarmCertifiedNext
                  ring hn fresh update cert
                  (grantDrainWarmCertifiedChosen ring cert)) := by
            change (z.val.warm.warmLabels i).map
              (fun w => grantDrainWarmCertifiedNext ring hn fresh update w
                (grantDrainWarmCostChosen ring hn fresh update y hC i z)) = _
            rw [hw, hEdge]
            rfl
          have hPositive :
              0 < grantDrainWarmStageCombinedQuota
                ring cert (z.val.ledger.grantLabels i) := by
            simpa [grantDrainWarmCostQuota, hw] using hp
          change
            (match (grantDrainWarmCostNext ring hn fresh update y hC z
              (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.warm.warmLabels i with
             | none => grantDrainWarmCostLedgerQuota
               ((grantDrainWarmCostNext ring hn fresh update y hC z
                 (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.ledger.grantLabels i)
             | some w => grantDrainWarmStageCombinedQuota ring w
               ((grantDrainWarmCostNext ring hn fresh update y hC z
                 (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.ledger.grantLabels i)) +
              1 ≤
            (match z.val.warm.warmLabels i with
             | none => grantDrainWarmCostLedgerQuota (z.val.ledger.grantLabels i)
             | some w => grantDrainWarmStageCombinedQuota ring w (z.val.ledger.grantLabels i))
          rw [hNextSome, hw]
          change grantDrainWarmStageCombinedQuota ring
              (grantDrainWarmCertifiedNext ring hn fresh update cert
                (grantDrainWarmCertifiedChosen ring cert))
              (grantDrainLedgerStep ring fresh update z.val.ledger.physical
                (grantDrainWarmCostChosen ring hn fresh update y hC i z)
                (z.val.ledger.grantLabels i)) + 1 ≤
            grantDrainWarmStageCombinedQuota ring cert (z.val.ledger.grantLabels i)
          rw [hEdge, ← hState]
          exact grantDrainWarmStageActiveChosenDrop
            ring hn fresh update cert (z.val.ledger.grantLabels i) hWarm
      | false =>
          have hEdge :
              grantDrainWarmCostChosen ring hn fresh update y hC i z =
                grantDrainWarmStageColdChosen ring z.val.ledger.physical
                  (z.val.ledger.grantLabels i) := by
            simp [grantDrainWarmCostChosen, hw, hWarm]
          have hNextSome :
              (grantDrainWarmCostNext ring hn fresh update y hC z
                (grantDrainWarmCostChosen
                  ring hn fresh update y hC i z)).val.warm.warmLabels i =
                some (grantDrainWarmCertifiedNext ring hn fresh update cert
                  (grantDrainWarmStageColdChosen ring z.val.ledger.physical
                    (z.val.ledger.grantLabels i))) := by
            change (z.val.warm.warmLabels i).map
              (fun w => grantDrainWarmCertifiedNext ring hn fresh update w
                (grantDrainWarmCostChosen ring hn fresh update y hC i z)) = _
            rw [hw, hEdge]
            rfl
          have hPositive :
              0 < grantDrainWarmStageCombinedQuota
                ring cert (z.val.ledger.grantLabels i) := by
            simpa [grantDrainWarmCostQuota, hw] using hp
          change
            (match (grantDrainWarmCostNext ring hn fresh update y hC z
              (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.warm.warmLabels i with
             | none => grantDrainWarmCostLedgerQuota
               ((grantDrainWarmCostNext ring hn fresh update y hC z
                 (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.ledger.grantLabels i)
             | some w => grantDrainWarmStageCombinedQuota ring w
               ((grantDrainWarmCostNext ring hn fresh update y hC z
                 (grantDrainWarmCostChosen ring hn fresh update y hC i z)).val.ledger.grantLabels i)) +
              1 ≤
            (match z.val.warm.warmLabels i with
             | none => grantDrainWarmCostLedgerQuota (z.val.ledger.grantLabels i)
             | some w => grantDrainWarmStageCombinedQuota ring w (z.val.ledger.grantLabels i))
          rw [hNextSome, hw]
          change grantDrainWarmStageCombinedQuota ring
              (grantDrainWarmCertifiedNext ring hn fresh update cert
                (grantDrainWarmStageColdChosen ring z.val.ledger.physical
                  (z.val.ledger.grantLabels i)))
              (grantDrainLedgerStep ring fresh update z.val.ledger.physical
                (grantDrainWarmCostChosen ring hn fresh update y hC i z)
                (z.val.ledger.grantLabels i)) + 1 ≤
            grantDrainWarmStageCombinedQuota ring cert (z.val.ledger.grantLabels i)
          rw [hEdge, ← hState]
          exact grantDrainWarmStageColdMarkedChosenDrop
            ring hn fresh update cert (z.val.ledger.grantLabels i)
            hWarm (hPhase.2 hWarm) hPositive

/-- The global 8n bound holds for every original identity at
every reachable joint state, including initially untracked cold grants. -/
theorem grantDrainWarmCostQuotaBound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (i : Fin n) :
    grantDrainWarmCostQuota ring hn fresh update y hC i z ≤ 8 * n := by
  have hAligned := grantDrainWarmCostCarrierAligned
    ring hn fresh update y hC z
  have hLedger : (z.val.ledger.grantLabels i).remaining ≤ 2 * n :=
    hAligned.2.2.2 i
  have hTwo : 2 * n ≤ 8 * n := by omega
  cases hw : z.val.warm.warmLabels i with
  | none =>
      have hBound := grantDrainWarmCostLedgerQuotaLeRemaining
        (z.val.ledger.grantLabels i)
      have hFinal := Nat.le_trans (Nat.le_trans hBound hLedger) hTwo
      simpa [grantDrainWarmCostQuota, hw] using hFinal
  | some cert =>
      cases hWarm : cert.label.warm with
      | true =>
          have hBudget := hAligned.2.2.1 i cert hw
          simpa [grantDrainWarmCostQuota, hw,
            grantDrainWarmStageCombinedQuota, hWarm] using hBudget
      | false =>
          have hBound := grantDrainWarmStageColdQuotaBound
            ring cert (z.val.ledger.grantLabels i) hWarm
          have hFinal := Nat.le_trans (Nat.le_trans hBound hLedger) hTwo
          simpa [grantDrainWarmCostQuota, hw] using hFinal


/-- Under genuine initial C_native ancestry, a live already marked
source label has positive remaining quota.  The proof uses the
full immutable grant-label ghost and the existing LockBudget theorem. -/
private theorem grantDrainWarmCostMarkedRemainingPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (i : Fin n)
    (hLive : (z.val.ledger.grantLabels i).host ≠ none)
    (hMarked : (z.val.ledger.grantLabels i).mark ≠ .unmarked) :
    0 < (z.val.ledger.grantLabels i).remaining := by
  obtain ⟨word, hWord⟩ := z.property
  have hLedger :
      z.val.ledger =
        grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring y) word := by
    rw [hWord]
    exact grantDrainWarmStageJointLedgerWord
      ring hn fresh update word
      (grantDrainWarmStageJointInitial ring hn y hC)
  have hLiveWord :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring y) word).grantLabels i).host ≠
          none := by
    rw [← hLedger]
    exact hLive
  have hMarkedWord :
      ((grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring y) word).grantLabels i).mark ≠
          .unmarked := by
    rw [← hLedger]
    exact hMarked
  have hPositive := grantDrainMarkedBranchLivePositive
    ring hn fresh update y hC.1.1 word i hLiveWord hMarkedWord
  rw [← hLedger] at hPositive
  exact hPositive

/-- Every LIVE immutable label has strictly positive combined
quota.  If still warm, the certified plus-one reserve pays it;
if cold or untracked, the source ledger's established mark and
NoExhaustion pay it. -/
theorem grantDrainWarmCostLiveQuotaPositive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (i : Fin n)
    (hLive : (z.val.ledger.grantLabels i).host ≠ none) :
    0 < grantDrainWarmCostQuota ring hn fresh update y hC i z := by
  have hAligned := grantDrainWarmCostCarrierAligned
    ring hn fresh update y hC z
  have hPhase := hAligned.2.1 i
  cases hw : z.val.warm.warmLabels i with
  | none =>
      simp only [hw] at hPhase
      have hPositive := grantDrainWarmCostMarkedRemainingPositive
        ring hn fresh update y hC z i hLive (hPhase hLive)
      cases hHost : (z.val.ledger.grantLabels i).host with
      | none =>
          exact False.elim (hLive hHost)
      | some g =>
          simpa [grantDrainWarmCostQuota, hw,
            grantDrainWarmCostLedgerQuota, hHost] using hPositive
  | some cert =>
      simp only [hw] at hPhase
      cases hWarm : cert.label.warm with
      | true =>
          have hRank := grantDrainWarmStageWarmRankPositive
            ring cert hWarm
          simp only [grantDrainWarmCostQuota, hw]
          simp only [grantDrainWarmStageCombinedQuota,
            hWarm, if_true]
          omega
      | false =>
          have hPositive := grantDrainWarmCostMarkedRemainingPositive
            ring hn fresh update y hC z i hLive
            (hPhase.2 hWarm hLive)
          cases hHost : (z.val.ledger.grantLabels i).host with
          | none =>
              exact False.elim (hLive hHost)
          | some g =>
              simp only [grantDrainWarmCostQuota, hw]
              simp only [grantDrainWarmStageCombinedQuota,
                hWarm, Bool.false_eq_true, ↓reduceIte,
                hHost, reduceCtorEq]
              exact hPositive

/-- When all n original quotas vanish, every physical grant has
retired. Full-label ancestry supplies its immutable origin, and
live-quota positivity contradicts zero at that origin. -/
theorem grantDrainWarmCostZeroPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (hZero : ∀ i : Fin n,
      grantDrainWarmCostQuota ring hn fresh update y hC i z = 0) :
    GrantFree z.val.warm.physical := by
  intro g
  by_cases hGrant : z.val.warm.physical.grant g = true
  · obtain ⟨word, hWord⟩ := z.property
    have hLedger :
        z.val.ledger =
          grantDrainEntranceRun ring fresh update
            (grantDrainEntranceInitial ring y) word := by
      rw [hWord]
      exact grantDrainWarmStageJointLedgerWord
        ring hn fresh update word
        (grantDrainWarmStageJointInitial ring hn y hC)
    have hLedgerGrant : z.val.ledger.physical.grant g = true := by
      rw [← z.val.physicalEq]
      exact hGrant
    have hGrantWord :
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring y) word).physical.grant g =
            true := by
      rw [← hLedger]
      exact hLedgerGrant
    obtain ⟨i, hHostWord⟩ :=
      grantDrainMarkedBranchPhysicalCover
        ring hn fresh update y word g hGrantWord
    have hHost :
        (z.val.ledger.grantLabels i).host = some g := by
      rw [hLedger]
      exact hHostWord
    have hLive :
        (z.val.ledger.grantLabels i).host ≠ none := by
      rw [hHost]
      intro hh
      cases hh
    have hPositive :=
      grantDrainWarmCostLiveQuotaPositive
        ring hn fresh update y hC z i hLive
    exact False.elim (Nat.ne_of_gt hPositive (hZero i))
  · cases hg : z.val.warm.physical.grant g with
    | false => rfl
    | true => exact False.elim (hGrant hg)


/-- Conversely, a physically grant-free state has no live original
ledger hosts and no still-warm hosted certificate.  Hence every
combined quota is zero; the two stopping predicates agree on this
reachable carrier. -/
theorem grantDrainWarmCostFreeAllZero
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC)
    (hFree : GrantFree z.val.warm.physical) :
    ∀ i : Fin n,
      grantDrainWarmCostQuota ring hn fresh update y hC i z = 0 := by
  have hAligned := grantDrainWarmCostCarrierAligned
    ring hn fresh update y hC z
  intro i
  have hNoHost : (z.val.ledger.grantLabels i).host = none := by
    cases hh : (z.val.ledger.grantLabels i).host with
    | none => rfl
    | some g =>
        have hSound := hAligned.1 i g hh
        rw [← z.val.physicalEq] at hSound
        have hg := hFree g
        rw [hg] at hSound
        cases hSound
  cases hw : z.val.warm.warmLabels i with
  | none =>
      simp [grantDrainWarmCostQuota, hw,
        grantDrainWarmCostLedgerQuota, hNoHost]
  | some cert =>
      have hPhase := hAligned.2.1 i
      simp only [hw] at hPhase
      cases hWarm : cert.label.warm with
      | true =>
          have hSame := hPhase.1 hWarm
          obtain ⟨g, hCertHost⟩ := cert.hosted hWarm
          rw [hNoHost, hCertHost] at hSame
          cases hSame
      | false =>
          simp [grantDrainWarmCostQuota, hw,
            grantDrainWarmStageCombinedQuota, hWarm, hNoHost]

/-- The family-tail zero-quota target is *exactly* GrantFree on the
reachable certified carrier, not merely a sufficient condition. -/
theorem grantDrainWarmCostZeroIffGrantFree
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (z : GrantDrainWarmCostCarrier ring hn fresh update y hC) :
    (∀ i : Fin n,
      grantDrainWarmCostQuota ring hn fresh update y hC i z = 0) ↔
      GrantFree z.val.warm.physical := by
  constructor
  · exact grantDrainWarmCostZeroPhysical
      ring hn fresh update y hC z
  · exact grantDrainWarmCostFreeAllZero
      ring hn fresh update y hC z

/-- Physical projection of the reachable joint carrier is exactly the
old canonical grantDrainStep at every scheduler letter. -/
theorem grantDrainWarmCostProjection
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (P : GrantDrainState n Scratch → Prop) :
    ∀ T : Nat,
      ∀ z : GrantDrainWarmCostCarrier ring hn fresh update y hC,
        costNumerator
          (grantDrainWarmCostNext ring hn fresh update y hC)
          (fun w => P w.val.warm.physical) z T =
        costNumerator (grantDrainStep ring fresh update)
          P z.val.warm.physical T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z
      by_cases hp : P z.val.warm.physical
      · have hTarget :
            (fun w : GrantDrainWarmCostCarrier
              ring hn fresh update y hC => P w.val.warm.physical) z := hp
        rw [costNumerator_terminal
          (grantDrainWarmCostNext ring hn fresh update y hC)
          (fun w => P w.val.warm.physical) z hTarget (T + 1),
          costNumerator_terminal
          (grantDrainStep ring fresh update) P
          z.val.warm.physical hp (T + 1)]
      · have hNotTarget :
            ¬ (fun w : GrantDrainWarmCostCarrier
              ring hn fresh update y hC => P w.val.warm.physical) z := hp
        rw [costNumerator_succ
          (grantDrainWarmCostNext ring hn fresh update y hC)
          (fun w => P w.val.warm.physical) z hNotTarget T,
          costNumerator_succ
          (grantDrainStep ring fresh update) P
          z.val.warm.physical hp T]
        have hChildren :
            (fun e : Fin n =>
              costNumerator
                (grantDrainWarmCostNext ring hn fresh update y hC)
                (fun w => P w.val.warm.physical)
                (grantDrainWarmCostNext
                  ring hn fresh update y hC z e) T) =
            (fun e : Fin n =>
              costNumerator (grantDrainStep ring fresh update) P
                (grantDrainStep ring fresh update
                  z.val.warm.physical e) T) := by
          funext e
          have hProjection :
              (grantDrainWarmCostNext
                ring hn fresh update y hC z e).val.warm.physical =
              grantDrainStep ring fresh update z.val.warm.physical e := by
            rfl
          rw [ih (grantDrainWarmCostNext ring hn fresh update y hC z e),
            hProjection]
        rw [hChildren]

/-- The unconditional warm stage bound, with ONE original uniform
scheduler, n original identities, and no reset of warm/ledger quota.
This is the hWarm premise required by GrantDrainProducer. -/
theorem grantDrainWarmStageCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (y : GrantDrainState n Scratch)
    (hC : C_native ring y.native)
    (T : Nat) :
    costNumerator (grantDrainStep ring fresh update)
      (fun z : GrantDrainState n Scratch => GrantFree z) y T ≤
        n ^ T * (23 * n ^ 2) := by
  have hQuotaCost :=
    grantDrainLabelFamilyTwentyThreeSquareCost
      (grantDrainWarmCostNext ring hn fresh update y hC)
      (fun i z => grantDrainWarmCostQuota
        ring hn fresh update y hC i z)
      (fun i z => grantDrainWarmCostChosen
        ring hn fresh update y hC i z)
      hn (Nat.le_refl n)
      (fun z i e =>
        grantDrainWarmCostQuotaNonincrease
          ring hn fresh update y hC z i e)
      (fun z i hp =>
        grantDrainWarmCostQuotaDrop
          ring hn fresh update y hC z i hp)
      (fun z i =>
        grantDrainWarmCostQuotaBound
          ring hn fresh update y hC z i)
  have hTargetCost :=
    L3.Prob.costNumerator_target_mono
      (grantDrainWarmCostNext ring hn fresh update y hC)
      (fun z : GrantDrainWarmCostCarrier
        ring hn fresh update y hC =>
        ∀ i : Fin n,
          grantDrainWarmCostQuota ring hn fresh update y hC i z = 0)
      (fun z : GrantDrainWarmCostCarrier
        ring hn fresh update y hC => GrantFree z.val.warm.physical)
      (fun z hZero =>
        grantDrainWarmCostZeroPhysical
          ring hn fresh update y hC z hZero)
      (grantDrainWarmCostInitial ring hn fresh update y hC) T
  have hCost :
      costNumerator
        (grantDrainWarmCostNext ring hn fresh update y hC)
        (fun z : GrantDrainWarmCostCarrier
          ring hn fresh update y hC => GrantFree z.val.warm.physical)
        (grantDrainWarmCostInitial ring hn fresh update y hC) T ≤
          n ^ T * (23 * n ^ 2) := by
    exact Nat.le_trans hTargetCost
      (hQuotaCost
        (grantDrainWarmCostInitial ring hn fresh update y hC) T)
  have hProj := grantDrainWarmCostProjection
    ring hn fresh update y hC
    (fun z : GrantDrainState n Scratch => GrantFree z)
    T (grantDrainWarmCostInitial ring hn fresh update y hC)
  rw [hProj] at hCost
  exact hCost

/-- Closing the producer's last R8e premise without any assumed
leaf: the all-marked branch is already provided earlier. -/
theorem grantDrainSharedBoundProved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) := by
  exact grantDrainSharedBoundOfWarm ring hn fresh update
    (fun y hC T =>
      grantDrainWarmStageCost ring hn fresh update y hC T)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainWarmCostAlignedInitial
#print axioms L3.GrantDrainEntrance.grantDrainWarmCostAlignedNext
#print axioms L3.GrantDrainEntrance.grantDrainWarmCostAlignedOfReachable
#print axioms L3.GrantDrainEntrance.grantDrainWarmCostQuotaNonincrease
#print axioms L3.GrantDrainEntrance.grantDrainWarmCostQuotaDrop
#print axioms L3.GrantDrainEntrance.grantDrainWarmCostQuotaBound
#print axioms L3.GrantDrainEntrance.grantDrainWarmCostZeroPhysical
#print axioms L3.GrantDrainEntrance.grantDrainWarmStageCost
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundProved
