import Leader.Wu.Birth.CheckPermitRepair
import Leader.Wu.Birth.LeaderlessBirthMassRenewal
import Leader.Wu.Birth.FirstLeaderComposition
import Leader.Wu.Entrance.WindowLocality

set_option autoImplicit false

/-! # The leaderless birth-mass leaf on the R1 step

`step1` is the population-protocol step of `BirthCheckPermitRepair.protocol` (width two) on full configurations.
`UniformR1BirthMass L`: from every leaderless configuration at most seven eighths of the words of length `L` stay
leaderless along every prefix.  The generic renewal of `BirthLeaderlessBirthMassRenewal` gives the `1/n` no-leader
tail at horizon `6 (log2 n + 1) L` (`r1_leaderless_tail`, and `r1_leaderless_tail_on` for a step-closed class).
`step1` changes only the served pair and the new pair depends only on the old pair (`step1_pairLocal`), so the
window locality theorems of `B6WindowLocality` apply to R1. -/

namespace BirthCheckPermitRepairLeaf

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthLeaderlessBirthMassRenewal B6WindowLocality

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) := BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- The R1 step with width two. -/
def step1 (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    FC n psi kappa tau :=
  (BirthCheckPermitRepair.protocol hpsi (by decide : 0 < 2) h2 kappa tau).step ring C e

theorem step1_other (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) : step1 hpsi h2 ring C e i = C i := by
  simp only [step1, PopulationProtocol.step, if_neg hi]
  exact if_neg hj

theorem step1_pairLocal (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    PairLocal ring (step1 (kappa := kappa) (tau := tau) hpsi h2 ring) := by
  refine ⟨fun C e i hi hj => step1_other hpsi h2 ring C e i hi hj, ?_⟩
  intro C D e hl hr
  simp only [step1, PopulationProtocol.step, BirthCheckPermitRepair.protocol, hl, hr]
  exact ⟨trivial, trivial⟩

/-- The leaderless birth-mass leaf on the R1 step. -/
def UniformR1BirthMass (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat) : Prop :=
  UniformEscapeMass (S := FC n psi kappa tau) (step1 hpsi h2 ring)
    BirthShortDoneTerminalFirstHit.Leaderless L 8

theorem r1_leaderless_tail (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat)
    (hmass : UniformR1BirthMass (kappa := kappa) (tau := tau) hpsi h2 ring L)
    (hn : 2 ≤ n) (C : FC n psi kappa tau) (h0 : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * aliveCount (step1 hpsi h2 ring) BirthShortDoneTerminalFirstHit.Leaderless C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  tail_one_over_n _ _ L hmass hn C h0

/-- Restricted-class form of the R1 leaf. -/
def UniformR1BirthMassOn (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (R : FC n psi kappa tau → Prop) (L : Nat) : Prop :=
  UniformEscapeMassOn (step1 hpsi h2 ring) BirthShortDoneTerminalFirstHit.Leaderless R L 8

theorem r1_leaderless_tail_on (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (R : FC n psi kappa tau → Prop) (hR : ∀ C e, R C → R (step1 hpsi h2 ring C e)) (L : Nat)
    (hmass : UniformR1BirthMassOn hpsi h2 ring R L)
    (hn : 2 ≤ n) (C : FC n psi kappa tau) (hCR : R C) (h0 : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * aliveCount (step1 hpsi h2 ring) BirthShortDoneTerminalFirstHit.Leaderless C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  tail_one_over_n_on _ _ R L hR hmass hn C hCR h0

end BirthCheckPermitRepairLeaf

/-! ## Agreement with the consumer on rows without an `equal` CHECK outcome -/

namespace BirthCheckPermitRepairAgree

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepPreCheckResetRepair
  K2BirthDispatcher K2BirthDispatcherDone BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair

variable {n psi kappa tau : Nat}

/-- On authorized inputs: the initiator's CHECK outcome on the ordinary branch is not `equal`. -/
def AuthNoEqual (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat) (l r : AuthorizedAgentState psi) : Prop :=
  (doneThroughCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa (normalizeDeletion l)
    (normalizeDeletion r)).1.core.state ≠ .equal

/-- The initiator's CHECK outcome on the ordinary branch of the row is not `equal`. -/
def NoEqualOutcome (hpsi : 0 < psi) (h2 : 2 ≤ psi) (l r : ExpiringAgentState psi kappa tau) : Prop :=
  AuthNoEqual hpsi h2 kappa (prepareExpiringDisposal hpsi l).core.erase (prepareExpiringDisposal hpsi r).core.erase

theorem authorized_eq (hpsi : 0 < psi) (h2 : 2 ≤ psi) (l r : AuthorizedAgentState psi)
    (h : AuthNoEqual hpsi h2 kappa l r) :
    BirthCheckPermitRepair.authorized hpsi (by decide : 0 < 2) h2 kappa l r =
      doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa l r := by
  unfold BirthCheckPermitRepair.authorized doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [BirthCheckPermitRepair.ordinary_eq_of_not_equal _ _ _ _ _ _ h]

theorem reify_congr {q q' : AuthorizedAgentState psi × AuthorizedAgentState psi} (e : q = q')
    (hq : q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa)
    (hq' : q'.1.core.inProtocolDomain kappa ∧ q'.2.core.inProtocolDomain kappa) :
    ((⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
        ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩) :
        AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa) =
      (⟨BoundedAgentState.ofDomain q'.1.core hq'.1, q'.1.path0Crossed⟩,
        ⟨BoundedAgentState.ofDomain q'.2.core hq'.2, q'.2.path0Crossed⟩) := by
  subst e
  rfl

theorem row_eq (hpsi : 0 < psi) (h2 : 2 ≤ psi) (l r : ExpiringAgentState psi kappa tau)
    (h : NoEqualOutcome hpsi h2 l r) :
    BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r =
      BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2 l r := by
  have ha := authorized_eq hpsi h2 (prepareExpiringDisposal hpsi l).core.erase
    (prepareExpiringDisposal hpsi r).core.erase h
  have hb : BirthCheckPermitRepair.bounded hpsi (by decide : 0 < 2) h2 (prepareExpiringDisposal hpsi l).core
      (prepareExpiringDisposal hpsi r).core =
      doneMetadataBoundedEntryWidth hpsi (by decide : 0 < 2) h2 (prepareExpiringDisposal hpsi l).core
        (prepareExpiringDisposal hpsi r).core := by
    unfold BirthCheckPermitRepair.bounded doneMetadataBoundedEntryWidth
    dsimp only
    exact reify_congr ha
      (BirthCheckPermitRepair.authorized_domain hpsi (by decide : 0 < 2) h2 _ _
        (prepareExpiringDisposal hpsi l).core.core.erase_inProtocolDomain
        (prepareExpiringDisposal hpsi r).core.core.erase_inProtocolDomain)
      (doneMetadataAuthorizedEntryWidth_domain hpsi (by decide : 0 < 2) h2 _ _
        (prepareExpiringDisposal hpsi l).core.core.erase_inProtocolDomain
        (prepareExpiringDisposal hpsi r).core.core.erase_inProtocolDomain)
  have he : BirthCheckPermitRepair.expiring hpsi (by decide : 0 < 2) h2 l r =
      doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r := by
    unfold BirthCheckPermitRepair.expiring doneMetadataEntryWidth
    simp only [hb]
  unfold BirthCheckPermitRepair.row BirthShortDoneTerminalHost.row BirthShortDoneTerminalHost.metadata
  rw [he]

/-- On a row without an `equal` CHECK outcome the R1 step is the consumer step. -/
theorem step1_eq (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthCheckPermitRepairLeaf.FC n psi kappa tau) (e : Fin n)
    (h : NoEqualOutcome hpsi h2 (C e) (C (ring.rightNeighbor e))) :
    BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e = BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e := by
  funext i
  simp only [BirthCheckPermitRepairLeaf.step1, BirthPhaseWait2BlockProgress.currentStep2,
    BirthShortDoneTerminalConsumer.step, PopulationProtocol.step, BirthCheckPermitRepair.protocol,
    BirthShortDoneTerminalConsumer.protocol, row_eq hpsi h2 _ _ h]

/-- Every row served along the consumer run has no `equal` CHECK outcome. -/
def NoEqualAlong (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    BirthCheckPermitRepairLeaf.FC n psi kappa tau → List (Fin n) → Prop
  | _, [] => True
  | C, e :: w => NoEqualOutcome hpsi h2 (C e) (C (ring.rightNeighbor e)) ∧
      NoEqualAlong hpsi h2 ring (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) w

theorem noEqualAlong_cons (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthCheckPermitRepairLeaf.FC n psi kappa tau) (e : Fin n) (w : List (Fin n)) :
    NoEqualAlong hpsi h2 ring C (e :: w) ↔ (NoEqualOutcome hpsi h2 (C e) (C (ring.rightNeighbor e)) ∧
      NoEqualAlong hpsi h2 ring (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) w) :=
  Iff.rfl

/-- Along such a word the R1 run is the consumer run. -/
theorem run_eq (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ (C : BirthCheckPermitRepairLeaf.FC n psi kappa tau), NoEqualAlong hpsi h2 ring C w →
      w.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring) C =
        w.foldl (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C := by
  induction w with
  | nil => intro C _; rw [List.foldl_nil, List.foldl_nil]
  | cons e w ih =>
      intro C h
      have h' := (noEqualAlong_cons hpsi h2 ring C e w).1 h
      rw [List.foldl_cons, List.foldl_cons]
      rw [step1_eq hpsi h2 ring C e h'.1]
      exact ih _ h'.2

end BirthCheckPermitRepairAgree
