import Leader.Wu.Comparison.ExpiringRepair
import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Birth.ShortDoneTerminalBirthPhysical
import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel
import Leader.Wu.Birth.ShortDoneTerminalRowRightLeader
import Leader.Wu.Splice.OrdinaryHostLabelFrame
import Leader.Wu.Splice.PhysicalHoldBirthSafe
import Leader.Wu.Birth.CheckPermitRepairLeaf
import Leader.Wu.Entrance.LocalRuler

set_option autoImplicit false
set_option Elab.async false

/-!
# Physical host-row boundary for an additive B9 successor

The computational interface contains only a binary physical row.
Geometric laws are separate proof objects. Locality is derived from the
native two-site update, not assumed as a field of the interface.

The terminal consumer receives the complete geometric contract.
R1 receives guarded contracts on proved agreement domains. Its unrestricted
contract is recorded only in the PLAN comment at the end of this file.

No B9 table is defined or modified here.
-/

namespace B9Host

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
-- These are the defining namespaces of the native steps used below.
open PopulationProtocol BirthShortDoneTerminalConsumer
  BirthCheckPermitRepairLeaf BirthPhaseWait2BlockProgress

/-- A physical pair service, with no access to B9 controller fields. -/
structure HostRow (P : Type) where
  row : P → P → P × P

abbrev Phys (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau

abbrev PhysConfig (n psi kappa tau : Nat) :=
  Fin n → Phys psi kappa tau

variable {n psi kappa tau width : Nat}

def leader (u : Phys psi kappa tau) : Bool :=
  u.core.core.leader

def label (u : Phys psi kappa tau) : Fin psi :=
  u.core.core.label

def Aligned (l r : Phys psi kappa tau) : Prop :=
  (label r).val = ((label l).val + 1) % psi

/-- Detection uses exactly the row selected for physical execution. -/
def LeftDeletionCandidate (host : HostRow (Phys psi kappa tau))
    (l r : Phys psi kappa tau) : Prop :=
  leader l = true ∧ leader (host.row l r).1 = false

/-- Native population-protocol convention: on an aliased edge, the left
output wins. The B9 self-edge hold belongs to the future B9 table, not here. -/
def hostStep {P : Type} (host : HostRow P)
    (ring : DirectedRing n) (C : Fin n → P) (e : Fin n) : Fin n → P :=
  let q := host.row (C e) (C (ring.rightNeighbor e))
  fun i =>
    if i = e then q.1
    else if i = ring.rightNeighbor e then q.2
    else C i

theorem hostStep_left {P : Type} (host : HostRow P)
    (ring : DirectedRing n) (C : Fin n → P) (e : Fin n) :
    hostStep host ring C e e =
      (host.row (C e) (C (ring.rightNeighbor e))).1 := by
  simp only [hostStep, if_pos rfl]

theorem hostStep_right {P : Type} (host : HostRow P)
    (ring : DirectedRing n) (C : Fin n → P) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    hostStep host ring C e (ring.rightNeighbor e) =
      (host.row (C e) (C (ring.rightNeighbor e))).2 := by
  simp only [hostStep, if_neg hne]
  simp

theorem hostStep_other {P : Type} (host : HostRow P)
    (ring : DirectedRing n) (C : Fin n → P) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    hostStep host ring C e i = C i := by
  simp only [hostStep, if_neg hi, if_neg hj]

theorem hostStep_pairLocal {P : Type} (host : HostRow P)
    (ring : DirectedRing n) :
    B6WindowLocality.PairLocal ring (hostStep host ring) := by
  refine ⟨?_, ?_⟩
  · intro C e i hi hj
    exact hostStep_other host ring C e i hi hj
  · intro C D e hL hR
    constructor <;> simp only [hostStep, hL, hR]

/-- Agreement is required only on the pair served in this step. -/
theorem hostStep_eq_of_row_eq {P : Type} (host refHost : HostRow P)
    (ring : DirectedRing n) (C : Fin n → P) (e : Fin n)
    (hrow : host.row (C e) (C (ring.rightNeighbor e)) =
      refHost.row (C e) (C (ring.rightNeighbor e))) :
    hostStep host ring C e = hostStep refHost ring C e := by
  simp only [hostStep, hrow]

theorem aligned_of_labels_eq
    (l r outL outR : Phys psi kappa tau)
    (hL : label outL = label l) (hR : label outR = label r)
    (hA : Aligned l r) : Aligned outL outR := by
  unfold Aligned
  rw [hL, hR]
  exact hA

/-- No semantic host law is needed for this consequence of the detector. -/
theorem left_leader_of_not_candidate
    (host : HostRow (Phys psi kappa tau)) (l r : Phys psi kappa tau)
    (hno : ¬ LeftDeletionCandidate host l r) (hl : leader l = true) :
    leader (host.row l r).1 = true := by
  cases hout : leader (host.row l r).1 with
  | false => exact False.elim (hno ⟨hl, hout⟩)
  | true => rfl

/-- The three geometric laws. These are not assumptions on
all HostRow values, and are not needed for their native pair locality. -/
structure SpliceLaws (host : HostRow (Phys psi kappa tau)) : Prop where
  left_follower_label :
    ∀ (l r : Phys psi kappa tau),
      leader l = false → label (host.row l r).1 = label l
  right_leader :
    ∀ (l r : Phys psi kappa tau),
      leader r = true → leader (host.row l r).2 = true
  aligned_followers :
    ∀ (l r : Phys psi kappa tau),
      leader l = false → leader r = false →
      leader (host.row l r).1 = false →
      leader (host.row l r).2 = false →
      Aligned l r → Aligned (host.row l r).1 (host.row l r).2

/-- A guarded certificate is deliberately a different type from the
unrestricted contract. Every field retains the pair-domain hypothesis. -/
structure SpliceLawsOn (host : HostRow (Phys psi kappa tau))
    (R : Phys psi kappa tau → Phys psi kappa tau → Prop) : Prop where
  left_follower_label :
    ∀ (l r : Phys psi kappa tau), R l r →
      leader l = false → label (host.row l r).1 = label l
  right_leader :
    ∀ (l r : Phys psi kappa tau), R l r →
      leader r = true → leader (host.row l r).2 = true
  aligned_followers :
    ∀ (l r : Phys psi kappa tau), R l r →
      leader l = false → leader r = false →
      leader (host.row l r).1 = false →
      leader (host.row l r).2 = false →
      Aligned l r → Aligned (host.row l r).1 (host.row l r).2

/-- Transfer the three laws only where full pair-output equality is proved. -/
theorem spliceLawsOn_of_row_eq
    (host refHost : HostRow (Phys psi kappa tau))
    (laws : SpliceLaws refHost)
    (R : Phys psi kappa tau → Phys psi kappa tau → Prop)
    (hEq : ∀ l r, R l r → host.row l r = refHost.row l r) :
    SpliceLawsOn host R := by
  refine ⟨?_, ?_, ?_⟩
  · intro l r hR hl
    rw [hEq l r hR]
    exact laws.left_follower_label l r hl
  · intro l r hR hr
    rw [hEq l r hR]
    exact laws.right_leader l r hr
  · intro l r hR hl hr hOL hOR hA
    simp only [hEq l r hR] at hOL hOR ⊢
    exact laws.aligned_followers l r hl hr hOL hOR hA
/-- The existing terminal consumer, with width absorbed into the host value. -/
def terminalHost (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width ≤ psi) : HostRow (Phys psi kappa tau) :=
  ⟨BirthShortDoneTerminalHost.row hpsi hwidth hle⟩

theorem hostStep_terminal_eq_step
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : PhysConfig n psi kappa tau) (e : Fin n) :
    hostStep (terminalHost hpsi hwidth hle) ring C e =
      BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring C e := rfl

/-- Source: B9SpliceV10ePhysicalHoldBirth.left_follower_label_frame. -/
theorem terminalHost_left_follower_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Phys psi kappa tau) (hl : leader l = false) :
    label ((terminalHost hpsi hwidth hle).row l r).1 = label l :=
  B9SpliceV10ePhysicalHoldBirth.left_follower_label_frame
    hpsi hwidth hle l r hl

/-- Source: BirthShortDoneTerminalRowRightLeader.row_right_leader. -/
theorem terminalHost_right_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Phys psi kappa tau) (hr : leader r = true) :
    leader ((terminalHost hpsi hwidth hle).row l r).2 = true :=
  BirthShortDoneTerminalRowRightLeader.row_right_leader
    hpsi hwidth hle l r hr

/-- With follower inputs and no metadata birth, normalization is the
identity on both computed endpoints. This converts the existing entry-label
frames into final-row label frames; it does not identify entry with input. -/
private theorem terminal_metadata_eq_entry_of_no_birth
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Phys psi kappa tau)
    (hl : leader l = false) (hr : leader r = false)
    (hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi hwidth hle l r = false) :
    BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r =
      BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r := by
  have hl0 : l.core.core.leader = false := hl
  have hr0 : r.core.core.leader = false := hr
  have hnb :
      K2BirthDispatcher.newborn l
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1 = false ∧
      K2BirthDispatcher.newborn r
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2 = false := by
    simpa only [BirthShortDoneTerminalObserver.birthEvent,
      Bool.or_eq_false_iff] using hb
  have hml :
      (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1.core.core.leader = false := by
    simpa [K2BirthDispatcher.newborn, hl0] using hnb.1
  have hmr :
      (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2.core.core.leader = false := by
    simpa [K2BirthDispatcher.newborn, hr0] using hnb.2
  let d := BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r
  change (K2BirthLeaderNormalize.normalizeLeader hpsi d.1).core.core.leader = false at hml
  change (K2BirthLeaderNormalize.normalizeLeader hpsi d.2).core.core.leader = false at hmr
  rw [K2BirthLeaderNormalize.normalizeLeader_leader] at hml hmr
  change (K2BirthLeaderNormalize.normalizeLeader hpsi d.1,
    K2BirthLeaderNormalize.normalizeLeader hpsi d.2) = d
  apply Prod.ext
  · change K2BirthLeaderNormalize.normalizeLeader hpsi d.1 = d.1
    simp only [K2BirthLeaderNormalize.normalizeLeader, hml,
      Bool.false_eq_true, if_false]
  · change K2BirthLeaderNormalize.normalizeLeader hpsi d.2 = d.2
    simp only [K2BirthLeaderNormalize.normalizeLeader, hmr,
      Bool.false_eq_true, if_false]

/-- The terminal row cannot turn an aligned follower pair into a misaligned
follower pair. Birth is excluded by the two actual output-follower premises;
deletion-priority cases preserve both labels, and the open ordinary case
provides the exact successor labels. -/
theorem terminalHost_aligned_followers
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Phys psi kappa tau)
    (hl : leader l = false) (hr : leader r = false)
    (hOL : leader ((terminalHost hpsi hwidth hle).row l r).1 = false)
    (hOR : leader ((terminalHost hpsi hwidth hle).row l r).2 = false)
    (hA : Aligned l r) :
    Aligned ((terminalHost hpsi hwidth hle).row l r).1
      ((terminalHost hpsi hwidth hle).row l r).2 := by
  have hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi hwidth hle l r = false := by
    cases hb0 : BirthShortDoneTerminalObserver.birthEvent
        hpsi hwidth hle l r with
    | false => rfl
    | true =>
        rcases BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
          hpsi hwidth hle l r hb0 with hL | hR
        · have hbad : (false : Bool) = true := hOL.symm.trans hL
          cases hbad
        · have hbad : (false : Bool) = true := hOR.symm.trans hR
          cases hbad
  have hm := terminal_metadata_eq_entry_of_no_birth
    hpsi hwidth hle l r hl hr hb
  have hframe := B9SpliceV8LabelFrame.hostRow_labels_metadata
    hpsi hwidth hle l r
  change
    (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label =
        (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1.core.core.label ∧
    (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label =
        (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2.core.core.label at hframe
  simp only [hm] at hframe
  cases hdR : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) with
  | true =>
      have hd := B9SpliceV8LabelFrame.host_responder_deletion_label_frame
        hpsi hwidth hle l r hdR
      exact aligned_of_labels_eq l r _ _
        (hframe.1.trans hd.1) (hframe.2.trans hd.2) hA
  | false =>
      cases hdL : deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) with
      | true =>
          have hd := B9SpliceV8LabelFrame.host_initiator_deletion_label_frame
            hpsi hwidth hle l r hdR hdL
          exact aligned_of_labels_eq l r _ _
            (hframe.1.trans hd.1) (hframe.2.trans hd.2) hA
      | false =>
          have hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
              hpsi l r := ⟨hdR, hdL⟩
          have hlabels := BirthShortDoneTerminalOrdinaryLabelR1.ordinary_row_labels_of_no_birth
            hpsi hwidth hle l r hl hr hopen hb
          change
            (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label.val =
              ((BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label.val + 1) % psi
          exact (congrArg (fun a : Fin psi => a.val) hlabels.2).trans
            (congrArg (fun a : Fin psi => (a.val + 1) % psi) hlabels.1.symm)

/-- The complete consumer certificate; no B9 preservation theorem is assumed. -/
theorem terminalHost_spliceLaws
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    SpliceLaws (terminalHost (kappa := kappa) (tau := tau) hpsi hwidth hle) where
  left_follower_label := terminalHost_left_follower_label hpsi hwidth hle
  right_leader := terminalHost_right_leader hpsi hwidth hle
  aligned_followers := terminalHost_aligned_followers hpsi hwidth hle
/-- The actual permit-repaired row, at arbitrary admissible width. -/
def r1HostWidth (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width ≤ psi) : HostRow (Phys psi kappa tau) :=
  ⟨BirthCheckPermitRepair.row hpsi hwidth hle⟩

/-- Width-two R1 host used by BirthCheckPermitRepairLeaf.step1. -/
def r1Host (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    HostRow (Phys psi kappa tau) :=
  r1HostWidth hpsi (by decide : 0 < 2) h2

/-- Identification with R1's own native step, not with the consumer step. -/
theorem hostStep_r1_eq_step1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : PhysConfig n psi kappa tau) (e : Fin n) :
    hostStep (r1Host hpsi h2) ring C e =
      BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e := rfl

/-- Existing width-two agreement theorem. NoEqualOutcome is not asserted
on all follower pairs or on all pairs outside the genuinely active E class.
Source: BirthCheckPermitRepairAgree.row_eq. -/
theorem r1Host_row_eq_terminal_of_noEqual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hne : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    (r1Host hpsi h2).row l r =
      (terminalHost hpsi (by decide : 0 < 2) h2).row l r :=
  BirthCheckPermitRepairAgree.row_eq hpsi h2 l r hne

/-- Responder-deletion agreement is generic in width and needs no CHECK
outcome hypothesis. Source: B6LocalRuler.r1_row_eq_host_of_responder_delete. -/
theorem r1HostWidth_row_eq_terminal_of_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Phys psi kappa tau)
    (hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) :
    (r1HostWidth hpsi hwidth hle).row l r =
      (terminalHost hpsi hwidth hle).row l r :=
  B6LocalRuler.r1_row_eq_host_of_responder_delete
    hpsi hwidth hle l r hdel

/-- Existing step agreement, with its served-pair hypothesis retained.
Source: BirthCheckPermitRepairAgree.step1_eq. -/
theorem hostStep_r1_eq_currentStep2_of_noEqual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : PhysConfig n psi kappa tau) (e : Fin n)
    (hne : BirthCheckPermitRepairAgree.NoEqualOutcome
      hpsi h2 (C e) (C (ring.rightNeighbor e))) :
    hostStep (r1Host hpsi h2) ring C e =
      BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e := by
  rw [hostStep_r1_eq_step1]
  exact BirthCheckPermitRepairAgree.step1_eq hpsi h2 ring C e hne

/-- The responder-deletion agreement also respects the native alias convention. -/
theorem hostStep_r1Width_eq_terminal_of_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : PhysConfig n psi kappa tau) (e : Fin n)
    (hdel : deletionActive
      (normalizeDeletion
        (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))).core.erase) = true) :
    hostStep (r1HostWidth hpsi hwidth hle) ring C e =
      hostStep (terminalHost hpsi hwidth hle) ring C e :=
  hostStep_eq_of_row_eq _ _ ring C e
    (r1HostWidth_row_eq_terminal_of_responder_delete
      hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hdel)

/-- All three geometric laws on the proved no-equal agreement domain.
This is a guarded certificate, not SpliceLaws for the unrestricted R1 row. -/
theorem r1Host_spliceLawsOn_noEqual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    SpliceLawsOn (r1Host (kappa := kappa) (tau := tau) hpsi h2)
      (BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2) := by
  refine spliceLawsOn_of_row_eq
    (r1Host hpsi h2)
    (terminalHost hpsi (by decide : 0 < 2) h2)
    (terminalHost_spliceLaws hpsi (by decide : 0 < 2) h2)
    (BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2) ?_
  intro l r hne
  exact r1Host_row_eq_terminal_of_noEqual hpsi h2 l r hne

/-- A separate guarded certificate for the prepared responder-deletion branch,
including pairs whose hypothetical ordinary CHECK outcome might be equal. -/
theorem r1HostWidth_spliceLawsOn_responder_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    SpliceLawsOn
      (r1HostWidth (kappa := kappa) (tau := tau) hpsi hwidth hle)
      (fun _ r => deletionActive
        (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) := by
  refine spliceLawsOn_of_row_eq
    (r1HostWidth hpsi hwidth hle)
    (terminalHost hpsi hwidth hle)
    (terminalHost_spliceLaws hpsi hwidth hle)
    (fun _ r => deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) ?_
  intro l r hdel
  exact r1HostWidth_row_eq_terminal_of_responder_delete
    hpsi hwidth hle l r hdel

/-
PLAN -- NOT DECLARATIONS, NOT ASSUMPTIONS.

The unrestricted R1 certificates remain future targets:

theorem r1HostWidth_spliceLaws
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    SpliceLaws
      (r1HostWidth (kappa := kappa) (tau := tau) hpsi hwidth hle)

theorem r1Host_spliceLaws
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    SpliceLaws (r1Host (kappa := kappa) (tau := tau) hpsi h2)

Before declaring either theorem, prove the needed whole-row label/leader
facts through the ordinary equal-CHECK case. The existing permitFix_core
identity is at the CHECK cut, not at the end of the physical row.

The active exceptional class E additionally requires ordinary priority and a
true permit at that cut. NoEqualOutcome is narrower than the complement of E;
the no-equal certificate above must not be advertised as full non-E coverage.
Responder deletion is covered separately by its existing full-row equality.

Do not replace this missing geometric proof with unconditional full-row
R1/consumer equality: the crossed aligned CHECK witness distinguishes their
comparison outputs. No unrestricted R1 law value is installed in this file.
-/

end B9Host

-- These are commands for the eventual build, not recorded results of a run.
#print axioms B9Host.terminalHost_spliceLaws
#print axioms B9Host.r1Host_spliceLawsOn_noEqual
#print axioms B9Host.r1HostWidth_spliceLawsOn_responder_delete
