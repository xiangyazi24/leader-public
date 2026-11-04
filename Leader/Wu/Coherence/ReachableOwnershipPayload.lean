import Leader.Wu.Coherence.ReachableWideOverlapPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachablePlus4

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3

variable {n ψ κ τ : Nat}

/-- Footprint of the strict swept prefix; binder matches
`SweptPrefixOwnedClearV31` exactly. -/
def InSweptOwnedFootprintV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner p : Fin n) : Prop :=
  ∃ k : Fin (raw (C owner)).label.val,
    R2Coherence.groupPos ring (eraseCfgV3 C) owner k.val = p

/-- Footprint of a whole owned group; binder matches
`GroupOwnedClearV31` exactly. -/
def InGroupOwnedFootprintV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner p : Fin n) : Prop :=
  ∃ k : Fin ψ,
    R2Coherence.groupPos ring (eraseCfgV3 C) owner k.val = p

/-- The four phases whose current invariant owns an entire group. -/
def CarriesGroupOwnedPhaseV31
    (C : FC n ψ κ τ) (owner : Fin n) : Prop :=
  (C owner).ctl.tok = .commit ∨
    (C owner).ctl.mark = .sealed ∨
    (C owner).ctl.tok = .release ∨
    (C owner).ctl.tok = .scrubL

/-- Prepay a root sweep which a live seek is about to create. -/
def SeekIncomingSweepOpenROverlapClearWideV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C (ring.rightNeighbor e)).ctl.tok = .seek →
    PendingOpenROwnerV31 ring C owner →
      (atRootB (C (ring.rightNeighbor e)) = true →
        SweepOpenRSafeAtV31 ring C owner
            (ring.rightNeighbor (ring.rightNeighbor e)) ∧
        ∀ d : Fin
            (ψ - (raw (C (ring.rightNeighbor e))).label.val),
          SweepOpenRSafeAtV31 ring C owner
            (R2Coherence.fwd ring (ring.rightNeighbor e) d.val)) ∧
      (atRootB (C (ring.rightNeighbor e)) = false →
        atRootB (C e) = true →
          SweepOpenRSafeAtV31 ring C owner (ring.rightNeighbor e) ∧
          ∀ d : Fin (ψ - (raw (C e)).label.val),
            SweepOpenRSafeAtV31 ring C owner
              (R2Coherence.fwd ring e d.val))

/-- Every current/future cell in the live openR suffix is already main-clear. -/
def OpenRForwardMainClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ e : Fin n,
    (C e).ctl.tok = .openR →
      ∀ d : Fin (ψ - (raw (C e)).label.val),
        MainClearV3
          (C (R2Coherence.fwd ring e d.val))

/-- An openR service never opens a cell owned by a surviving phase. -/
def OpenRPhaseOwnershipDisjointV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C e).ctl.tok = .openR →
    successorB (C e) (C (ring.rightNeighbor e)) = true →
    owner ≠ ring.rightNeighbor e →
      ((C owner).ctl.tok = .sweep →
          ¬ InSweptOwnedFootprintV31 ring C owner e) ∧
      (CarriesGroupOwnedPhaseV31 C owner →
          ¬ InGroupOwnedFootprintV31 ring C owner e) ∧
      (atTerminalB (C (ring.rightNeighbor e)) = true →
        ((C owner).ctl.tok = .sweep →
            ¬ InSweptOwnedFootprintV31 ring C owner
              (ring.rightNeighbor e)) ∧
        (CarriesGroupOwnedPhaseV31 C owner →
            ¬ InGroupOwnedFootprintV31 ring C owner
              (ring.rightNeighbor e)))

def ReachablePhaseFactsPlus4V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsPlus3V31 ring C ∧
    SeekIncomingSweepOpenROverlapClearWideV31 ring C ∧
    OpenRForwardMainClearV31 ring C ∧
    OpenRPhaseOwnershipDisjointV31 ring C

/-- Entrance is vacuous: quarantine has no seek token. -/
theorem seekIncomingSweepOpenROverlapClearWide_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    SeekIncomingSweepOpenROverlapClearWideV31 ring
      (quarantineInitV31 C) := by
  intro e owner hSeek
  simp [quarantineInitV31, setControl] at hSeek

/-- Entrance is vacuous: quarantine has no openR token. -/
theorem openRForwardMainClear_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    OpenRForwardMainClearV31 ring (quarantineInitV31 C) := by
  intro e hOpenR
  simp [quarantineInitV31, setControl] at hOpenR

/-- Entrance is vacuous: quarantine has no openR token. -/
theorem openRPhaseOwnershipDisjoint_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    OpenRPhaseOwnershipDisjointV31 ring (quarantineInitV31 C) := by
  intro e owner hOpenR
  simp [quarantineInitV31, setControl] at hOpenR

/-- Full Plus4 entrance. -/
theorem reachablePhaseFactsPlus4_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsPlus4V31 ring C := by
  refine ⟨reachablePhaseFactsPlus3_entrance hψ h2 ring C hBirth,
    ?_, ?_, ?_⟩
  · rcases hBirth.1 with ⟨_, D, _, hEq⟩
    rw [hEq]
    exact seekIncomingSweepOpenROverlapClearWide_quarantineInit ring D
  · rcases hBirth.1 with ⟨_, D, _, hEq⟩
    rw [hEq]
    exact openRForwardMainClear_quarantineInit ring D
  · rcases hBirth.1 with ⟨_, D, _, hEq⟩
    rw [hEq]
    exact openRPhaseOwnershipDisjoint_quarantineInit ring D

private theorem branch_seek_token_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_seek_eq_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = seekStageV3 l r := by
  have hSeek := branch_seek_token_plus4 hψ h2 l r hb
  simp [rowV3, hSeek]

private theorem seekStage_phys_plus4
    (l r : Cell ψ κ τ) :
    (seekStageV3 l r).1.phys = l.phys ∧
      (seekStageV3 l r).2.phys = r.phys := by
  unfold seekStageV3
  repeat' split <;> simp [setControl]


private theorem seek_step_left_eq_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    stepV3 hψ h2 ring C e e =
      (seekStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hrow := rowV3_seek_eq_plus4 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow]

private theorem seek_step_right_eq_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      (seekStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
  have hrow := rowV3_seek_eq_plus4 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hrow, hne]

/-- Seek changes controller coordinates only. -/
private theorem seek_step_phys_eq_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ∀ p : Fin n,
      (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  have hs := seekStage_phys_plus4
    (C e) (C (ring.rightNeighbor e))
  by_cases hpe : p = e
  · subst p
    rw [seek_step_left_eq_plus4 hψ h2 ring C e hb]
    exact hs.1
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [seek_step_right_eq_plus4 hψ h2 ring C e hb hpe]
      exact hs.2
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]

private theorem seek_step_raw_eq_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) := by
  change
    (stepV3 hψ h2 ring C e p).phys.base.core.core =
      (C p).phys.base.core.core
  exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (seek_step_phys_eq_plus4 hψ h2 ring C e hb p)

private theorem seek_step_atRoot_eq_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    atRootB (stepV3 hψ h2 ring C e p) = atRootB (C p) := by
  unfold atRootB
  rw [seek_step_raw_eq_plus4 hψ h2 ring C e p hb]

private theorem groupPos_eq_of_labels_plus4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]

private theorem prefixPos_eq_of_labels_plus4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring i ((raw (D i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

/-- One-way footprint transport needed by seek: seek holds every physical
label, so a post-state freshness read was already a pre-state freshness read. -/
private theorem footprint_after_seek_to_before_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (hFoot : InOpenRFreshFootprintV31 ring
      (stepV3 hψ h2 ring C e) owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  have hLab : ∀ x : Fin n,
      (raw (stepV3 hψ h2 ring C e x)).label = (raw (C x)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  rcases hFoot with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  have hGPko := groupPos_eq_of_labels_plus4 ring hLab j ko.val
  rw [hGPko] at hOwnerD
  have hGPq := groupPos_eq_of_labels_plus4 ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD :
      R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val = front := by
    simpa [front] using hGPq
  have hLabelVal :
      (raw (stepV3 hψ h2 ring C e
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFrontD]
    exact congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hmD : m <
        (raw (stepV3 hψ h2 ring C e
          (R2Coherence.groupPos ring
            (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val))).label.val + 1 :=
      kD.isLt
    simpa only [hLabelVal] using hmD
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  let m : Nat := kD.val
  have hPrefixD0 :
      R2Coherence.prefixPos ring (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val) m = p := by
    simpa [m] using hPrefixD
  have hPrefixD1 :
      R2Coherence.prefixPos ring (eraseCfgV3 (stepV3 hψ h2 ring C e))
        front m = p := by
    simpa only [hFrontD] using hPrefixD0
  have hPP := prefixPos_eq_of_labels_plus4 ring hLab front m
  have hPrefixC :
      R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p := by
    exact hPP.symm.trans hPrefixD1
  have hFrontC :
      R2Coherence.groupPos ring (eraseCfgV3 C) j q.val = front := by
    rfl
  have hkCm : kC.val = m := by
    rfl
  simpa only [hFrontC, hkCm] using hPrefixC
