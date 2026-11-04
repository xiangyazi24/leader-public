import Leader.Wu.Coherence.ReachableOpenNoHazardSweepRead


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableOpenNoHazard4


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3


variable {n ψ κ τ : Nat}


/-- Minimal extra sentence inside R2: a live-sweep read which is also in a
pending owner's freshness footprint is not an ordinary open/none cell. -/
def SweepPendingOpenRFootprintOwnedV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (sweep owner p : Fin n),
    (C sweep).ctl.tok = .sweep →
    PendingOpenROwnerV31 ring C owner →
    InSweepWideReadV31 ring C sweep p →
    InOpenRFreshFootprintV31 ring C owner p →
      PhaseOwnedV31 (C p)


/-- Replacement for R2, not a fifth payload conjunct. -/
def OpenRPhaseOwnershipDisjointStrongV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  OpenRPhaseOwnershipDisjointV31 ring C ∧
    SweepPendingOpenRFootprintOwnedV31 ring C


/-- Same four Plus4 fields; only R2 is strengthened. -/
def ReachablePhaseFactsPlus4StrongR2V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsPlus3V31 ring C ∧
    SeekIncomingSweepOpenROverlapClearWideV31 ring C ∧
    OpenRForwardMainClearV31 ring C ∧
    OpenRPhaseOwnershipDisjointStrongV31 ring C


/-- Quarantine has no live sweep, so the added R2 sentence is vacuous. -/
theorem sweepPendingOpenRFootprintOwned_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    SweepPendingOpenRFootprintOwnedV31 ring (quarantineInitV31 C) := by
  intro sweep owner p hSweep
  simp [quarantineInitV31, setControl] at hSweep


theorem openRPhaseOwnershipDisjointStrong_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    OpenRPhaseOwnershipDisjointStrongV31 ring (quarantineInitV31 C) := by
  exact ⟨openRPhaseOwnershipDisjoint_quarantineInit ring C,
    sweepPendingOpenRFootprintOwned_quarantineInit ring C⟩


/-- Entrance for the four-field replacement payload. -/
theorem reachablePhaseFactsPlus4StrongR2_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsPlus4StrongR2V31 ring C := by
  have hOld := reachablePhaseFactsPlus4_entrance hψ h2 ring C hBirth
  refine ⟨hOld.1, hOld.2.1, hOld.2.2.1, ?_⟩
  rcases hBirth.1 with ⟨_, D, _, hEq⟩
  rw [hEq]
  exact openRPhaseOwnershipDisjointStrong_quarantineInit ring D


private theorem branch_openNoHazard_open_none4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem phaseOwned_not_open_none4
    (u : Cell ψ κ τ)
    (hOwned : PhaseOwnedV31 u)
    (hOpen : u.ctl.mark = .open)
    (hNone : u.ctl.tok = .none) : False := by
  unfold PhaseOwnedV31 at hOwned
  rcases hOwned with hm | ht
  · exact hm hOpen
  · exact ht hNone


private theorem groupPos_eq_of_labels4
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


private theorem prefixPos_eq_of_labels4
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



private theorem sweptFootprint_after_frame_to_before4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner p : Fin n)
    (hFoot : InSweptOwnedFootprintV31 ring D owner p) :
    InSweptOwnedFootprintV31 ring C owner p := by
  rcases hFoot with ⟨kD, hPosD⟩
  have hLabelVal := congrArg Fin.val (hF owner).1
  have hkC : kD.val < (raw (C owner)).label.val := by
    let m : Nat := kD.val
    have hmD : m < (raw (D owner)).label.val := kD.isLt
    simpa only [hLabelVal] using hmD
  let kC : Fin (raw (C owner)).label.val := ⟨kD.val, hkC⟩
  refine ⟨kC, ?_⟩
  change R2Coherence.groupPos ring (eraseCfgV3 C) owner kD.val = p
  have hGP := groupPos_eq_of_labels4 ring (fun x => (hF x).1)
    owner kD.val
  exact hGP.symm.trans hPosD


private theorem groupFootprint_after_frame_to_before4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner p : Fin n)
    (hFoot : InGroupOwnedFootprintV31 ring D owner p) :
    InGroupOwnedFootprintV31 ring C owner p := by
  rcases hFoot with ⟨k, hPosD⟩
  refine ⟨k, ?_⟩
  have hGP := groupPos_eq_of_labels4 ring (fun x => (hF x).1)
    owner k.val
  exact hGP.symm.trans hPosD


/-- Freshness footprint is label-only, so a post-frame hit was already a
pre-frame hit.  The Nat projection avoids dependent-Fin rewrite motives. -/
private theorem openFreshFootprint_after_frame_to_before4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner p : Fin n)
    (hFoot : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  have hLab : ∀ x : Fin n,
      (raw (D x)).label = (raw (C x)).label := fun x => (hF x).1
  rcases hFoot with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  have hGPko := groupPos_eq_of_labels4 ring hLab j ko.val
  rw [hGPko] at hOwnerD
  have hGPq := groupPos_eq_of_labels4 ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD :
      R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using hGPq
  have hLabelVal :
      (raw (D (R2Coherence.groupPos ring
        (eraseCfgV3 D) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFrontD]
    exact congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hmD : m <
        (raw (D (R2Coherence.groupPos ring
          (eraseCfgV3 D) j q.val))).label.val + 1 := kD.isLt
    simpa only [hLabelVal] using hmD
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  let m : Nat := kD.val
  have hPrefixD0 :
      R2Coherence.prefixPos ring (eraseCfgV3 D)
        (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) m = p := by
    simpa [m] using hPrefixD
  have hPrefixD1 :
      R2Coherence.prefixPos ring (eraseCfgV3 D) front m = p := by
    simpa only [hFrontD] using hPrefixD0
  have hPP := prefixPos_eq_of_labels4 ring hLab front m
  have hPrefixC :
      R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p := by
    exact hPP.symm.trans hPrefixD1
  have hFrontC :
      R2Coherence.groupPos ring (eraseCfgV3 C) j q.val = front := by
    rfl
  have hkCm : kC.val = m := by
    rfl
  simpa only [hFrontC, hkCm] using hPrefixC


private theorem pending_after_frame_to_before4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (hPost : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hPost with ⟨hScrub, hSucc, hRoot⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hScrub
    exact hScrub
  · have hL := congrArg Fin.val (hF owner).1
    have hR := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hSucc ⊢
    rw [hL, hR] at hSucc
    exact hSucc
  · have hL := congrArg Fin.val (hF owner).1
    unfold atRootB at hRoot ⊢
    rw [hL] at hRoot
    exact hRoot


private theorem sweepWideRead_after_frame_to_before4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (sweep p : Fin n)
    (hRead : InSweepWideReadV31 ring D sweep p) :
    InSweepWideReadV31 ring C sweep p := by
  unfold InSweepWideReadV31 at hRead ⊢
  rcases hRead with hResp | ⟨dD, hPos⟩
  · exact Or.inl hResp
  · right
    have hLabel := congrArg Fin.val (hF sweep).1
    have hdC : dD.val < ψ - (raw (C sweep)).label.val := by
      let m : Nat := dD.val
      have hmD : m < ψ - (raw (D sweep)).label.val := dD.isLt
      simpa only [hLabel] using hmD
    let dC : Fin (ψ - (raw (C sweep)).label.val) := ⟨dD.val, hdC⟩
    refine ⟨dC, ?_⟩
    simpa [dC] using hPos



private theorem carriesGroupOwned_after_frame_to_before4
    {C D : FC n ψ κ τ} (hF : OpenNoHazardFrameV31 C D)
    (owner : Fin n) (hCarry : CarriesGroupOwnedPhaseV31 D owner) :
    CarriesGroupOwnedPhaseV31 C owner := by
  unfold CarriesGroupOwnedPhaseV31 at hCarry ⊢
  rw [(hF owner).2.2.2] at hCarry
  exact hCarry


private theorem phaseOwned_before_to_after_frame4
    {C D : FC n ψ κ τ} (hF : OpenNoHazardFrameV31 C D)
    (p : Fin n) (hOwned : PhaseOwnedV31 (C p)) :
    PhaseOwnedV31 (D p) := by
  unfold PhaseOwnedV31 at hOwned ⊢
  rw [(hF p).2.2.2]
  exact hOwned


private theorem successor_after_frame_to_before4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (e : Fin n)
    (hSucc : successorB (D e) (D (ring.rightNeighbor e)) = true) :
    successorB (C e) (C (ring.rightNeighbor e)) = true := by
  have hL := congrArg Fin.val (hF e).1
  have hR := congrArg Fin.val (hF (ring.rightNeighbor e)).1
  unfold successorB at hSucc ⊢
  rw [hL, hR] at hSucc
  exact hSucc


private theorem terminal_after_frame_to_before4
    {C D : FC n ψ κ τ} (hF : OpenNoHazardFrameV31 C D)
    (p : Fin n) (hTerm : atTerminalB (D p) = true) :
    atTerminalB (C p) = true := by
  have hL := congrArg Fin.val (hF p).1
  unfold atTerminalB at hTerm ⊢
  rw [hL] at hTerm
  exact hTerm


/-- Old R2 itself is invariant under an open/no-hazard frame: it reads only
controller data, labels, and label-derived footprints. -/
private theorem openRPhaseOwnershipDisjoint_openFrame4
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (hOld : OpenRPhaseOwnershipDisjointV31 ring C) :
    OpenRPhaseOwnershipDisjointV31 ring D := by
  intro e owner hOpenD hSuccD hne
  have hOpenC := hOpenD
  rw [(hF e).2.2.2] at hOpenC
  have hSuccC := successor_after_frame_to_before4 ring hF e hSuccD
  have h := hOld e owner hOpenC hSuccC hne
  refine ⟨?_, ?_, ?_⟩
  · intro hSweepD hFootD
    have hSweepC := hSweepD
    rw [(hF owner).2.2.2] at hSweepC
    exact (h.1 hSweepC)
      (sweptFootprint_after_frame_to_before4 ring hF owner e hFootD)
  · intro hCarryD hFootD
    have hCarryC := carriesGroupOwned_after_frame_to_before4
      hF owner hCarryD
    exact (h.2.1 hCarryC)
      (groupFootprint_after_frame_to_before4 ring hF owner e hFootD)
  · intro hTermD
    have hTermC := terminal_after_frame_to_before4 hF
      (ring.rightNeighbor e) hTermD
    have ht := h.2.2 hTermC
    constructor
    · intro hSweepD hFootD
      have hSweepC := hSweepD
      rw [(hF owner).2.2.2] at hSweepC
      exact (ht.1 hSweepC)
        (sweptFootprint_after_frame_to_before4 ring hF owner
          (ring.rightNeighbor e) hFootD)
    · intro hCarryD hFootD
      have hCarryC := carriesGroupOwned_after_frame_to_before4
        hF owner hCarryD
      exact (ht.2 hCarryC)
        (groupFootprint_after_frame_to_before4 ring hF owner
          (ring.rightNeighbor e) hFootD)


/-- The strengthened R2 is preserved by openNoHazard with no reachability or
chain-origin hypothesis: both old R2 and the new sentence are frame-only. -/
theorem openRPhaseOwnershipDisjointStrong_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    OpenRPhaseOwnershipDisjointStrongV31 ring
      (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  constructor
  · exact openRPhaseOwnershipDisjoint_openFrame4 ring hF hStrong.1
  · intro sweep owner p hSweepD hPendingD hReadD hFootD
    have hSweepC := hSweepD
    rw [(hF sweep).2.2.2] at hSweepC
    have hPendingC := pending_after_frame_to_before4
      ring hF owner hPendingD
    have hReadC := sweepWideRead_after_frame_to_before4
      ring hF sweep p hReadD
    have hFootC := openFreshFootprint_after_frame_to_before4
      ring hF owner p hFootD
    have hOwnedC := hStrong.2 sweep owner p
      hSweepC hPendingC hReadC hFootC
    exact phaseOwned_before_to_after_frame4 hF p hOwnedC



/-- Per-cell transport for the existing wide predicate, now using the strong
R2 sentence exactly in the formerly missing case. -/
private theorem safeAt_openNoHazard_of_strongR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep owner p : Fin n)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hSweep : (C sweep).ctl.tok = .sweep)
    (hPending : PendingOpenROwnerV31 ring C owner)
    (hRead : InSweepWideReadV31 ring C sweep p)
    (hSafe : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  unfold SweepOpenRSafeAtV31 at hSafe ⊢
  rcases hSafe with hClear | hOut
  · by_cases hFoot : InOpenRFreshFootprintV31 ring C owner p
    · have hOwned := hStrong.2 sweep owner p
        hSweep hPending hRead hFoot
      have hc := branch_openNoHazard_open_none4 hψ h2
        (C e) (C (ring.rightNeighbor e)) hb
      have hpe : p ≠ e := by
        intro hp
        subst p
        exact phaseOwned_not_open_none4 (C e) hOwned
          hc.2.2.1 hc.1
      have hpr : p ≠ ring.rightNeighbor e := by
        intro hp
        subst p
        exact phaseOwned_not_open_none4 (C (ring.rightNeighbor e)) hOwned
          hc.2.2.2 hc.2.1
      left
      rw [stepV3_other hψ h2 ring C e p hpe hpr]
      exact hClear
    · right
      intro hFootD
      exact hFoot (openFreshFootprint_after_frame_to_before4
        ring hF owner p hFootD)
  · right
    intro hFootD
    exact hOut (openFreshFootprint_after_frame_to_before4
      ring hF owner p hFootD)


/-- The original Plus3 wide clause is preserved once R2 is strengthened. -/
theorem sweepOpenROverlapClearWide_openNoHazard_of_strongR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  intro sweep owner hSweepD hPendingD
  have hSweepC := hSweepD
  rw [(hF sweep).2.2.2] at hSweepC
  have hPendingC := pending_after_frame_to_before4
    ring hF owner hPendingD
  have hSource := hWide sweep owner hSweepC hPendingC
  constructor
  · have hReadC : InSweepWideReadV31 ring C sweep
        (ring.rightNeighbor sweep) := by
      exact Or.inl rfl
    exact safeAt_openNoHazard_of_strongR2
      hψ h2 ring C e sweep owner (ring.rightNeighbor sweep)
      hStrong hb hSweepC hPendingC hReadC hSource.1
  · intro dD
    have hLabel := congrArg Fin.val (hF sweep).1
    have hdC : dD.val < ψ - (raw (C sweep)).label.val := by
      let m : Nat := dD.val
      have hmD : m < ψ -
          (raw (stepV3 hψ h2 ring C e sweep)).label.val := dD.isLt
      simpa only [hLabel] using hmD
    let dC : Fin (ψ - (raw (C sweep)).label.val) := ⟨dD.val, hdC⟩
    have hOld := hSource.2 dC
    change SweepOpenRSafeAtV31 ring C owner
      (R2Coherence.fwd ring sweep dD.val) at hOld
    have hReadC : InSweepWideReadV31 ring C sweep
        (R2Coherence.fwd ring sweep dD.val) := by
      right
      refine ⟨dC, ?_⟩
      rfl
    exact safeAt_openNoHazard_of_strongR2
      hψ h2 ring C e sweep owner
      (R2Coherence.fwd ring sweep dD.val)
      hStrong hb hSweepC hPendingC hReadC hOld


/-- Hence the old pointwise pair clause is preserved too. -/
theorem sweepOpenROverlapClear_openNoHazard_of_strongR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e) := by
  exact sweepOpenROverlapClearWide_implies_pointwise ring _
    (sweepOpenROverlapClearWide_openNoHazard_of_strongR2
      hψ h2 ring C e hWide hStrong hb)


/-- Direct closure of the STOP case: under strong R2 the allegedly
served/read/in-footprint cell cannot exist, so no physical transport lemma is
needed. -/
theorem openNoHazardSweepReadMainClearTransport_of_strongR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep owner p : Fin n)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hSweep : (C sweep).ctl.tok = .sweep)
    (hPending : PendingOpenROwnerV31 ring C owner)
    (hRead : InSweepWideReadV31 ring C sweep p)
    (hServed : p = e ∨ p = ring.rightNeighbor e)
    (hFoot : InOpenRFreshFootprintV31 ring C owner p)
    (hClear : MainClearV3 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) := by
  have hOwned := hStrong.2 sweep owner p
    hSweep hPending hRead hFoot
  have hc := branch_openNoHazard_open_none4 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  rcases hServed with hpe | hpr
  · subst p
    exact (phaseOwned_not_open_none4 (C e) hOwned
      hc.2.2.1 hc.1).elim
  · subst p
    exact (phaseOwned_not_open_none4 (C (ring.rightNeighbor e)) hOwned
      hc.2.2.2 hc.2.1).elim


/-- Wrapper using the four-field replacement payload. -/
theorem sweepOpenROverlapClearWide_openNoHazard_plus4StrongR2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  exact sweepOpenROverlapClearWide_openNoHazard_of_strongR2
    hψ h2 ring C e hPlus.1.2 hPlus.2.2.2 hb


end R2CoherenceV31ReachableOpenNoHazard4
