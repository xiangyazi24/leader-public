import Leader.Wu.Coherence.SixTokenController
import Leader.Wu.Coherence.SixTokenBranches


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2Coherence
open R2CoherenceBranches


variable {n ψ κ τ width : Nat}


/-! ## CHECK-ready sanitation -/


/-- Wrapper-level CHECK-ready sanitizer. Only malformed/pathless stored
`CHECK_ready` material is retired; quarantine control is untouched. -/
def sanitizeCheckReady (u : Cell ψ κ τ) : Cell ψ κ τ :=
  { u with phys := sanitizeReadyPhys u.phys }


/-- Endpoint form of sanitation inertness. -/
theorem sanitize_inert_of_readyAlignedCell
    (u : Cell ψ κ τ) (h : ReadyAlignedCell u) :
    sanitizeCheckReady u = u := by
  rcases u with ⟨phys, ctl⟩
  change (⟨sanitizeReadyPhys phys, ctl⟩ : Cell ψ κ τ) = ⟨phys, ctl⟩
  have hp : sanitizeReadyPhys phys = phys := by
    apply sanitizeReadyPhys_eq_self
    exact h
  rw [hp]


/-- Requested all-state form: sanitation is literally inert on
`ReadyAlignedAll`. -/
theorem sanitize_inert_of_readyAligned
    (C : FC n ψ κ τ) (h : ReadyAlignedAll C) (i : Fin n) :
    sanitizeCheckReady (C i) = C i :=
  sanitize_inert_of_readyAlignedCell (C i) (h i)


/-- Physical open proposal after CHECK-ready revalidation. -/
def proposalV2 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : R2.Cell ψ κ τ × R2.Cell ψ κ τ :=
  let l' := sanitizeCheckReady l
  let r' := sanitizeCheckReady r
  R2.row hψ hw hle l'.phys r'.phys


/-- V2 no-write predicate is about the proposal that will actually install. -/
def ProposalNoWriteV2
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Prop :=
  let q := proposalV2 hψ hw hle l r
  pairWrites l.phys r.phys q.1 q.2 = false ∧
    pairRelabels l.phys r.phys q.1 q.2 = false


/-- Open lane with sanitation performed before the R2 proposal. -/
def openStageV2 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let q := proposalV2 hψ hw hle l r
  if pairHazard l.phys r.phys q.1 q.2 then
    if endpointHazard r.phys q.2 then
      (l, startClosing r)
    else
      (startClosing l, r)
  else
    (install l q.1, install r q.2)


/-- V2 ordinary lane differs from V1 only in its open/open sublane. -/
def ordinaryStageV2
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then
      sealedStage hψ hw hle l r
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      openStageV2 hψ hw hle l r
    else
      (l, r)
  else
    (l, r)


/-! ## Scheduler-aware reopen certification -/


/-- Literal two-endpoint update used by V2. -/
def pairUpdate (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (q : Cell ψ κ τ × Cell ψ κ τ) : FC n ψ κ τ :=
  fun i =>
    if i = e then q.1
    else if i = ring.rightNeighbor e then q.2
    else C i


/-- RELEASE itself is the V1 physical/control rule. If it would expose a
`.reopen` responder, the prospective full configuration is certified first.
An uncertified release-to-reopen handoff fails closed to sealed controls. -/
def releaseStageV2
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) :
    Cell ψ κ τ × Cell ψ κ τ :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let q := releaseStage l r
  if q.2.ctl.tok = .reopen then
    let D := pairUpdate ring C e q
    if ReopenSuffixClear ring D e then q
    else (setControl l .sealed .none, setControl r .sealed .none)
  else q




private theorem releaseStageV2_eq_release_of_not_reopen
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hTok :
      (releaseStage (C e) (C (ring.rightNeighbor e))).2.ctl.tok ≠ .reopen) :
    releaseStageV2 ring C e =
      releaseStage (C e) (C (ring.rightNeighbor e)) := by
  unfold releaseStageV2
  dsimp only
  rw [if_neg hTok]


private theorem releaseStageV2_eq_release_of_reopen_clear
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hTok :
      (releaseStage (C e) (C (ring.rightNeighbor e))).2.ctl.tok = .reopen)
    (hClear :
      ReopenSuffixClear ring
        (pairUpdate ring C e
          (releaseStage (C e) (C (ring.rightNeighbor e)))) e) :
    releaseStageV2 ring C e =
      releaseStage (C e) (C (ring.rightNeighbor e)) := by
  unfold releaseStageV2
  dsimp only
  rw [if_pos hTok, if_pos hClear]


private theorem releaseStageV2_eq_sealed_of_reopen_not_clear
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hTok :
      (releaseStage (C e) (C (ring.rightNeighbor e))).2.ctl.tok = .reopen)
    (hClear :
      ¬ ReopenSuffixClear ring
        (pairUpdate ring C e
          (releaseStage (C e) (C (ring.rightNeighbor e)))) e) :
    releaseStageV2 ring C e =
      (setControl (C e) .sealed .none,
       setControl (C (ring.rightNeighbor e)) .sealed .none) := by
  unfold releaseStageV2
  dsimp only
  rw [if_pos hTok, if_neg hClear]

theorem releaseStageV2_reopen_suffix
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) :
    let q := releaseStageV2 ring C e
    q.2.ctl.tok = .reopen →
      ReopenSuffixClear ring (pairUpdate ring C e q) e := by
  dsimp only
  by_cases hTok :
      (releaseStage (C e) (C (ring.rightNeighbor e))).2.ctl.tok = .reopen
  · by_cases hClear :
      ReopenSuffixClear ring
        (pairUpdate ring C e
          (releaseStage (C e) (C (ring.rightNeighbor e)))) e
    · have hEq := releaseStageV2_eq_release_of_reopen_clear
        ring C e hTok hClear
      rw [hEq]
      intro _
      exact hClear
    · have hEq := releaseStageV2_eq_sealed_of_reopen_not_clear
        ring C e hTok hClear
      rw [hEq]
      intro h
      have hbad : Token.none = Token.reopen := by
        simpa [setControl] using h
      cases hbad
  · have hEq := releaseStageV2_eq_release_of_not_reopen
      ring C e hTok
    rw [hEq]
    intro h
    exact (hTok h).elim



/-- REOPEN executes only under the full current-state suffix certificate. -/
def reopenStageV2
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) :
    Cell ψ κ τ × Cell ψ κ τ :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  if ReopenSuffixClear ring C e then
    reopenStage l r
  else
    (l, r)


theorem reopenStageV2_of_suffixClear
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (h : ReopenSuffixClear ring C e) :
    reopenStageV2 ring C e =
      reopenStage (C e) (C (ring.rightNeighbor e)) := by
  simp [reopenStageV2, h]


theorem reopenStageV2_fail_closed
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (h : ¬ ReopenSuffixClear ring C e) :
    reopenStageV2 ring C e = (C e, C (ring.rightNeighbor e)) := by
  simp [reopenStageV2, h]


/-! ## V2 row, step and branch classifier -/


/-- Scheduler-aware V2 row. Token priority is unchanged. -/
def rowV2
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) :
    Cell ψ κ τ × Cell ψ κ τ :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  if r.ctl.tok = .seek then seekStage l r
  else if l.ctl.tok = .sweep then sweepStage l r
  else if r.ctl.tok = .commit then commitStage l r
  else if l.ctl.tok = .release then releaseStageV2 ring C e
  else if r.ctl.tok = .reopen then reopenStageV2 ring C e
  else ordinaryStageV2 hψ hw hle l r


/-- Full-ring V2 step. A local PopulationProtocol transition is intentionally
not used because the reopen certificate is a current global suffix fact. -/
def stepV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  pairUpdate ring C e
    (rowV2 hψ (by decide : 0 < 2) h2 ring C e)


/-- V2 branch class, mirroring `rowV2`; reopen remains the selected branch even
when its certificate guard makes the physical step fail closed. -/
def branchAtV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : Branch :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  if r.ctl.tok = .seek then .seek
  else if l.ctl.tok = .sweep then .sweep
  else if r.ctl.tok = .commit then .commit
  else if l.ctl.tok = .release then .release
  else if r.ctl.tok = .reopen then .reopen
  else if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then
      .sealed
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      let q := proposalV2 hψ (by decide : 0 < 2) h2 l r
      if pairHazard l.phys r.phys q.1 q.2 then .openHazard
      else .openNoHazard
    else .mixed
  else .mixed


/-! ## Exact aligned open-lane agreement -/


/-- On aligned endpoints the new proposal is literally the old R2 proposal. -/
theorem proposalV2_eq_proposal_of_aligned
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : ReadyAlignedCell l) (hr : ReadyAlignedCell r) :
    proposalV2 hψ hw hle l r = proposal hψ hw hle l r := by
  unfold proposalV2 proposal
  rw [sanitize_inert_of_readyAlignedCell l hl,
    sanitize_inert_of_readyAlignedCell r hr]


/-- Requested local agreement theorem: open controls, aligned stored ready
states and a silent V2 proposal reduce exactly to the physical R2 row. -/
theorem row_eq_r2_of_open_no_write_aligned
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hl : ReadyAlignedCell (C e))
    (hr : ReadyAlignedCell (C (ring.rightNeighbor e)))
    (hlm : (C e).ctl.mark = .open)
    (hrm : (C (ring.rightNeighbor e)).ctl.mark = .open)
    (hlt : (C e).ctl.tok = .none)
    (hrt : (C (ring.rightNeighbor e)).ctl.tok = .none)
    (hsafe : ProposalNoWriteV2 hψ hw hle
      (C e) (C (ring.rightNeighbor e))) :
    rowV2 hψ hw hle ring C e =
      (install (C e)
          (proposal hψ hw hle (C e) (C (ring.rightNeighbor e))).1,
       install (C (ring.rightNeighbor e))
          (proposal hψ hw hle (C e) (C (ring.rightNeighbor e))).2) := by
  have hq := proposalV2_eq_proposal_of_aligned
    hψ hw hle (C e) (C (ring.rightNeighbor e)) hl hr
  change
    pairWrites (C e).phys (C (ring.rightNeighbor e)).phys
        (proposalV2 hψ hw hle (C e) (C (ring.rightNeighbor e))).1
        (proposalV2 hψ hw hle (C e) (C (ring.rightNeighbor e))).2 = false ∧
      pairRelabels (C e).phys (C (ring.rightNeighbor e)).phys
        (proposalV2 hψ hw hle (C e) (C (ring.rightNeighbor e))).1
        (proposalV2 hψ hw hle (C e) (C (ring.rightNeighbor e))).2 = false
    at hsafe
  rw [hq] at hsafe
  rcases hsafe with ⟨hwrite, hlabel⟩
  simp [rowV2, ordinaryStageV2, openStageV2, hq, pairHazard,
    hlm, hrm, hlt, hrt, hwrite, hlabel]


/-- Edge form of the V2 no-write premise. -/
def NoHazardAtV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : Prop :=
  ProposalNoWriteV2 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))




private def pairUpdateRaw {X : Type}
    (ring : DirectedRing n) (C : Fin n → X) (e : Fin n)
    (q : X × X) : Fin n → X :=
  fun i =>
    if i = e then q.1
    else if i = ring.rightNeighbor e then q.2
    else C i


private theorem stepV2_eq_pairUpdateRaw
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    stepV2 hψ h2 ring C e =
      pairUpdateRaw ring C e
        (rowV2 hψ (by decide : 0 < 2) h2 ring C e) := by
  rfl


private theorem r2_step_eq_pairUpdateRaw
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (D : R2.FC n ψ κ τ) (e : Fin n) :
    R2.step hψ h2 ring D e =
      pairUpdateRaw ring D e
        (R2.row hψ (by decide : 0 < 2) h2
          (D e) (D (ring.rightNeighbor e))) := by
  rfl


private theorem project_pairUpdateRaw
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (q : Cell ψ κ τ × Cell ψ κ τ) :
    project (pairUpdateRaw ring C e q) =
      pairUpdateRaw ring (project C) e (q.1.phys, q.2.phys) := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [pairUpdateRaw, project]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [pairUpdateRaw, project, hie]
    · simp [pairUpdateRaw, project, hie, hij]

theorem project_stepV2_of_open_no_write_aligned
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hOpen : AllOpen C) (hReady : ReadyAlignedAll C)
    (hNo : NoHazardAtV2 hψ h2 ring C e) :
    project (stepV2 hψ h2 ring C e) =
      R2.step hψ h2 ring (project C) e := by
  have hl := hOpen e
  have hr := hOpen (ring.rightNeighbor e)
  rcases hl with ⟨hlm, hlt⟩
  rcases hr with ⟨hrm, hrt⟩
  have hrow := row_eq_r2_of_open_no_write_aligned
    hψ (by decide : 0 < 2) h2 ring C e
    (hReady e) (hReady (ring.rightNeighbor e))
    hlm hrm hlt hrt hNo
  have hphys :
      ((rowV2 hψ (by decide : 0 < 2) h2 ring C e).1.phys,
       (rowV2 hψ (by decide : 0 < 2) h2 ring C e).2.phys) =
        R2.row hψ (by decide : 0 < 2) h2
          (project C e) (project C (ring.rightNeighbor e)) := by
    rw [hrow]
    rfl
  calc
    project (stepV2 hψ h2 ring C e) =
        project
          (pairUpdateRaw ring C e
            (rowV2 hψ (by decide : 0 < 2) h2 ring C e)) := by
      rw [stepV2_eq_pairUpdateRaw hψ h2 ring C e]
    _ = pairUpdateRaw ring (project C) e
        ((rowV2 hψ (by decide : 0 < 2) h2 ring C e).1.phys,
         (rowV2 hψ (by decide : 0 < 2) h2 ring C e).2.phys) :=
      project_pairUpdateRaw ring C e
        (rowV2 hψ (by decide : 0 < 2) h2 ring C e)
    _ = pairUpdateRaw ring (project C) e
        (R2.row hψ (by decide : 0 < 2) h2
          (project C e) (project C (ring.rightNeighbor e))) := by
      rw [hphys]
    _ = R2.step hψ h2 ring (project C) e := by
      symm
      exact r2_step_eq_pairUpdateRaw hψ h2 ring (project C) e



/-- The R2→R1 physical obligation is unchanged. Under the aligned open-lane
hypotheses, V2 therefore inherits the same leaderless statement. -/
theorem leaderless_agreementV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hR2 : R2R1AgreementObligation (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hOpen : AllOpen C) (hReady : ReadyAlignedAll C)
    (hNo : NoHazardAtV2 hψ h2 ring C e)
    (hLead : R2.Leaderless (project C))
    (hProd : R2.NoProducer (project C)) :
    baseProject (stepV2 hψ h2 ring C e) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring (baseProject C) e := by
  have hp := project_stepV2_of_open_no_write_aligned
    hψ h2 ring C e hOpen hReady hNo
  change (fun i => (project (stepV2 hψ h2 ring C e) i).base) = _
  rw [hp]
  exact hR2 (project C) e hLead hProd


/-! ## V2 branch obligations -/


/-- One V2 branch's exact global coherence obligation. -/
def BranchPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : Branch) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    AdmittedPostBirthGeometry hψ ring C →
    CoherentPrefixes ring C →
    branchAtV2 hψ h2 ring C e = b →
    CoherentPrefixes ring (stepV2 hψ h2 ring C e)


def SeekPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .seek


def SweepPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .sweep


def CommitPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .commit


def ReleasePreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .release


def ReopenPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .reopen


def SealedPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .sealed


def OpenHazardPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .openHazard


def OpenNoHazardPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .openNoHazard


def MixedPreservationObligationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring .mixed


/-! ## Seven monotone V2 branches -/


private theorem quarantineMutation_stepV2_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPair : PairQuarantineMutation
      (C e) (C (ring.rightNeighbor e))
      (rowV2 hψ (by decide : 0 < 2) h2 ring C e)) :
    QuarantineMutation C (stepV2 hψ h2 ring C e) := by
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [stepV2, pairUpdate] using (And.intro hLM hLN)
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [stepV2, pairUpdate, hpe] using (And.intro hRM hRN)
    · have hSame :
          ((C p).phys ≠ (C p).phys → NonOpen (C p)) ∧
            (NonOpen (C p) → NonOpen (C p)) :=
        ⟨fun h => (h rfl).elim, fun h => h⟩
      simpa [stepV2, pairUpdate, hpe, hpj] using hSame





private theorem pairMutation_selfV2_local
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation l r (l, r) := by
  simp [PairQuarantineMutation]


private theorem pairMutation_seekStageV2_local
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation l r (seekStage l r) := by
  unfold seekStage
  split
  · simp [PairQuarantineMutation, NonOpen, setControl]
  · split
    · simp [PairQuarantineMutation, NonOpen, setControl]
    · simp [PairQuarantineMutation, NonOpen, setControl]


private theorem pairMutation_sweepStageV2_local
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation l r (sweepStage l r) := by
  unfold sweepStage
  split
  · simp [PairQuarantineMutation, NonOpen, setControl]
  · exact pairMutation_selfV2_local l r


private theorem pairMutation_commitStageV2_local
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation l r (commitStage l r) := by
  unfold commitStage
  dsimp only
  split
  · simp [PairQuarantineMutation, NonOpen, setControl]
  · split
    · simp [PairQuarantineMutation, NonOpen, setControl]
    · simp [PairQuarantineMutation, NonOpen, setControl]


private theorem pairMutation_releaseStage_rawV2_local
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation l r (releaseStage l r) := by
  unfold releaseStage
  split
  · split
    · simp [PairQuarantineMutation, NonOpen, setControl]
    · split
      · simp [PairQuarantineMutation, NonOpen, setControl]
      · simp [PairQuarantineMutation, NonOpen, setControl]
  · exact pairMutation_selfV2_local l r


private theorem pairMutation_releaseStageV2_local
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) :
    PairQuarantineMutation
      (C e) (C (ring.rightNeighbor e))
      (releaseStageV2 ring C e) := by
  have hBase :
      PairQuarantineMutation
        (C e) (C (ring.rightNeighbor e))
        (releaseStage (C e) (C (ring.rightNeighbor e))) :=
    pairMutation_releaseStage_rawV2_local
      (C e) (C (ring.rightNeighbor e))
  by_cases hTok :
      (releaseStage (C e) (C (ring.rightNeighbor e))).2.ctl.tok = .reopen
  · by_cases hClear :
      ReopenSuffixClear ring
        (pairUpdate ring C e
          (releaseStage (C e) (C (ring.rightNeighbor e)))) e
    · rw [releaseStageV2_eq_release_of_reopen_clear
        ring C e hTok hClear]
      exact hBase
    · rw [releaseStageV2_eq_sealed_of_reopen_not_clear
        ring C e hTok hClear]
      simp [PairQuarantineMutation, NonOpen, setControl]
  · rw [releaseStageV2_eq_release_of_not_reopen ring C e hTok]
    exact hBase


private theorem pairMutation_sealedStageV2_local
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : l.ctl.mark = .sealed) (hr : r.ctl.mark = .sealed) :
    PairQuarantineMutation l r
      (sealedStage hψ (by decide : 0 < 2) h2 l r) := by
  unfold sealedStage
  split
  · simp [PairQuarantineMutation, NonOpen, setControl, hl, hr]
  · dsimp only
    split
    · exact pairMutation_selfV2_local l r
    · simp [PairQuarantineMutation, NonOpen, install, hl, hr]


private theorem pairMutation_openStageV2_of_hazard_local
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hHaz :
      pairHazard l.phys r.phys
        (proposalV2 hψ (by decide : 0 < 2) h2 l r).1
        (proposalV2 hψ (by decide : 0 < 2) h2 l r).2 = true) :
    PairQuarantineMutation l r
      (openStageV2 hψ (by decide : 0 < 2) h2 l r) := by
  unfold openStageV2
  dsimp only
  rw [if_pos hHaz]
  split
  · simp [PairQuarantineMutation, NonOpen, startClosing, setControl]
  · simp [PairQuarantineMutation, NonOpen, startClosing, setControl]

private theorem pairMutation_of_monotone_branchV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (b : Branch)
    (hb : branchAtV2 hψ h2 ring C e = b)
    (hReopen : b ≠ .reopen) (hOpen : b ≠ .openNoHazard) :
    PairQuarantineMutation
      (C e) (C (ring.rightNeighbor e))
      (rowV2 hψ (by decide : 0 < 2) h2 ring C e) := by
  have hb' := hb
  unfold branchAtV2 at hb'
  dsimp only at hb'
  unfold rowV2
  dsimp only
  by_cases hSeek : (C (ring.rightNeighbor e)).ctl.tok = .seek
  · rw [if_pos hSeek]
    exact pairMutation_seekStageV2_local
      (C e) (C (ring.rightNeighbor e))
  · rw [if_neg hSeek]
    rw [if_neg hSeek] at hb'
    by_cases hSweep : (C e).ctl.tok = .sweep
    · rw [if_pos hSweep]
      exact pairMutation_sweepStageV2_local
        (C e) (C (ring.rightNeighbor e))
    · rw [if_neg hSweep]
      rw [if_neg hSweep] at hb'
      by_cases hCommit : (C (ring.rightNeighbor e)).ctl.tok = .commit
      · rw [if_pos hCommit]
        exact pairMutation_commitStageV2_local
          (C e) (C (ring.rightNeighbor e))
      · rw [if_neg hCommit]
        rw [if_neg hCommit] at hb'
        by_cases hRelease : (C e).ctl.tok = .release
        · rw [if_pos hRelease]
          exact pairMutation_releaseStageV2_local ring C e
        · rw [if_neg hRelease]
          rw [if_neg hRelease] at hb'
          by_cases hReopenTok :
              (C (ring.rightNeighbor e)).ctl.tok = .reopen
          · rw [if_pos hReopenTok] at hb'
            exact (hReopen hb'.symm).elim
          · rw [if_neg hReopenTok]
            rw [if_neg hReopenTok] at hb'
            by_cases hNone :
                (C e).ctl.tok = .none ∧
                  (C (ring.rightNeighbor e)).ctl.tok = .none
            · rw [if_pos hNone] at hb'
              unfold ordinaryStageV2
              rw [if_pos hNone]
              by_cases hSealed :
                  (C e).ctl.mark = .sealed ∧
                    (C (ring.rightNeighbor e)).ctl.mark = .sealed
              · rw [if_pos hSealed]
                exact pairMutation_sealedStageV2_local hψ h2
                  (C e) (C (ring.rightNeighbor e))
                  hSealed.1 hSealed.2
              · rw [if_neg hSealed] at hb'
                rw [if_neg hSealed]
                by_cases hOpenCtl :
                    (C e).ctl.mark = .open ∧
                      (C (ring.rightNeighbor e)).ctl.mark = .open
                · rw [if_pos hOpenCtl] at hb'
                  try dsimp only at hb'
                  rw [if_pos hOpenCtl]
                  by_cases hHaz :
                      pairHazard
                        (C e).phys
                        (C (ring.rightNeighbor e)).phys
                        (proposalV2 hψ (by decide : 0 < 2) h2
                          (C e) (C (ring.rightNeighbor e))).1
                        (proposalV2 hψ (by decide : 0 < 2) h2
                          (C e) (C (ring.rightNeighbor e))).2 = true
                  · exact pairMutation_openStageV2_of_hazard_local hψ h2
                      (C e) (C (ring.rightNeighbor e)) hHaz
                  · rw [if_neg hHaz] at hb'
                    exact (hOpen hb'.symm).elim
                · rw [if_neg hOpenCtl]
                  exact pairMutation_selfV2_local
                    (C e) (C (ring.rightNeighbor e))
            · unfold ordinaryStageV2
              rw [if_neg hNone]
              exact pairMutation_selfV2_local
                (C e) (C (ring.rightNeighbor e))



private theorem monotoneBranchPreservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (b : Branch)
    (hReopen : b ≠ .reopen) (hOpen : b ≠ .openNoHazard) :
    BranchPreservationObligationV2
      (κ := κ) (τ := τ) hψ h2 ring b := by
  intro C e _hGeom hC hb
  apply coherentPrefixes_of_quarantineMutation ring
    (C := C) (D := stepV2 hψ h2 ring C e)
  · exact quarantineMutation_stepV2_of_pair hψ h2 ring C e
      (pairMutation_of_monotone_branchV2
        hψ h2 ring C e b hb hReopen hOpen)
  · exact hC


theorem seek_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SeekPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .seek (by decide) (by decide)


theorem sweep_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SweepPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .sweep (by decide) (by decide)


theorem commit_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    CommitPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .commit (by decide) (by decide)


theorem release_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ReleasePreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .release (by decide) (by decide)


theorem sealed_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SealedPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .sealed (by decide) (by decide)


theorem openHazard_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    OpenHazardPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .openHazard (by decide) (by decide)


theorem mixed_preservationV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    MixedPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring := by
  exact monotoneBranchPreservationV2 (κ := κ) (τ := τ)
    hψ h2 ring .mixed (by decide) (by decide)


/-- Bundle interface. The corrected reopen and open/no-hazard obligations are
left as the two named semantic leaves; the other seven are discharged above. -/
structure PreservationObligationsV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop where
  seek : SeekPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring
  sweep : SweepPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring
  commit : CommitPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring
  release : ReleasePreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring
  reopen : ReopenPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring
  sealed : SealedPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring
  openHazard : OpenHazardPreservationObligationV2
    (κ := κ) (τ := τ) hψ h2 ring
  openNoHazard : OpenNoHazardPreservationObligationV2
    (κ := κ) (τ := τ) hψ h2 ring
  mixed : MixedPreservationObligationV2 (κ := κ) (τ := τ) hψ h2 ring


/-- V2 dispatcher once the two repaired semantic leaves are supplied. -/
theorem coherentPrefixes_stepV2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hO : PreservationObligationsV2 (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ)
    (hGeom : AdmittedPostBirthGeometry hψ ring C)
    (hC : CoherentPrefixes ring C) (e : Fin n) :
    CoherentPrefixes ring (stepV2 hψ h2 ring C e) := by
  cases hb : branchAtV2 hψ h2 ring C e with
  | seek => exact hO.seek C e hGeom hC hb
  | sweep => exact hO.sweep C e hGeom hC hb
  | commit => exact hO.commit C e hGeom hC hb
  | release => exact hO.release C e hGeom hC hb
  | reopen => exact hO.reopen C e hGeom hC hb
  | sealed => exact hO.sealed C e hGeom hC hb
  | openHazard => exact hO.openHazard C e hGeom hC hb
  | openNoHazard => exact hO.openNoHazard C e hGeom hC hb
  | mixed => exact hO.mixed C e hGeom hC hb


/-! ## Closed ψ=3 regressions for the two counterexamples -/


namespace Regression


private abbrev PCfg := R2.FC 3 3 3 48
private abbrev WCfg := FC 3 3 3 48


private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩


/-- Same complete literal used by the two counterexamples. -/
private def literal (i : Fin 3)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (bit : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) i
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      state := state
      path := path
      bit := bit
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


private def openCell (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.open, .none⟩⟩


/-! ### openNoHazard counterexample, now sanitized -/


private def badReadyInput : WCfg := fun i =>
  match i.val with
  | 0 => openCell (literal 0 .equal (.some 0 0))
  | 1 => openCell (literal 1 .CHECK_ready (.some 0 0))
  | _ => openCell (literal 2 .none .bot)


private def badReadyAfterV2 : WCfg :=
  stepV2 h3 h23 ring3 badReadyInput 0


/-- The forged resident-label-1 / payload-label-0 CHECK_ready is cleared before
R2 sees it. This is a closed field image only. -/
theorem badReady_sanitized_fields :
    let u := sanitizeCheckReady (badReadyInput 1)
    (raw u).label = (1 : Fin 3) ∧
      (raw u).state = .none ∧
      (raw u).path = .bot := by
  decide +kernel


/-- The exact old bad image (equal + stale label-0 payload + open control) is
not produced by the V2 service. -/
theorem badReady_v2_blocked_fields :
    ¬ ((raw (badReadyAfterV2 1)).state = .equal ∧
      (raw (badReadyAfterV2 1)).path = .some 0 0 ∧
      (badReadyAfterV2 1).ctl = ⟨.open, .none⟩) := by
  decide +kernel


/-! ### Reopen counterexample, now fail-closed -/


private def reopenPhys : PCfg := fun i =>
  match i.val with
  | 0 => literal 0 .none (.some 0 0)
  | 1 => literal 1 .none (.some 1 0)
  | _ => literal 2 .equal (.some 2 0)


private def reopenInput : WCfg := fun i =>
  match i.val with
  | 0 => openCell (reopenPhys 0)
  | 1 => ⟨reopenPhys 1, ⟨.releasing, .reopen⟩⟩
  | _ => openCell (reopenPhys 2)


private def reopenAfterV2 : WCfg :=
  stepV2 h3 h23 ring3 reopenInput 0


/-- The malformed final token does not carry the new suffix certificate. -/
theorem reopen_v2_guard_rejects :
    ¬ ReopenSuffixClear ring3 reopenInput 0 := by
  decide +kernel


/-- Therefore the old destructive final reopen is not executed: the root path
is not cleared, the token remains held, and the remote equal frontier is left
behind the still-present non-open witness. -/
theorem reopen_v2_blocked_fields :
    (raw (reopenAfterV2 0)).path = .some 0 0 ∧
      (reopenAfterV2 1).ctl = ⟨.releasing, .reopen⟩ ∧
      (raw (reopenAfterV2 2)).state = .equal ∧
      (raw (reopenAfterV2 2)).path = .some 2 0 := by
  decide +kernel


end Regression


end R2CoherenceV2
