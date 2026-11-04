import Leader.Wu.Coherence.ReopenController
import Leader.Wu.Birth.LeaderlessBirthMassRenewal

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2Coherence R2CoherenceBranches R2CoherenceV2
open BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ width : Nat}

/-- Seven local token values.  Together with the existing four marks this is
exactly 4 * 7 = 28 controller combinations. -/
inductive TokenV3 where
  | none
  | seek
  | sweep
  | commit
  | release
  | scrubL
  | openR
  deriving DecidableEq, Repr

structure ControlV3 where
  mark : Mark
  tok : TokenV3
  deriving DecidableEq, Repr

structure Cell (ψ κ τ : Nat) where
  phys : R2.Cell ψ κ τ
  ctl : ControlV3
  deriving DecidableEq

abbrev FC (n ψ κ τ : Nat) := Fin n → Cell ψ κ τ

def controllerStateCountV3 : Nat := 4 * 7

theorem controllerStateCountV3_eq : controllerStateCountV3 = 28 := by
  decide

def raw (u : Cell ψ κ τ) : BoundedAgentState ψ κ :=
  u.phys.base.core.core

/-- Proof projection only.  `scrubL` and `openR` are both non-none for the
old `PrefixDead` predicate; no executable V3 guard consults this erasure. -/
def eraseTokenV3 : TokenV3 → R2Coherence.Token
  | .none => .none
  | .seek => .seek
  | .sweep => .sweep
  | .commit => .commit
  | .release => .release
  | .scrubL => .reopen
  | .openR => .reopen

def eraseCellV3 (u : Cell ψ κ τ) : R2Coherence.Cell ψ κ τ :=
  ⟨u.phys, ⟨u.ctl.mark, eraseTokenV3 u.ctl.tok⟩⟩

def eraseCfgV3 (C : FC n ψ κ τ) : R2Coherence.FC n ψ κ τ :=
  fun i => eraseCellV3 (C i)

def install (u : Cell ψ κ τ) (p : R2.Cell ψ κ τ) : Cell ψ κ τ :=
  { u with phys := p }

def setControl (u : Cell ψ κ τ) (m : Mark) (t : TokenV3) : Cell ψ κ τ :=
  { u with ctl := ⟨m, t⟩ }

def clearMain (u : Cell ψ κ τ) : Cell ψ κ τ :=
  { u with phys := R2Coherence.clearMainPhys u.phys }

def proposalV3 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : R2.Cell ψ κ τ × R2.Cell ψ κ τ :=
  R2.row hψ hw hle
    (sanitizeReadyPhys l.phys) (sanitizeReadyPhys r.phys)

def sealedProposalV3 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : R2.Cell ψ κ τ × R2.Cell ψ κ τ :=
  let q := R2.row hψ hw hle
    (R2Coherence.clearMainPhys l.phys)
    (R2Coherence.clearMainPhys r.phys)
  (R2Coherence.clearMainPhys q.1, R2Coherence.clearMainPhys q.2)

def pathChangedV3 (old out : R2.Cell ψ κ τ) : Bool :=
  decide (old.base.core.core.path ≠ out.base.core.core.path)

def pairPathChangesV3
    (l r ql qr : R2.Cell ψ κ τ) : Bool :=
  pathChangedV3 l ql || pathChangedV3 r qr

def endpointHazardV3 (old out : R2.Cell ψ κ τ) : Bool :=
  R2Coherence.endpointHazard old out || pathChangedV3 old out

def pairHazardV3
    (l r ql qr : R2.Cell ψ κ τ) : Bool :=
  R2Coherence.pairHazard l r ql qr || pairPathChangesV3 l r ql qr

def atRootB (u : Cell ψ κ τ) : Bool :=
  decide ((raw u).label.val = 0)

def atTerminalB (u : Cell ψ κ τ) : Bool :=
  decide ((raw u).label.val + 1 = ψ)

def successorB (l r : Cell ψ κ τ) : Bool :=
  decide ((raw r).label.val = (raw l).label.val + 1)

def writerQuiet (u : Cell ψ κ τ) : Bool :=
  decide ((raw u).path3 = none ∧
    (raw u).write_state = .none ∧ (raw u).write = .none)

def startClosing (u : Cell ψ κ τ) : Cell ψ κ τ :=
  setControl u .closing .seek

def seekStageV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if atRootB r then
    (l, setControl r .closing .sweep)
  else if atRootB l then
    (setControl l .closing .sweep, setControl r .closing .none)
  else
    (setControl l .closing .seek, setControl r .closing .none)

/-- A malformed active sweep edge restarts the left-seeking reset instead of
holding a forged phase forever. -/
def sweepStageV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    let l' := setControl (clearMain l) .closing .none
    let r' := setControl (clearMain r) .closing
      (if atTerminalB r then .commit else .sweep)
    (l', r')
  else
    (startClosing l, r)

def commitStageV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let r' := setControl (clearMain r) .sealed .none
  if atRootB r then
    (l, r')
  else if atRootB l then
    (setControl (clearMain l) .sealed .none, r')
  else
    (setControl (clearMain l) .closing .commit, r')

/-- Rightward quiescence scan.  Terminal success emits `scrubL`, never
`openR` directly. -/
def releaseStageV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    if writerQuiet r then
      let l' := setControl l .releasing .none
      let r' := setControl r .releasing
        (if atTerminalB r then .scrubL else .release)
      (l', r')
    else if atRootB l then
      (setControl l .sealed .none, r)
    else
      (setControl l .closing .commit, r)
  else
    (startClosing l, r)

/-- Backward exposure scrub.  A root responder is not a valid predecessor of
this wave; such garbage is converted to a fresh seek. -/
def scrubLStageV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    if atRootB r then
      (l, startClosing r)
    else
      let l' := clearMain l
      let r' := setControl (clearMain r) .releasing .none
      if atRootB l then
        (setControl l' .releasing .openR, r')
      else
        (setControl l' .releasing .scrubL, r')
  else
    (l, startClosing r)

/-- Forward reopening wave.  Invalid geometry restarts quarantine.  The
terminal service is the only service which consumes `openR`. -/
def openRStageV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    let l' := clearMain l
    let r' := clearMain r
    if atTerminalB r then
      (setControl l' .open .none, setControl r' .open .none)
    else
      (setControl l' .open .none, setControl r' .releasing .openR)
  else
    (startClosing l, r)

/-- Open lane with CHECK-ready sanitation and the main-path dependency. -/
def openStageV3 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let q := proposalV3 hψ hw hle l r
  if pairHazardV3 l.phys r.phys q.1 q.2 then
    if endpointHazardV3 r.phys q.2 then
      (l, startClosing r)
    else
      (startClosing l, r)
  else
    (install l q.1, install r q.2)

def sealedStageV3 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if atRootB l && successorB l r && writerQuiet l && writerQuiet r then
    (setControl l .releasing .release, r)
  else
    let q := sealedProposalV3 hψ hw hle l r
    if R2Coherence.pairRelabels l.phys r.phys q.1 q.2 then
      (l, r)
    else
      (install l q.1, install r q.2)



/-- A pair has exactly the local label shape of an admitted directed edge:
either it enters a root/leader boundary, or it is a non-wrap successor edge. -/
def passiveEdgeOKV3 (l r : Cell ψ κ τ) : Bool :=
  atRootB r || successorB l r


/-- Recovery for tokenless mixed/passive controls.
On a locally admitted edge, fail closed into the existing seek/sweep/commit
quarantine.  On a locally impossible edge, clear only main comparison material
and reopen the pair so malformed physical geometry is not frozen forever. -/
def normalizePassiveV3
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if passiveEdgeOKV3 l r then
    (l, startClosing r)
  else
    (setControl (clearMain l) .open .none,
     setControl (clearMain r) .open .none)


theorem normalizePassiveV3_good_edge
    (l r : Cell ψ κ τ) (h : passiveEdgeOKV3 l r = true) :
    normalizePassiveV3 l r = (l, startClosing r) := by
  simp [normalizePassiveV3, h]


theorem normalizePassiveV3_bad_edge
    (l r : Cell ψ κ τ) (h : passiveEdgeOKV3 l r = false) :
    normalizePassiveV3 l r =
      (setControl (clearMain l) .open .none,
       setControl (clearMain r) .open .none) := by
  simp [normalizePassiveV3, h]


/-- The arm used on admitted/recovered edges is physically inert. -/
theorem normalizePassiveV3_good_edge_physical
    (l r : Cell ψ κ τ) (h : passiveEdgeOKV3 l r = true) :
    (normalizePassiveV3 l r).1.phys = l.phys ∧
      (normalizePassiveV3 l r).2.phys = r.phys := by
  rw [normalizePassiveV3_good_edge l r h]
  simp [startClosing, setControl]

def ordinaryStageV3
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then
      sealedStageV3 hψ hw hle l r
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      openStageV3 hψ hw hle l r
    else
      normalizePassiveV3 l r
  else
    (l, r)


/-- Pure radius-one transition: no `ring`, configuration, `groupPos`, history,
or proof certificate occurs in the type. -/
def rowV3
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if r.ctl.tok = .seek then seekStageV3 l r
  else if l.ctl.tok = .sweep then sweepStageV3 l r
  else if r.ctl.tok = .commit then commitStageV3 l r
  else if l.ctl.tok = .release then releaseStageV3 l r
  else if r.ctl.tok = .scrubL then scrubLStageV3 l r
  else if l.ctl.tok = .openR then openRStageV3 l r
  else ordinaryStageV3 hψ hw hle l r

def protocolV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := Cell ψ κ τ
  Y := Bool
  transition := rowV3 hψ (by decide : 0 < 2) h2
  output := fun u => (raw u).leader

def stepV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (protocolV3 hψ h2 κ τ).step ring C e

inductive BranchV3 where
  | seek | sweep | commit | release | scrubL | openR
  | sealed | openHazard | openNoHazard | mixed
  deriving DecidableEq, Repr

def branchAtV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) : BranchV3 :=
  if r.ctl.tok = .seek then .seek
  else if l.ctl.tok = .sweep then .sweep
  else if r.ctl.tok = .commit then .commit
  else if l.ctl.tok = .release then .release
  else if r.ctl.tok = .scrubL then .scrubL
  else if l.ctl.tok = .openR then .openR
  else if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then .sealed
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
      if pairHazardV3 l.phys r.phys q.1 q.2 then .openHazard
      else .openNoHazard
    else .mixed
  else .mixed

/-- Literal pair-locality certificate for the installed protocol. -/
theorem protocolV3_transition
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    (protocolV3 hψ h2 κ τ).transition =
      rowV3 hψ (by decide : 0 < 2) h2 := by
  rfl

theorem stepV3_other
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepV3 hψ h2 ring C e i = C i := by
  simp [stepV3, protocolV3, PopulationProtocol.step, hi, hj]

/-- These are proof predicates only. -/
def MainClearV3 (u : Cell ψ κ τ) : Prop :=
  R2CoherenceBranches.MainClear (eraseCellV3 u)

def GroupMainClearV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Prop :=
  ∀ k : Fin ψ,
    MainClearV3
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val))

def IntrinsicFreshAtV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Prop :=
  (raw (C i)).state = .equal →
    ∀ k : Fin ((raw (C i)).label.val + 1),
      R2Coherence.freshComponent
        (eraseCellV3
          (C (R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val))) k.val

def GroupIntrinsicFreshV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Prop :=
  ∀ k : Fin ψ,
    IntrinsicFreshAtV3 ring C
      (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val)

/-- Every arithmetic `psi`-window whose `groupPos` scan contains an `openR`
owner is intrinsically fresh.  This exactly covers every window for which the
owner can serve as a `PrefixDead` witness. -/
def OpenROwnerFreshV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (owner : Fin n) : Prop :=
  ∀ j : Fin n, ∀ k : Fin ψ,
    R2Coherence.groupPos ring (eraseCfgV3 C) j k.val = owner →
      GroupIntrinsicFreshV3 ring C j

instance openROwnerFreshV3Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) (owner : Fin n) :
    Decidable (OpenROwnerFreshV3 ring C owner) := by
  unfold OpenROwnerFreshV3 GroupIntrinsicFreshV3 IntrinsicFreshAtV3
  infer_instance

def ControllerShapeV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (C i).ctl.mark = .sealed → GroupMainClearV3 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .release →
      (C i).ctl.mark = .releasing ∧ GroupMainClearV3 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .scrubL →
      (C i).ctl.mark = .releasing ∧
      (raw (C i)).label.val ≠ 0 ∧ GroupMainClearV3 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .openR →
      (C i).ctl.mark = .releasing ∧ OpenROwnerFreshV3 ring C i)


instance controllerShapeV3Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (ControllerShapeV3 ring C) := by
  unfold ControllerShapeV3 OpenROwnerFreshV3 GroupMainClearV3
    GroupIntrinsicFreshV3 IntrinsicFreshAtV3 MainClearV3
  infer_instance


/-- Proof-side forward-closed controller invariant.  It is deliberately NOT a
runtime guard.  Empty word gives the current structural shape; quantified future
words say forged completion phases cannot recur after the first hit. -/
def ControllerSoundV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  ∀ w : List (Fin n),
    ControllerShapeV3 ring (w.foldl (stepV3 hψ h2 ring) C)

theorem controllerSoundV3_shape
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (h : ControllerSoundV3 hψ h2 ring C) :
    ControllerShapeV3 ring C := by
  simpa [ControllerSoundV3] using h []

theorem controllerSoundV3_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ControllerSoundV3 hψ h2 ring C) :
    ControllerSoundV3 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  unfold ControllerSoundV3 at h ⊢
  intro w
  simpa only [List.foldl_cons] using h (e :: w)

abbrev AdmittedPostBirthGeometryV3
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  R2Coherence.AdmittedPostBirthGeometry hψ ring (eraseCfgV3 C)

abbrev CoherentPrefixesV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  R2Coherence.CoherentPrefixes ring (eraseCfgV3 C)

def RecoveredV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  AdmittedPostBirthGeometryV3 hψ ring C ∧
    CoherentPrefixesV3 ring C ∧
    ControllerSoundV3 hψ h2 ring C

/-- Exact first-hit mass currency: `Good` means neither recovery nor the higher
layer's allowed exit has yet occurred.  Escaping `Good` within the block is a
first hit of `RecoveredV3 ∨ Exit`. -/
def RecoveryFirstHitMassObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (Exit : FC n ψ κ τ → Prop) (L Q : Nat) : Prop :=
  UniformEscapeMass
    (stepV3 hψ h2 ring)
    (fun C => ¬ RecoveredV3 hψ h2 ring C ∧ ¬ Exit C)
    L Q



/-- Candidate controller potential law: while outside the viability kernel,
no scheduler letter may increase the chosen lexicographic debt. -/
def RecoveryPotentialNoRaiseV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (P : FC n ψ κ τ → Nat) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ¬ ControllerSoundV3 hψ h2 ring C →
      P (stepV3 hψ h2 ring C e) ≤ P C


/-- Outside the viability kernel, at least one scheduler letter strictly
reduces the controller debt. -/
def RecoveryPotentialExistsDecreaseV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (P : FC n ψ κ τ → Nat) : Prop :=
  ∀ C : FC n ψ κ τ,
    ¬ ControllerSoundV3 hψ h2 ring C →
      ∃ e : Fin n, P (stepV3 hψ h2 ring C e) < P C


/-- The exact potential proof interface for the candidate tuple
`(S,O,X,D,M)` described above. -/
def RecoveryPotentialLawsV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (P : FC n ψ κ τ → Nat) : Prop :=
  RecoveryPotentialNoRaiseV3 hψ h2 ring P ∧
    RecoveryPotentialExistsDecreaseV3 hψ h2 ring P




/-- This is the new decisive recovery leaf for route (1).  It is deliberately
parameterized by the higher layer's leader-creation/admitted-exit predicate. -/
def ControllerRecoveryObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (Exit : FC n ψ κ τ → Prop) : Prop :=
  ∃ L Q : Nat, 0 < L ∧ 2 ≤ Q ∧
    RecoveryFirstHitMassObligationV3 hψ h2 ring Exit L Q

/-- Per-branch preservation after recovery. -/
def BranchPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    RecoveredV3 hψ h2 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
    RecoveredV3 hψ h2 ring (stepV3 hψ h2 ring C e)

abbrev SeekPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .seek
abbrev SweepPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .sweep
abbrev CommitPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .commit
abbrev ReleasePreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .release
abbrev ScrubLPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .scrubL
abbrev OpenRPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .openR
abbrev SealedPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .sealed
abbrev OpenHazardPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .openHazard
abbrev OpenNoHazardPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .openNoHazard
abbrev MixedPreservationObligationV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring .mixed

/-- The local main-path dependency really is absent on an open/no-hazard branch. -/
theorem openNoHazard_no_path_change
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
    pairPathChangesV3 l.phys r.phys q.1 q.2 = false := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all [pairHazardV3]

/-- Malformed active SCRUB-L cannot remain a forged completion certificate. -/
theorem scrubL_root_restarts
    (l r : Cell ψ κ τ)
    (hs : successorB l r = true) (hr : atRootB r = true) :
    scrubLStageV3 l r = (l, startClosing r) := by
  simp [scrubLStageV3, hs, hr]

theorem scrubL_bad_edge_restarts
    (l r : Cell ψ κ τ)
    (hs : successorB l r = false) :
    scrubLStageV3 l r = (l, startClosing r) := by
  simp [scrubLStageV3, hs]

theorem openR_bad_edge_restarts
    (l r : Cell ψ κ τ)
    (hs : successorB l r = false) :
    openRStageV3 l r = (startClosing l, r) := by
  simp [openRStageV3, hs]

/-- Hazard services hold both physical endpoints. -/
theorem openStageV3_hazard_physical
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hHaz :
      let q := proposalV3 hψ hw hle l r
      pairHazardV3 l.phys r.phys q.1 q.2 = true) :
    (openStageV3 hψ hw hle l r).1.phys = l.phys ∧
      (openStageV3 hψ hw hle l r).2.phys = r.phys := by
  unfold openStageV3 at *
  dsimp only at hHaz
  rw [if_pos hHaz]
  split <;> simp [startClosing, setControl]

/-- Remaining global semantic work after the local controller algebra above. -/
structure PreservationObligationsV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop where
  seek : SeekPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  sweep : SweepPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  commit : CommitPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  release : ReleasePreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  scrubL : ScrubLPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  openR : OpenRPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  sealed : SealedPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring
  openHazard : OpenHazardPreservationObligationV3
    (κ := κ) (τ := τ) hψ h2 ring
  openNoHazard : OpenNoHazardPreservationObligationV3
    (κ := κ) (τ := τ) hψ h2 ring
  mixed : MixedPreservationObligationV3 (κ := κ) (τ := τ) hψ h2 ring

namespace Regression

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def ring5 : DirectedRing 5 := ⟨by decide⟩
private def ring6 : DirectedRing 6 := ⟨by decide⟩

private def literal (lab : Fin 3)
    (leader : Bool := false)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (bit : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := leader
      shield := leader
      gen_ws := false
      label := lab
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

private def releasingCell (p : R2.Cell 3 3 48) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨.releasing, t⟩⟩

/-! CHECK-ready witness: not excluded by controller shape; it is blocked
by local sanitation/path hazard. -/
private def badReadyInput : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => openCell (literal 0 false .equal (.some 0 0) false)
  | 1 => openCell (literal 1 false .CHECK_ready (.some 0 0) false)
  | _ => openCell (literal 2)

private def badReadyAfter : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 badReadyInput 0

theorem badReady_before_shape_and_coherent :
    ControllerShapeV3 ring3 badReadyInput ∧
      AdmittedPostBirthGeometryV3 h3 ring3 badReadyInput ∧
      CoherentPrefixesV3 ring3 badReadyInput := by
  decide +kernel

theorem badReady_branch_is_hazard :
    branchAtV3 h3 h23 (badReadyInput 0) (badReadyInput 1) = .openHazard := by
  decide +kernel

theorem badReady_after_coherent :
    CoherentPrefixesV3 ring3 badReadyAfter := by
  decide +kernel

/-! OPEN path-erasure witness: also not excluded by controller shape;
`pairPathChangesV3` turns it into a quarantine launch. -/
private def pathEraseInput : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => openCell (literal 0 false .none (.some 0 0))
  | 1 => openCell
      (literal 1 false .eliminate_signal (.some 1 0))
  | _ => openCell (literal 2 false .equal (.some 2 0))

private def pathEraseAfter : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 pathEraseInput 0

theorem pathErase_before_shape_and_coherent :
    ControllerShapeV3 ring3 pathEraseInput ∧
      AdmittedPostBirthGeometryV3 h3 ring3 pathEraseInput ∧
      CoherentPrefixesV3 ring3 pathEraseInput := by
  decide +kernel

theorem pathErase_branch_is_hazard :
    branchAtV3 h3 h23 (pathEraseInput 0) (pathEraseInput 1) = .openHazard := by
  decide +kernel

theorem pathErase_after_coherent :
    CoherentPrefixesV3 ring3 pathEraseAfter := by
  decide +kernel

/-! REOPEN family: a forged scrub phase over uncleared main material is
rejected by `ControllerShapeV3`. -/
private def oldReopenInput : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => openCell (literal 0 false .none (.some 0 0))
  | 1 => releasingCell (literal 1 false .none (.some 1 0)) .scrubL
  | _ => openCell (literal 2 false .equal (.some 2 0))

theorem oldReopen_before_admitted_coherent :
    AdmittedPostBirthGeometryV3 h3 ring3 oldReopenInput ∧
      CoherentPrefixesV3 ring3 oldReopenInput := by
  decide +kernel

theorem oldReopen_not_shape :
    ¬ ControllerShapeV3 ring3 oldReopenInput := by
  decide +kernel

theorem oldReopen_not_sound :
    ¬ ControllerSoundV3 h3 h23 ring3 oldReopenInput := by
  intro h
  exact oldReopen_not_shape
    (controllerSoundV3_shape h3 h23 ring3 oldReopenInput h)

/-! Label-zero leader-boundary witness: `scrubL` at label zero is an
explicit malformed phase and is excluded. -/
private def boundaryInput : FC 4 3 3 48 := fun i =>
  match i.val with
  | 0 => openCell
      (literal 0 false .equal (.some 0 1) false)
  | 1 => releasingCell (literal 0 true) .scrubL
  | 2 => openCell (literal 1)
  | _ => openCell (literal 2)

theorem boundary_before_admitted_coherent :
    AdmittedPostBirthGeometryV3 h3 ring4 boundaryInput ∧
      CoherentPrefixesV3 ring4 boundaryInput := by
  decide +kernel

theorem boundary_not_shape :
    ¬ ControllerShapeV3 ring4 boundaryInput := by
  decide +kernel

theorem boundary_not_sound :
    ¬ ControllerSoundV3 h3 h23 ring4 boundaryInput := by
  intro h
  exact boundary_not_shape
    (controllerSoundV3_shape h3 h23 ring4 boundaryInput h)

/-! Forged OPEN-R completion family.  These are coherent before the
service only because the forged token is a `PrefixDead` witness.  They are
excluded by `ControllerShapeV3`, hence by `ControllerSoundV3`; without that
proof-side first-hit invariant, the actual local V3 completion step still
reproduces the n=3..6 counterexample. -/

private def staleRoot (leader : Bool) : Cell 3 3 48 :=
  openCell (literal 0 leader .equal (.some 0 1) false)

private def finishOwner : Cell 3 3 48 :=
  releasingCell (literal 1) .openR

private def terminal : Cell 3 3 48 :=
  openCell (literal 2)

private def bad3 : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot false
  | 1 => finishOwner
  | _ => terminal

private def bad4 : FC 4 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot true
  | 1 => finishOwner
  | 2 => terminal
  | _ => openCell (literal 0)

private def bad5 : FC 5 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot true
  | 1 => finishOwner
  | 2 => terminal
  | 3 => openCell (literal 0)
  | _ => openCell (literal 1)

private def bad6 : FC 6 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot true
  | 1 => finishOwner
  | 2 => terminal
  | 3 => openCell (literal 0)
  | 4 => openCell (literal 1)
  | _ => openCell (literal 2)

theorem bad3_before :
    AdmittedPostBirthGeometryV3 h3 ring3 bad3 ∧
      CoherentPrefixesV3 ring3 bad3 := by
  decide +kernel

theorem bad3_not_shape : ¬ ControllerShapeV3 ring3 bad3 := by
  decide +kernel

theorem bad3_not_sound : ¬ ControllerSoundV3 h3 h23 ring3 bad3 := by
  intro h
  exact bad3_not_shape (controllerSoundV3_shape h3 h23 ring3 bad3 h)

theorem bad3_after :
    ¬ CoherentPrefixesV3 ring3 (stepV3 h3 h23 ring3 bad3 1) := by
  decide +kernel

theorem bad4_before :
    AdmittedPostBirthGeometryV3 h3 ring4 bad4 ∧
      CoherentPrefixesV3 ring4 bad4 := by
  decide +kernel

theorem bad4_not_shape : ¬ ControllerShapeV3 ring4 bad4 := by
  decide +kernel

theorem bad4_after :
    ¬ CoherentPrefixesV3 ring4 (stepV3 h3 h23 ring4 bad4 1) := by
  decide +kernel

theorem bad5_before :
    AdmittedPostBirthGeometryV3 h3 ring5 bad5 ∧
      CoherentPrefixesV3 ring5 bad5 := by
  decide +kernel

theorem bad5_not_shape : ¬ ControllerShapeV3 ring5 bad5 := by
  decide +kernel

theorem bad5_after :
    ¬ CoherentPrefixesV3 ring5 (stepV3 h3 h23 ring5 bad5 1) := by
  decide +kernel

theorem bad6_before :
    AdmittedPostBirthGeometryV3 h3 ring6 bad6 ∧
      CoherentPrefixesV3 ring6 bad6 := by
  decide +kernel

theorem bad6_not_shape : ¬ ControllerShapeV3 ring6 bad6 := by
  decide +kernel

theorem bad6_after :
    ¬ CoherentPrefixesV3 ring6 (stepV3 h3 h23 ring6 bad6 1) := by
  decide +kernel



/-! The tokenless orphan-passive fixture is no longer fixed. -/


private def orphanSealedCellV3 (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.sealed, .none⟩⟩


private def orphanClosingCellV3 (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.closing, .none⟩⟩


private def orphanPassiveN3 : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => orphanSealedCellV3 (literal 0 false .none (.some 0 0))
  | 1 => orphanClosingCellV3 (literal 1)
  | _ => orphanClosingCellV3 (literal 2)


private def orphanPassiveN3_s1 : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 orphanPassiveN3 0


private def orphanPassiveN3_s2 : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 orphanPassiveN3_s1 0


/-- Edge 0→1 is a valid 0→1 successor edge, so the normalizer launches a
responder seek without changing physical state. -/
theorem orphanPassiveN3_first_launches_seek :
    (orphanPassiveN3_s1 1).ctl = ⟨.closing, .seek⟩ ∧
      (orphanPassiveN3_s1 1).phys = (orphanPassiveN3 1).phys := by
  decide +kernel


/-- Serving the same edge again lets the existing seek rule see the label-zero
initiator and hand control to the ordinary rightward sweep. -/
theorem orphanPassiveN3_second_hands_to_sweep :
    (orphanPassiveN3_s2 0).ctl = ⟨.closing, .sweep⟩ ∧
      (orphanPassiveN3_s2 1).ctl = ⟨.closing, .none⟩ := by
  decide +kernel


/-- The old all-letter fixed-point certificate is destroyed. -/
theorem orphanPassiveN3_not_fixed :
    ∃ e i : Fin 3,
      stepV3 h3 h23 ring3 orphanPassiveN3 e i ≠ orphanPassiveN3 i := by
  refine ⟨0, 1, ?_⟩
  decide +kernel


/-- After the two-letter takeover prefix `[0,0]`, the current shape clauses
have no dirty sealed/release/scrub/openR witness left. -/
theorem orphanPassiveN3_s2_shape :
    ControllerShapeV3 ring3 orphanPassiveN3_s2 := by
  decide +kernel

end Regression


end R2CoherenceV31
