import Leader.Wu.WriteSeq.WriterProducerRepair


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2Coherence


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair


variable {n ψ κ τ width : Nat}


/-- Four physical quarantine marks. -/
inductive Mark where
  | open
  | closing
  | sealed
  | releasing
  deriving DecidableEq, Repr


/-- Six finite control-token values. -/
inductive Token where
  | none
  | seek
  | sweep
  | commit
  | release
  | reopen
  deriving DecidableEq, Repr


/-- Exactly 4 × 6 possible control states. -/
structure Control where
  mark : Mark
  tok : Token
  deriving DecidableEq, Repr


/-- R2 physical state plus the finite quarantine controller. -/
structure Cell (ψ κ τ : Nat) where
  phys : R2.Cell ψ κ τ
  ctl : Control
  deriving DecidableEq


abbrev FC (n ψ κ τ : Nat) := Fin n → Cell ψ κ τ


/-- The bounded raw protocol record seen by CHECK/writer logic. -/
def raw (u : Cell ψ κ τ) : BoundedAgentState ψ κ :=
  u.phys.base.core.core


/-- Install a physical result without touching quarantine control. -/
def install (u : Cell ψ κ τ) (p : R2.Cell ψ κ τ) : Cell ψ κ τ :=
  { u with phys := p }


/-- Replace only the finite quarantine control. -/
def setControl (u : Cell ψ κ τ) (m : Mark) (t : Token) : Cell ψ κ τ :=
  { u with ctl := ⟨m, t⟩ }


/-- Delete the complete main-comparison carrier, retaining writer state. -/
def clearMainPhys (u : R2.Cell ψ κ τ) : R2.Cell ψ κ τ :=
  { u with
    base := ⟨clearComparisonCarrier u.base.core, freshStall τ⟩ }


/-- Controller-level version of `clearMainPhys`. -/
def clearMain (u : Cell ψ κ τ) : Cell ψ κ τ :=
  { u with phys := clearMainPhys u.phys }


@[simp] theorem clearMainPhys_state (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.state = .none := by
  rfl


@[simp] theorem clearMainPhys_path (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.path = .bot := by
  rfl


@[simp] theorem clearMainPhys_path2 (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.path2 = none := by
  rfl


@[simp] theorem clearMainPhys_bit (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.bit = u.base.core.core.bit := by
  rfl


@[simp] theorem clearMainPhys_label (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.label = u.base.core.core.label := by
  rfl


@[simp] theorem clearMainPhys_leader (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.leader = u.base.core.core.leader := by
  rfl


@[simp] theorem clearMainPhys_path3 (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.core.path3 = u.base.core.core.path3 := by
  rfl


@[simp] theorem clearMainPhys_crossed (u : R2.Cell ψ κ τ) :
    (clearMainPhys u).base.core.path0Crossed = false := by
  rfl


/-- Exact ordinary R2 proposal. It is not installed until arbitration ends. -/
def proposal (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : R2.Cell ψ κ τ × R2.Cell ψ κ τ :=
  R2.row hψ hw hle l.phys r.phys


/-- A sealed service cannot feed live main comparison material into R2 and
cannot leave any on the two serviced outputs. -/
def sealedProposal (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : R2.Cell ψ κ τ × R2.Cell ψ κ τ :=
  let q := R2.row hψ hw hle (clearMainPhys l.phys) (clearMainPhys r.phys)
  (clearMainPhys q.1, clearMainPhys q.2)


/-- Resident-ID mutation hazard. -/
def bitChanged (old out : R2.Cell ψ κ τ) : Bool :=
  decide (old.base.core.core.bit ≠ out.base.core.core.bit)


/-- Geometry mutation is quarantined by the same gate. -/
def labelChanged (old out : R2.Cell ψ κ τ) : Bool :=
  decide (old.base.core.core.label ≠ out.base.core.core.label)


/-- Endpoint hazard used for selecting the group to quarantine. -/
def endpointHazard (old out : R2.Cell ψ κ τ) : Bool :=
  bitChanged old out || labelChanged old out


/-- A pair proposal writes at least one resident bit. -/
def pairWrites (l r ql qr : R2.Cell ψ κ τ) : Bool :=
  bitChanged l ql || bitChanged r qr


/-- A pair proposal relabels at least one endpoint. -/
def pairRelabels (l r ql qr : R2.Cell ψ κ τ) : Bool :=
  labelChanged l ql || labelChanged r qr


/-- Conservative open-lane hazard: resident write OR relabel. -/
def pairHazard (l r ql qr : R2.Cell ψ κ τ) : Bool :=
  pairWrites l r ql qr || pairRelabels l r ql qr


/-- Physical label-zero test. -/
def atRootB (u : Cell ψ κ τ) : Bool :=
  decide ((raw u).label.val = 0)


/-- Physical terminal-label test. -/
def atTerminalB (u : Cell ψ κ τ) : Bool :=
  decide ((raw u).label.val + 1 = ψ)


/-- Non-wrap successor test used by the within-group sweep. -/
def successorB (l r : Cell ψ κ τ) : Bool :=
  decide ((raw r).label.val = (raw l).label.val + 1)


/-- Strong release precondition. A release may wait forever; safety does not
rely on eager reopening. -/
def writerQuiet (u : Cell ψ κ τ) : Bool :=
  decide ((raw u).path3 = none ∧
    (raw u).write_state = .none ∧ (raw u).write = .none)


/-- A held hazardous proposal always starts a leftward seek. -/
def startClosing (u : Cell ψ κ τ) : Cell ψ κ τ :=
  setControl u .closing .seek


/-- Move a seek left until the label-zero cell owns a sweep token. -/
def seekStage (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if atRootB r then
    (l, setControl r .closing .sweep)
  else if atRootB l then
    (setControl l .closing .sweep, setControl r .closing .none)
  else
    (setControl l .closing .seek, setControl r .closing .none)


/-- Rightward group sweep. Every visited endpoint loses all main material. -/
def sweepStage (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    let l' := setControl (clearMain l) .closing .none
    let r' := setControl (clearMain r) .closing
      (if atTerminalB r then .commit else .sweep)
    (l', r')
  else
    (l, r)


/-- Leftward commit seals every swept cell. -/
def commitStage (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let r' := setControl (clearMain r) .sealed .none
  if atRootB r then
    (l, r')
  else if atRootB l then
    (setControl (clearMain l) .sealed .none, r')
  else
    (setControl (clearMain l) .closing .commit, r')


/-- Rightward release scan. Visited cells are frozen as `releasing`.
A nonquiet responder aborts by reusing the leftward commit-to-sealed wave. -/
def releaseStage (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    if writerQuiet r then
      let l' := setControl l .releasing .none
      let r' := setControl r .releasing
        (if atTerminalB r then .reopen else .release)
      (l', r')
    else if atRootB l then
      (setControl l .sealed .none, r)
    else
      (setControl l .closing .commit, r)
  else
    (l, r)


/-- Leftward reopen. Main material is cleared once more before each cell opens. -/
def reopenStage (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let r' := setControl (clearMain r) .open .none
  if atRootB r then
    (l, r')
  else if atRootB l then
    (setControl (clearMain l) .open .none, r')
  else
    (setControl (clearMain l) .releasing .reopen, r')


/-- Open lane: harmless R2 proposals install exactly. Hazardous proposals are
held physically and launch a group quarantine at one hazardous endpoint. -/
def openStage (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let q := proposal hψ hw hle l r
  if pairHazard l.phys r.phys q.1 q.2 then
    if endpointHazard r.phys q.2 then
      (l, startClosing r)
    else
      (startClosing l, r)
  else
    (install l q.1, install r q.2)


/-- Sealed lane: bit writes may execute, but main material is suppressed.
R2-internal relabels are conservatively held. A quiet root edge may launch
an optional release scan. -/
def sealedStage (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if atRootB l && successorB l r && writerQuiet l && writerQuiet r then
    (setControl l .releasing .release, r)
  else
    let q := sealedProposal hψ hw hle l r
    if pairRelabels l.phys r.phys q.1 q.2 then
      (l, r)
    else
      (install l q.1, install r q.2)


/-- No valid directional token: execute only a clean open/open or sealed/sealed
pair. Malformed or mixed controls freeze the physical pair. -/
def ordinaryStage (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then
      sealedStage hψ hw hle l r
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      openStage hψ hw hle l r
    else
      (l, r)
  else
    (l, r)


/-- Mechanism-B wrapper row. Token orientation determines the maintenance lane. -/
def row (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if r.ctl.tok = .seek then seekStage l r
  else if l.ctl.tok = .sweep then sweepStage l r
  else if r.ctl.tok = .commit then commitStage l r
  else if l.ctl.tok = .release then releaseStage l r
  else if r.ctl.tok = .reopen then reopenStage l r
  else ordinaryStage hψ hw hle l r


/-- Width-two population protocol on the finite wrapper carrier. -/
def protocol (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := Cell ψ κ τ
  Y := Bool
  transition := row hψ (by decide : 0 < 2) h2
  output := fun u => (raw u).leader


/-- Full-ring wrapper step. -/
def step (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (protocol hψ h2 κ τ).step ring C e


/-! ## Exact agreement on the open, non-hazard lane -/

/-- One cell is exactly in the ordinary open controller state. -/
def OpenControl (u : Cell ψ κ τ) : Prop :=
  u.ctl.mark = .open ∧ u.ctl.tok = .none

/-- All wrapper controls are open and token-free. -/
def AllOpen (C : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, OpenControl (C i)

/-- A proposal is safe to install on the open lane. Because label changes are
also dependencies, `NoWrite` includes both bit silence and label silence. -/
def ProposalNoWrite (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Prop :=
  let q := proposal hψ hw hle l r
  pairWrites l.phys r.phys q.1 q.2 = false ∧
    pairRelabels l.phys r.phys q.1 q.2 = false

/-- The wrapper row is literally the R2 row on physical components when both
controls are open/token-free and the proposal changes neither bits nor labels. -/
theorem row_eq_r2_of_open_no_write
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hlm : l.ctl.mark = .open) (hrm : r.ctl.mark = .open)
    (hlt : l.ctl.tok = .none) (hrt : r.ctl.tok = .none)
    (hsafe : ProposalNoWrite hψ hw hle l r) :
    row hψ hw hle l r =
      (install l (proposal hψ hw hle l r).1,
       install r (proposal hψ hw hle l r).2) := by
  change
    pairWrites l.phys r.phys
        (proposal hψ hw hle l r).1 (proposal hψ hw hle l r).2 = false ∧
      pairRelabels l.phys r.phys
        (proposal hψ hw hle l r).1 (proposal hψ hw hle l r).2 = false at hsafe
  rcases hsafe with ⟨hwrite, hlabel⟩
  simp [row, ordinaryStage, openStage, pairHazard,
    hlm, hrm, hlt, hrt, hwrite, hlabel]

/-- Physical projection of the preceding exact row theorem. -/
theorem row_phys_eq_r2_of_open_no_write
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hlm : l.ctl.mark = .open) (hrm : r.ctl.mark = .open)
    (hlt : l.ctl.tok = .none) (hrt : r.ctl.tok = .none)
    (hsafe : ProposalNoWrite hψ hw hle l r) :
    let q := row hψ hw hle l r
    (q.1.phys, q.2.phys) = R2.row hψ hw hle l.phys r.phys := by
  rw [row_eq_r2_of_open_no_write hψ hw hle l r hlm hrm hlt hrt hsafe]
  rfl

/-- The same lane leaves both finite controller registers unchanged. -/
theorem row_control_eq_of_open_no_write
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hlm : l.ctl.mark = .open) (hrm : r.ctl.mark = .open)
    (hlt : l.ctl.tok = .none) (hrt : r.ctl.tok = .none)
    (hsafe : ProposalNoWrite hψ hw hle l r) :
    let q := row hψ hw hle l r
    q.1.ctl = l.ctl ∧ q.2.ctl = r.ctl := by
  rw [row_eq_r2_of_open_no_write hψ hw hle l r hlm hrm hlt hrt hsafe]
  exact ⟨rfl, rfl⟩

/-- Forget quarantine control. -/
def project (C : FC n ψ κ τ) : R2.FC n ψ κ τ :=
  fun i => (C i).phys

/-- Forget both quarantine control and producer fuel. -/
def baseProject (C : FC n ψ κ τ) :
    BirthCheckPermitRepairLeaf.FC n ψ κ τ :=
  fun i => (C i).phys.base

/-- Pair-update form of `PopulationProtocol.step`, useful for exact projection
without unfolding either large physical row. -/
private def pairStep {X : Type} (T : X → X → X × X)
    (ring : DirectedRing n) (C : Fin n → X) (e : Fin n) : Fin n → X :=
  let j := ring.rightNeighbor e
  let q := T (C e) (C j)
  fun k => if k = e then q.1 else if k = j then q.2 else C k

private theorem pairStep_project {X Y : Type}
    (f : X → Y) (T : X → X → X × X) (U : Y → Y → Y × Y)
    (ring : DirectedRing n) (C : Fin n → X) (e : Fin n)
    (hpair :
      let p := T (C e) (C (ring.rightNeighbor e))
      let q := U (f (C e)) (f (C (ring.rightNeighbor e)))
      f p.1 = q.1 ∧ f p.2 = q.2) :
    (fun k => f (pairStep T ring C e k)) =
      pairStep U ring (fun k => f (C k)) e := by
  dsimp only at hpair
  rcases hpair with ⟨hL, hR⟩
  funext k
  by_cases hke : k = e
  · subst k
    simp [pairStep, hL]
  · by_cases hkr : k = ring.rightNeighbor e
    · subst k
      simp [pairStep, hke, hR]
    · simp [pairStep, hke, hkr]


private theorem step_eq_pairStep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    step hψ h2 ring C e =
      pairStep (row hψ (by decide : 0 < 2) h2) ring C e := by
  rfl

private theorem r2_step_eq_pairStep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2.FC n ψ κ τ) (e : Fin n) :
    R2.step hψ h2 ring C e =
      pairStep (R2.row hψ (by decide : 0 < 2) h2) ring C e := by
  rfl

/-- One scheduled edge is open/no-hazard exactly when its local proposal is. -/
def NoHazardAt (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : Prop :=
  ProposalNoWrite hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))

theorem project_step_of_open_no_write
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hOpen : AllOpen C) (hNo : NoHazardAt hψ h2 ring C e) :
    project (step hψ h2 ring C e) =
      R2.step hψ h2 ring (project C) e := by
  have hl := hOpen e
  have hr := hOpen (ring.rightNeighbor e)
  rcases hl with ⟨hlm, hlt⟩
  rcases hr with ⟨hrm, hrt⟩
  have hpairs := row_phys_eq_r2_of_open_no_write
    hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e)) hlm hrm hlt hrt hNo
  have hpair :
      let p := row hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))
      let q := R2.row hψ (by decide : 0 < 2) h2
        (project C e) (project C (ring.rightNeighbor e))
      p.1.phys = q.1 ∧ p.2.phys = q.2 := by
    constructor
    · exact congrArg Prod.fst hpairs
    · exact congrArg Prod.snd hpairs
  rw [step_eq_pairStep hψ h2 ring C e,
    r2_step_eq_pairStep hψ h2 ring (project C) e]
  change
    (fun k =>
      (pairStep (row hψ (by decide : 0 < 2) h2) ring C e k).phys) =
      pairStep (R2.row hψ (by decide : 0 < 2) h2)
        ring (project C) e
  exact pairStep_project (fun u : Cell ψ κ τ => u.phys)
    (row hψ (by decide : 0 < 2) h2)
    (R2.row hψ (by decide : 0 < 2) h2) ring C e hpair


/-- Every prefix configuration of the requested word remains open, and the
requested proposal at each letter is bit/label silent. -/
def OpenNoWriteAlong
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    FC n ψ κ τ → List (Fin n) → Prop
  | C, [] => AllOpen C
  | C, e :: w =>
      AllOpen C ∧ NoHazardAt hψ h2 ring C e ∧
        OpenNoWriteAlong hψ h2 ring (step hψ h2 ring C e) w

/-- Word projection used to reuse original-word R2 receipts. -/
theorem project_word_of_open_no_write
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (w : List (Fin n)) :
    ∀ C : FC n ψ κ τ,
      OpenNoWriteAlong hψ h2 ring C w →
      project (w.foldl (step hψ h2 ring) C) =
        w.foldl (R2.step hψ h2 ring) (project C) := by
  induction w with
  | nil =>
      intro C _
      rfl
  | cons e w ih =>
      intro C h
      rcases h with ⟨hOpen, hNo, htail⟩
      simp only [List.foldl_cons]
      calc
        project (w.foldl (step hψ h2 ring) (step hψ h2 ring C e)) =
            w.foldl (R2.step hψ h2 ring)
              (project (step hψ h2 ring C e)) :=
          ih (step hψ h2 ring C e) htail
        _ = w.foldl (R2.step hψ h2 ring)
              (R2.step hψ h2 ring (project C) e) := by
          rw [project_step_of_open_no_write hψ h2 ring C e hOpen hNo]

/-- The currently unexported R2→R1 leaderless/no-producer agreement is named
as a physical obligation rather than postulated as an axiom. -/
def R2R1AgreementObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (D : R2.FC n ψ κ τ) (e : Fin n),
    R2.Leaderless D → R2.NoProducer D →
    (fun i => (R2.step hψ h2 ring D e i).base) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring
        (fun i => (D i).base) e

theorem leaderless_agreement
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hR2 : R2R1AgreementObligation (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hOpen : AllOpen C) (hNo : NoHazardAt hψ h2 ring C e)
    (hLead : R2.Leaderless (project C))
    (hProd : R2.NoProducer (project C)) :
    baseProject (step hψ h2 ring C e) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring (baseProject C) e := by
  have hp := project_step_of_open_no_write hψ h2 ring C e hOpen hNo
  change (fun i => (project (step hψ h2 ring C e) i).base) = _
  rw [hp]
  change
    (fun i => (R2.step hψ h2 ring (project C) e i).base) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring
        (fun i => (project C i).base) e
  exact hR2 (project C) e hLead hProd


/-! ## Decidable current-state coherence -/

/-- Cyclic predecessor by `d` physical cells. -/
def back (ring : DirectedRing n) (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + n - (d % n)) % n, Nat.mod_lt _ ring.hn⟩

/-- Cyclic successor by `d` physical cells. -/
def fwd (ring : DirectedRing n) (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ ring.hn⟩

/-- Current label-zero position of the group containing `i`, assuming the
admitted post-birth label geometry. -/
def groupStart (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) : Fin n :=
  back ring i (raw (C i)).label.val

/-- Current k-th physical position of `i`'s group. -/
def groupPos (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) (k : Nat) : Fin n :=
  fwd ring (groupStart ring C i) k

/-- A live equality is logically dead as soon as any finite quarantine mark or
token exists in its current group. This is needed while a sweep is in flight:
the remote frontier need not have been physically cleared yet. -/
def PrefixDead (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) : Prop :=
  ∃ k : Fin ψ,
    let u := C (groupPos ring C i k.val)
    u.ctl.mark ≠ .open ∨ u.ctl.tok ≠ .none

instance prefixDeadDecidable (ring : DirectedRing n)
    (C : FC n ψ κ τ) (i : Fin n) : Decidable (PrefixDead ring C i) := by
  unfold PrefixDead
  infer_instance

/-- Physical position of label `k` in the prefix ending at frontier `i`. -/
def prefixPos (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) (k : Nat) : Fin n :=
  back ring i ((raw (C i)).label.val - k)

/-- One already-read main component still matches the current resident bit. -/
def freshComponent (u : Cell ψ κ τ) (k : Nat) : Prop :=
  (raw u).label.val = k ∧
    match (raw u).path with
    | .bot => False
    | .some lab b =>
        lab.val = k ∧ b.val = (if (raw u).bit then 1 else 0)

instance freshComponentDecidable (u : Cell ψ κ τ) (k : Nat) :
    Decidable (freshComponent u k) := by
  unfold freshComponent
  cases h : (raw u).path with
  | bot =>
      simp only [h]
      infer_instance
  | some lab b =>
      simp only [h]
      infer_instance


/-- Every stored equal frontier is either killed by an active group quarantine,
or every already-read component 0..frontier is fresh against current bits. -/
def FreshEqualPrefix (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) : Prop :=
  (raw (C i)).state = .equal →
    PrefixDead ring C i ∨
      ∀ k : Fin ((raw (C i)).label.val + 1),
        freshComponent (C (prefixPos ring C i k.val)) k.val

instance freshEqualPrefixDecidable (ring : DirectedRing n)
    (C : FC n ψ κ τ) (i : Fin n) : Decidable (FreshEqualPrefix ring C i) := by
  unfold FreshEqualPrefix
  infer_instance

/-- Decidable, history-free CHECK/ID coherence predicate. -/
def CoherentPrefixes (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, FreshEqualPrefix ring C i

instance coherentPrefixesDecidable (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Decidable (CoherentPrefixes ring C) := by
  unfold CoherentPrefixes
  infer_instance

/-- A quarantined group makes its current equal frontier dead immediately. -/
theorem freshEqualPrefix_of_dead
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hdead : PrefixDead ring C i) : FreshEqualPrefix ring C i := by
  intro _
  exact Or.inl hdead

/-- A cell that is not an equal frontier imposes no freshness obligation. -/
theorem freshEqualPrefix_of_not_equal
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hne : (raw (C i)).state ≠ .equal) : FreshEqualPrefix ring C i := by
  intro heq
  exact (hne heq).elim

/-- Clearing one wrapper cell destroys equality at that cell. -/
theorem clearMain_not_equal (u : Cell ψ κ τ) :
    (raw (clearMain u)).state ≠ .equal := by
  change (clearMainPhys u.phys).base.core.core.state ≠ .equal
  rw [clearMainPhys_state]
  decide

/-- If no physical cell stores equality, coherence is immediate. -/
theorem coherentPrefixes_of_no_equal
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ∀ i : Fin n, (raw (C i)).state ≠ .equal) :
    CoherentPrefixes ring C := by
  intro i
  exact freshEqualPrefix_of_not_equal ring C i (h i)

/-! ## Admitted post-birth geometry and exact remaining leaves -/

/-- Minimal geometry used by this coherence layer: every leader is label zero,
and every edge entering a follower has the current successor label. Higher B9
and ruler invariants may strengthen this predicate. -/
def AdmittedPostBirthGeometry
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (raw (C i)).leader = true →
      (raw (C i)).label = ⟨0, hψ⟩) ∧
  (∀ i : Fin n,
      let j := ring.rightNeighbor i
      (raw (C j)).leader = true ∨
        (raw (C j)).label =
          ⟨((raw (C i)).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)

instance admittedPostBirthGeometryDecidable
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (AdmittedPostBirthGeometry hψ ring C) := by
  unfold AdmittedPostBirthGeometry
  infer_instance

/-- The nine executable row classes. -/
inductive Branch where
  | seek
  | sweep
  | commit
  | release
  | reopen
  | sealed
  | openHazard
  | openNoHazard
  | mixed
  deriving DecidableEq, Repr

/-- Current branch selected at scheduler edge `e`; this mirrors `row` priority. -/
def branchAt
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
      let q := proposal hψ (by decide : 0 < 2) h2 l r
      if pairHazard l.phys r.phys q.1 q.2 then .openHazard
      else .openNoHazard
    else .mixed
  else .mixed

/-- One exact branch's remaining global coherence leaf. These are Props, not
axioms: callers must construct proofs from R2 frames + admitted geometry. -/
def BranchPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : Branch) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    AdmittedPostBirthGeometry hψ ring C →
    CoherentPrefixes ring C →
    branchAt hψ h2 ring C e = b →
    CoherentPrefixes ring (step hψ h2 ring C e)

def SeekPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .seek

def SweepPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .sweep

def CommitPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .commit

def ReleasePreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .release

def ReopenPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .reopen

def SealedPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .sealed

def OpenHazardPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .openHazard

def OpenNoHazardPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .openNoHazard

def MixedPreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring .mixed

/-- Named bundle of the remaining physical/global leaves. -/
structure PreservationObligations
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop where
  seek : SeekPreservationObligation (κ := κ) (τ := τ) hψ h2 ring
  sweep : SweepPreservationObligation (κ := κ) (τ := τ) hψ h2 ring
  commit : CommitPreservationObligation (κ := κ) (τ := τ) hψ h2 ring
  release : ReleasePreservationObligation (κ := κ) (τ := τ) hψ h2 ring
  reopen : ReopenPreservationObligation (κ := κ) (τ := τ) hψ h2 ring
  sealed : SealedPreservationObligation (κ := κ) (τ := τ) hψ h2 ring
  openHazard : OpenHazardPreservationObligation
    (κ := κ) (τ := τ) hψ h2 ring
  openNoHazard : OpenNoHazardPreservationObligation
    (κ := κ) (τ := τ) hψ h2 ring
  mixed : MixedPreservationObligation (κ := κ) (τ := τ) hψ h2 ring

/-- One-row preservation theorem. The wrapper-specific dispatcher is proved;
the branchwise R2/geometry leaves are the named Props above. -/
theorem coherentPrefixes_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hO : PreservationObligations (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ)
    (hGeom : AdmittedPostBirthGeometry hψ ring C)
    (hC : CoherentPrefixes ring C) (e : Fin n) :
    CoherentPrefixes ring (step hψ h2 ring C e) := by
  cases hb : branchAt hψ h2 ring C e with
  | seek => exact hO.seek C e hGeom hC hb
  | sweep => exact hO.sweep C e hGeom hC hb
  | commit => exact hO.commit C e hGeom hC hb
  | release => exact hO.release C e hGeom hC hb
  | reopen => exact hO.reopen C e hGeom hC hb
  | sealed => exact hO.sealed C e hGeom hC hb
  | openHazard => exact hO.openHazard C e hGeom hC hb
  | openNoHazard => exact hO.openNoHazard C e hGeom hC hb
  | mixed => exact hO.mixed C e hGeom hC hb

/-! ## Closed ψ=3 regression fixtures -/

namespace Regression

private abbrev PCfg := R2.FC 3 3 3 48
private abbrev WCfg := FC 3 3 3 48

private def ring3 : DirectedRing 3 := ⟨by decide⟩

private def r2step : PCfg → Fin 3 → PCfg :=
  R2.step (by decide : 0 < 3) (by decide : 2 ≤ 3) ring3

private def wstep : WCfg → Fin 3 → WCfg :=
  step (by decide : 0 < 3) (by decide : 2 ≤ 3) ring3

/-- Literal bounded cell template. `clean` is used only as a constructor for
all unmentioned finite fields; no transition is called here. -/
private def literal (i : Fin 3)
    (bit : Bool := false)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (writeState : WriteState := .none)
    (p3 : Option (BoundedPath3Info 3) := none)
    (bCarry : Bool := false)
    (fuel : WriterProducerRepair.Credit 3 := 0) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean
    (by decide : 0 < 3) (fun _ => false) i
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      bit := bit
      state := state
      path := path
      path3 := p3
      write_state := writeState
      write := .none
      b_carry := bCarry }
  ⟨⟨⟨b', false⟩, 48⟩, fuel⟩

private def p3zero (i : Fin 3) : Option (BoundedPath3Info 3) :=
  some { label := i, bit := 0, flag := 1 }

/-- Source cut: all-zero aligned main train; label 0 is a forged
producer and label 1 is a forged done acknowledgement carrying true carry. -/
private def q13252WriteInput : PCfg := fun i =>
  match i.val with
  | 0 => literal 0
      (path := .some 0 0) (writeState := .produce) (fuel := 12)
  | 1 => literal 1
      (path := .some 1 0) (writeState := .done)
      (p3 := p3zero 1) (bCarry := true) (fuel := 12)
  | _ => literal 2 (path := .some 2 0)

/-- Literal stale cut immediately before the terminal CHECK: the old payload
still says 000, but label-zero resident bit is now one and the frontier at
label one remains equal. -/
private def q13252TerminalInput : PCfg := fun i =>
  match i.val with
  | 0 => literal 0 true .equal (.some 0 0)
  | 1 => literal 1 false .equal (.some 1 0)
  | _ => literal 2 false .none (.some 2 0)

/-- Closed one-service R2 check: the forged acknowledgement changes bit zero
and leaves the main equal frontier live. -/
theorem q13300_r2_write_retains_equal :
    let D := r2step q13252WriteInput 0
    (D 0).base.core.core.bit = true ∧
      (D 1).base.core.core.state = .equal ∧
      (D 1).base.core.core.leader = false := by
  decide +kernel

/-- Closed one-service R2 check at the stale terminal cut: CHECK creates the
terminal leader without re-reading the changed label-zero resident bit. -/
theorem q13300_r2_terminal_birth :
    let D := r2step q13252TerminalInput 1
    (D 2).base.core.core.leader = true := by
  decide +kernel

private def openWrap (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.open, .none⟩⟩

private def q13252Open : WCfg := fun i => openWrap (q13252WriteInput i)

/-- Exact wrapper output of the hazardous writer letter: no physical
R2 output is installed; label zero owns the leftward seek. -/
private def q13252Held : WCfg := fun i =>
  match i.val with
  | 0 => ⟨q13252WriteInput 0, ⟨.closing, .seek⟩⟩
  | 1 => openWrap (q13252WriteInput 1)
  | _ => openWrap (q13252WriteInput 2)

/-- Closed one-service wrapper check: the proposed resident write is held and
a seek is launched. -/
theorem q13300_wrapper_holds_write_launches_seek :
    ∀ i : Fin 3, wstep q13252Open 0 i = q13252Held i := by
  decide +kernel

/-- The next edge cannot create a leader because the hazardous first
proposal was never installed. This is another closed single-service check,
starting from the literal held state above. -/
theorem q13300_wrapper_next_service_no_leader :
    let D := wstep q13252Held 1
    ∀ i : Fin 3, (raw (D i)).leader = false := by
  decide +kernel

/-- Composition uses only the two preceding single-service certificates. -/
theorem q13300_wrapper_attack_word_no_leader :
    let D := wstep (wstep q13252Open 0) 1
    ∀ i : Fin 3, (raw (D i)).leader = false := by
  have h1 : wstep q13252Open 0 = q13252Held :=
    funext q13300_wrapper_holds_write_launches_seek
  change ∀ i : Fin 3,
    (raw (wstep (wstep q13252Open 0) 1 i)).leader = false
  rw [h1]
  exact q13300_wrapper_next_service_no_leader

/-! ### Remote-frontier sweep regression -/

/-- A whole three-cell group carrying a live all-zero equal prefix. -/
private def sweepPhys : PCfg := fun i =>
  match i.val with
  | 0 => literal 0 false .equal (.some 0 0)
  | 1 => literal 1 false .equal (.some 1 0)
  | _ => literal 2 false .equal (.some 2 0)

/-- Sweep starts at label zero while the remote terminal frontier is untouched. -/
private def sweepStart : WCfg := fun i =>
  match i.val with
  | 0 => ⟨sweepPhys 0, ⟨.closing, .sweep⟩⟩
  | 1 => openWrap (sweepPhys 1)
  | _ => openWrap (sweepPhys 2)

/-- Literal state after the first sweep service 0→1. -/
private def sweepMid : WCfg := fun i =>
  match i.val with
  | 0 => ⟨clearMainPhys (sweepPhys 0), ⟨.closing, .none⟩⟩
  | 1 => ⟨clearMainPhys (sweepPhys 1), ⟨.closing, .sweep⟩⟩
  | _ => openWrap (sweepPhys 2)

/-- Literal state after the second sweep service 1→2, before commit moves left. -/
private def sweepCommit : WCfg := fun i =>
  match i.val with
  | 0 => ⟨clearMainPhys (sweepPhys 0), ⟨.closing, .none⟩⟩
  | 1 => ⟨clearMainPhys (sweepPhys 1), ⟨.closing, .none⟩⟩
  | _ => ⟨clearMainPhys (sweepPhys 2), ⟨.closing, .commit⟩⟩

/-- Closed single-service check for the first half of the sweep. -/
theorem q13300_sweep_first_service :
    ∀ i : Fin 3, wstep sweepStart 0 i = sweepMid i := by
  decide +kernel

/-- Closed single-service check: the second sweep letter reaches the terminal,
clears its remote equal frontier, and only then emits `commit`. -/
theorem q13300_sweep_terminal_service :
    ∀ i : Fin 3, wstep sweepMid 1 i = sweepCommit i := by
  decide +kernel

/-- The remote frontier is physically dead before the commit wave begins. -/
theorem q13300_sweep_remote_equal_cleared_before_commit :
    (raw (sweepCommit 2)).state = .none ∧
      (raw (sweepCommit 2)).path = .bot ∧
      (sweepCommit 2).ctl.tok = .commit := by
  decide +kernel

end Regression
end R2Coherence
