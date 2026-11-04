import Leader.Wu.Carrier.RoleThreePostRoute

/-!
# Total role-three postcommit control row

This is the literal radius-one row for the post-grid publication sector.  It
frames `pos` by type.  A valid role-three post head rolls `active := staging`
while following `PPLLRole3PostRoute`; duplicate heads are both consumed.
Exact role-three LIN tags are accepted only on a root-to-slot-one edge and use
the existing atomic fixed-bank copy.  Every other unreserved tag is erased to
a canonical literal QMAT root/cell while preserving the active payload.

When neither endpoint has tag debt, the row is exactly the full 65-mode QMAT
row.  This module proves only a total post/scrub row and a large aligned-tag
handoff envelope.  It does not prove arbitrary-soup convergence to
`ProgramFlight`, nor that forged post heads are disjoint from live literal
transactions.  Production of a source-faithful staged LIN state and that
global legitimacy argument remain separate compiler obligations.
-/

namespace PPLLRole3PostRow

open PPLLFixedActiveStaging
open PPLLLinearCarrierPacking
open PPLLParallelGeometryLift
open PPLLParallelGeometryPacked
open PPLLV2LiteralTable
open PPLLV2ValidatorPhysicalRefinement
open PPLLRole3PostRoute

set_option autoImplicit false
set_option warningAsError true

inductive LinCase where
  | source
  | target
  | none
  deriving DecidableEq, Repr

def linControl : LinCase → PPLLPairedFivePassCarrier.RootCtl32
  | .source => linSourcePhase
  | .target => linTargetPhase
  | .none => linNonePhase

def linSite : LinCase → Option BlockSide
  | .source => some .source
  | .target => some .target
  | .none => none

def encodeLin (base : PackedControl) (lin : LinCase) : PackedControl :=
  { base with
    role := stagingRole
    rootCtl := linControl lin
    message := 0
    trail := preLease }

def decodeLin (control : PackedControl) : Option LinCase :=
  if control.role = stagingRole ∧ control.trail = preLease ∧
      control.message.val = 0 then
    if control.rootCtl = linSourcePhase then some .source
    else if control.rootCtl = linTargetPhase then some .target
    else if control.rootCtl = linNonePhase then some .none
    else none
  else none

@[simp] theorem decodeLin_encodeLin (base : PackedControl) (lin : LinCase) :
    decodeLin (encodeLin base lin) = some lin := by
  cases lin <;>
    simp [decodeLin, encodeLin, linControl, linSourcePhase,
      linTargetPhase, linNonePhase, preLease, stagingRole]

def canonicalLiteralMode {h : Nat} (pos : Fin h) : PackedLiteralMode :=
  if pos.val = 0 then .root (.wash false false)
  else .cell (headless .empty)

@[simp] theorem decodeLiteralTag_writeLiteral (base : PackedControl)
    (mode : PackedLiteralMode) :
    decodeLiteralTag (writeLiteral base mode).role
        (writeLiteral base mode).rootCtl = some mode := by
  exact decodeLiteralTag_literalTag mode

theorem literalTag_role_ne_stagingRole (mode : PackedLiteralMode) :
    (literalTag mode).1 ≠ stagingRole := by
  intro heq
  have hdecode := decodeLiteralTag_literalTag mode
  rw [heq, decodeLiteralTag_role_three] at hdecode
  contradiction

@[simp] theorem writeLiteral_role (base : PackedControl)
    (mode : PackedLiteralMode) :
    (writeLiteral base mode).role = (literalTag mode).1 := rfl

@[simp] theorem writeLiteral_rootCtl (base : PackedControl)
    (mode : PackedLiteralMode) :
    (writeLiteral base mode).rootCtl = (literalTag mode).2 := rfl

/-- Erase control debt without publishing an untrusted staging bit. -/
def eraseToLiteral {h : Nat} (pos : Fin h) (base : PackedControl) :
    PackedControl :=
  { writeLiteral base (canonicalLiteralMode pos) with
    stagingBit := base.activeBit
    message := 0
    trail := 0 }

/-- Adopt a post state by publishing its current staging bit exactly once. -/
def rollToLiteral {h : Nat} (pos : Fin h) (base : PackedControl) :
    PackedControl :=
  { writeLiteral base (canonicalLiteralMode pos) with
    activeBit := base.stagingBit
    message := 0
    trail := 0 }

@[simp] theorem eraseToLiteral_activeBit {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    (eraseToLiteral pos base).activeBit = base.activeBit := rfl

@[simp] theorem eraseToLiteral_banks {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    (eraseToLiteral pos base).stagingBit = base.activeBit := rfl

@[simp] theorem rollToLiteral_banks {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    (rollToLiteral pos base).activeBit = base.stagingBit ∧
      (rollToLiteral pos base).stagingBit = base.stagingBit := by
  exact ⟨rfl, rfl⟩

@[simp] theorem decodeLiteralTag_eraseToLiteral {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    decodeLiteralTag (eraseToLiteral pos base).role
        (eraseToLiteral pos base).rootCtl =
      some (canonicalLiteralMode pos) := by
  simp [eraseToLiteral]

@[simp] theorem decodeLiteralTag_rollToLiteral {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    decodeLiteralTag (rollToLiteral pos base).role
        (rollToLiteral pos base).rootCtl =
      some (canonicalLiteralMode pos) := by
  simp [rollToLiteral]

inductive SanClass where
  | literal (mode : PackedLiteralMode)
  | lin (lin : LinCase)
  | post (route : PostRoute)
  | junk
  deriving DecidableEq, Repr

def ModeFitsPosition {h : Nat} (pos : Fin h) : PackedLiteralMode → Prop
  | .root _ => pos.val = 0
  | .cell _ => pos.val ≠ 0

instance modeFitsPositionDecidable {h : Nat} (pos : Fin h)
    (mode : PackedLiteralMode) : Decidable (ModeFitsPosition pos mode) := by
  cases mode <;> unfold ModeFitsPosition <;> infer_instance

/-- A decodable tag at the wrong block position is sanitation debt, not a
literal program state. -/
def classifyAt {h : Nat} (pos : Fin h) (control : PackedControl) : SanClass :=
  match decodePostRoute control with
  | some route => .post route
  | none =>
      match decodeLin control with
      | some lin => .lin lin
      | none =>
          match decodeLiteralTag control.role control.rootCtl with
          | some mode =>
              if ModeFitsPosition pos mode then .literal mode else .junk
          | none => .junk

@[simp] theorem classifyAt_encodePostRoute {h : Nat} (pos : Fin h)
    (base : PackedControl) (route : PostRoute) :
    classifyAt pos (encodePostRoute base route) = .post route := by
  simp [classifyAt]

@[simp] theorem classifyAt_encodeLin {h : Nat} (pos : Fin h)
    (base : PackedControl) (lin : LinCase) :
    classifyAt pos (encodeLin base lin) = .lin lin := by
  have hpost : decodePostRoute (encodeLin base lin) = none := by
    cases lin <;>
      simp [decodePostRoute, encodeLin, linControl, preLease, postLease,
        stagingRole]
  simp [classifyAt, hpost]

theorem decodePostRoute_eq_none_of_decodeLiteralTag_eq_some
    (control : PackedControl) (mode : PackedLiteralMode)
    (hdecode : decodeLiteralTag control.role control.rootCtl = some mode) :
    decodePostRoute control = none := by
  have hrole : control.role ≠ stagingRole := by
    intro heq
    rw [heq, decodeLiteralTag_role_three] at hdecode
    contradiction
  simp [decodePostRoute, hrole]

theorem decodeLin_eq_none_of_decodeLiteralTag_eq_some
    (control : PackedControl) (mode : PackedLiteralMode)
    (hdecode : decodeLiteralTag control.role control.rootCtl = some mode) :
    decodeLin control = none := by
  have hrole : control.role ≠ stagingRole := by
    intro heq
    rw [heq, decodeLiteralTag_role_three] at hdecode
    contradiction
  simp [decodeLin, hrole]

theorem classifyAt_eq_literal_of_decodeLiteralTag_eq_some {h : Nat}
    (pos : Fin h) (control : PackedControl) (mode : PackedLiteralMode)
    (hdecode : decodeLiteralTag control.role control.rootCtl = some mode)
    (hfit : ModeFitsPosition pos mode) :
    classifyAt pos control = .literal mode := by
  rw [classifyAt,
    decodePostRoute_eq_none_of_decodeLiteralTag_eq_some control mode hdecode,
    decodeLin_eq_none_of_decodeLiteralTag_eq_some control mode hdecode]
  simp [hdecode, hfit]

theorem canonicalLiteralMode_fits {h : Nat} (pos : Fin h) :
    ModeFitsPosition pos (canonicalLiteralMode pos) := by
  by_cases hzero : pos.val = 0
  · simp [canonicalLiteralMode, ModeFitsPosition, hzero]
  · simp [canonicalLiteralMode, ModeFitsPosition, hzero]

@[simp] theorem classify_eraseToLiteral {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    classifyAt pos (eraseToLiteral pos base) =
      .literal (canonicalLiteralMode pos) := by
  exact classifyAt_eq_literal_of_decodeLiteralTag_eq_some pos _ _
    (decodeLiteralTag_eraseToLiteral pos base) (canonicalLiteralMode_fits pos)

@[simp] theorem classify_rollToLiteral {h : Nat} (pos : Fin h)
    (base : PackedControl) :
    classifyAt pos (rollToLiteral pos base) =
      .literal (canonicalLiteralMode pos) := by
  exact classifyAt_eq_literal_of_decodeLiteralTag_eq_some pos _ _
    (decodeLiteralTag_rollToLiteral pos base) (canonicalLiteralMode_fits pos)

def eraseUnlessLiteral {h : Nat} (pos : Fin h) (base : PackedControl) :
    PackedControl :=
  match classifyAt pos base with
  | .literal _ => base
  | _ => eraseToLiteral pos base

/-- Service a route head currently on the initiator endpoint. -/
def servicePostLeft {h : Nat} (hh : 0 < h)
    (left right : ParallelCell h PackedControl) (route : PostRoute) :
    PackedControl × PackedControl :=
  if routeDirection route = .right then
    match routeService hh (route, left.1) with
    | none => (rollToLiteral left.1 left.2, rollToLiteral right.1 right.2)
    | some (nextRoute, nextPos) =>
        if nextPos = right.1 then
          (rollToLiteral left.1 left.2,
            encodePostRoute (rollToLiteral right.1 right.2) nextRoute)
        else if nextPos = left.1 then
          (encodePostRoute (rollToLiteral left.1 left.2) nextRoute, right.2)
        else
          (encodePostRoute left.2 route,
            eraseUnlessLiteral right.1 right.2)
  else
    (encodePostRoute left.2 route, eraseUnlessLiteral right.1 right.2)

/-- Service a route head currently on the responder endpoint. -/
def servicePostRight {h : Nat} (hh : 0 < h)
    (left right : ParallelCell h PackedControl) (route : PostRoute) :
    PackedControl × PackedControl :=
  if routeDirection route = .left then
    match routeService hh (route, right.1) with
    | none => (left.2, rollToLiteral right.1 right.2)
    | some (nextRoute, nextPos) =>
        if nextPos = left.1 then
          (encodePostRoute (rollToLiteral left.1 left.2) nextRoute,
            rollToLiteral right.1 right.2)
        else if nextPos = right.1 then
          (left.2, encodePostRoute (rollToLiteral right.1 right.2) nextRoute)
        else
          (eraseUnlessLiteral left.1 left.2,
            encodePostRoute right.2 route)
  else
    (eraseUnlessLiteral left.1 left.2, encodePostRoute right.2 route)

def installLinearizedLeft {h : Nat}
    (left right : ParallelCell h PackedControl) (lin : LinCase) :
    PackedControl × PackedControl :=
  let rolledLeft := { left.2 with activeBit := left.2.stagingBit }
  (encodePostRoute rolledLeft (initialRoute (linSite lin)),
    rollToLiteral right.1 right.2)

/-- Total pair row.  Post dominates LIN, LIN dominates sanitation, and only a
debt-free literal/literal pair delegates to the exact QMAT table. -/
def role3PostControlRow (h : Nat) (hh : 0 < h) : PackedControlRow h :=
  fun left right =>
    match classifyAt left.1 left.2, classifyAt right.1 right.2 with
    | .post _, .post _ =>
        (rollToLiteral left.1 left.2, rollToLiteral right.1 right.2)
    | .post route, _ => servicePostLeft hh left right route
    | _, .post route => servicePostRight hh left right route
    | .lin lin, _ =>
        if left.1.val = 0 ∧ right.1.val = 1 then
          installLinearizedLeft left right lin
        else
          (eraseToLiteral left.1 left.2,
            eraseUnlessLiteral right.1 right.2)
    | _, .lin _ =>
        (eraseUnlessLiteral left.1 left.2, right.2)
    | .literal leftMode, .literal rightMode =>
        let out := packedLiteralModeStep leftMode rightMode
        (writeLiteral left.2 out.1, writeLiteral right.2 out.2)
    | .junk, _ =>
        (eraseToLiteral left.1 left.2,
          eraseUnlessLiteral right.1 right.2)
    | _, .junk =>
        (eraseUnlessLiteral left.1 left.2,
          eraseToLiteral right.1 right.2)

def AlignedLiteralControl {h : Nat} (pos : Fin h)
    (control : PackedControl) : Prop :=
  ∃ mode, decodeLiteralTag control.role control.rootCtl = some mode ∧
    ModeFitsPosition pos mode

def AllAlignedLiteral {n h : Nat}
    (q : Fin n → ParallelCell h PackedControl) : Prop :=
  ∀ i, AlignedLiteralControl (q i).1 (q i).2

theorem modeFitsPosition_step_left {h : Nat} (pos : Fin h)
    (leftMode rightMode : PackedLiteralMode)
    (hfit : ModeFitsPosition pos leftMode) :
    ModeFitsPosition pos (packedLiteralModeStep leftMode rightMode).1 := by
  cases leftMode <;> cases rightMode <;>
    simpa [packedLiteralModeStep, ModeFitsPosition] using hfit

theorem modeFitsPosition_step_right {h : Nat} (pos : Fin h)
    (leftMode rightMode : PackedLiteralMode)
    (hfit : ModeFitsPosition pos rightMode) :
    ModeFitsPosition pos (packedLiteralModeStep leftMode rightMode).2 := by
  cases leftMode <;> cases rightMode <;>
    simpa [packedLiteralModeStep, ModeFitsPosition] using hfit

theorem role3PostControlRow_literal {h : Nat} (hh : 0 < h)
    (left right : ParallelCell h PackedControl)
    (leftMode rightMode : PackedLiteralMode)
    (hleft : decodeLiteralTag left.2.role left.2.rootCtl = some leftMode)
    (hright : decodeLiteralTag right.2.role right.2.rootCtl = some rightMode)
    (hleftFit : ModeFitsPosition left.1 leftMode)
    (hrightFit : ModeFitsPosition right.1 rightMode) :
    role3PostControlRow h hh left right =
      let out := packedLiteralModeStep leftMode rightMode
      (writeLiteral left.2 out.1, writeLiteral right.2 out.2) := by
  have hleftRole : left.2.role ≠ stagingRole := by
    intro heq
    rw [heq, decodeLiteralTag_role_three] at hleft
    contradiction
  have hrightRole : right.2.role ≠ stagingRole := by
    intro heq
    rw [heq, decodeLiteralTag_role_three] at hright
    contradiction
  simp [role3PostControlRow, classifyAt, decodePostRoute, decodeLin,
    hleft, hright, hleftRole, hrightRole, hleftFit, hrightFit]

theorem role3PostControlRow_outputs_literal {h : Nat} (hh : 0 < h)
    (left right : ParallelCell h PackedControl)
    (hleft : AlignedLiteralControl left.1 left.2)
    (hright : AlignedLiteralControl right.1 right.2) :
    AlignedLiteralControl left.1 (role3PostControlRow h hh left right).1 ∧
      AlignedLiteralControl right.1
        (role3PostControlRow h hh left right).2 := by
  rcases hleft with ⟨leftMode, hleft, hleftFit⟩
  rcases hright with ⟨rightMode, hright, hrightFit⟩
  rw [role3PostControlRow_literal hh left right leftMode rightMode hleft hright
    hleftFit hrightFit]
  dsimp only
  constructor
  · exact ⟨(packedLiteralModeStep leftMode rightMode).1,
      decodeLiteralTag_writeLiteral _ _,
      modeFitsPosition_step_left left.1 leftMode rightMode hleftFit⟩
  · exact ⟨(packedLiteralModeStep leftMode rightMode).2,
      decodeLiteralTag_writeLiteral _ _,
      modeFitsPosition_step_right right.1 leftMode rightMode hrightFit⟩

/-- Large tag-level handoff envelope.  On an already stabilized grid it is
closed and executes QMAT rather than scrub.  No ProgramFlight legitimacy or
arbitrary-soup convergence statement is inferred from this envelope. -/
theorem allAlignedLiteral_parallelStep {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (q : Fin n → ParallelCell h PackedControl)
    (hgrid : PositionGrid hh ring q) (hq : AllAlignedLiteral q)
    (edge : Fin n) :
    AllAlignedLiteral
      (parallelStep hh ring (role3PostControlRow h hh) q edge) := by
  intro i
  have hout := role3PostControlRow_outputs_literal hh
    (q edge) (q (ring.rightNeighbor edge)) (hq edge)
      (hq (ring.rightNeighbor edge))
  by_cases hie : i = edge
  · subst i
    simpa [parallelStep] using hout.1
  · by_cases hir : i = ring.rightNeighbor edge
    · subst i
      have hpos := hgrid edge
      unfold positions at hpos
      simpa [parallelStep, hie, hpos] using hout.2
    · simpa [parallelStep, hie, hir] using hq i

theorem role3PostRow_uses_no_new_states (h : Nat) :
    (packedCellStates h).values.length = 262144 * h :=
  packedCellStates_length h

#print axioms decodeLin_encodeLin
#print axioms classifyAt_encodePostRoute
#print axioms role3PostControlRow_literal
#print axioms role3PostControlRow_outputs_literal
#print axioms allAlignedLiteral_parallelStep
#print axioms role3PostRow_uses_no_new_states

end PPLLRole3PostRow
