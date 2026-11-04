import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false

namespace R2CoherenceV31PhaseDebt

open R2CoherenceV31

variable {n ψ κ τ : Nat}

/-- A live phase token must carry the mark belonging to its phase family. -/
def tokenMarkOKB (u : Cell ψ κ τ) : Bool :=
  match u.ctl.tok with
  | .none => true
  | .seek => decide (u.ctl.mark = .closing)
  | .sweep => decide (u.ctl.mark = .closing)
  | .commit => decide (u.ctl.mark = .closing)
  | .release => decide (u.ctl.mark = .releasing)
  | .scrubL => decide (u.ctl.mark = .releasing)
  | .openR => decide (u.ctl.mark = .releasing)

def phaseMarkDebtV31 (u : Cell ψ κ τ) : Nat :=
  if tokenMarkOKB u then 0 else 1

def activeTokenB (u : Cell ψ κ τ) : Bool :=
  decide (u.ctl.tok ≠ .none)

/-- Two adjacent live phase tokens are a malformed local superposition. -/
def superpositionDebtV31 (l r : Cell ψ κ τ) : Nat :=
  if activeTokenB l && activeTokenB r then 1 else 0

/-- Keep this boundary test conservative: tokenless closing/releasing trails are
legal, as are the open/releasing boundaries made by `openR`.  What cannot be a
single legal in-flight front on a successor edge is a direct open/sealed jump. -/
def impossiblePassiveBoundaryB (l r : Cell ψ κ τ) : Bool :=
  let tokenless :=
    (decide (l.ctl.tok = .none) : Bool) &&
      (decide (r.ctl.tok = .none) : Bool)
  let openSealed :=
    ((decide (l.ctl.mark = .open) : Bool) &&
       (decide (r.ctl.mark = .sealed) : Bool)) ||
    ((decide (l.ctl.mark = .sealed) : Bool) &&
       (decide (r.ctl.mark = .open) : Bool))
  tokenless && successorB l r && openSealed

def impossiblePassiveBoundaryDebtV31 (l r : Cell ψ κ τ) : Nat :=
  if impossiblePassiveBoundaryB l r then 1 else 0

/-- Label geometry must be either a successor edge or an edge entering a root. -/
def geometryDebtV31 (l r : Cell ψ κ τ) : Nat :=
  if passiveEdgeOKV3 l r then 0 else 1

/-- Conditions checked only when the left endpoint is the dispatcher-active
front.  In particular a sweep/openR token seen as the right endpoint of its
incoming edge is not charged. -/
def leftFrontDebtV31 (l r : Cell ψ κ τ) : Nat :=
  match l.ctl.tok with
  | .sweep =>
      if successorB l r && !atTerminalB l then 0 else 1
  | .release =>
      if successorB l r && !atTerminalB l && writerQuiet r then 0 else 1
  | .openR =>
      if successorB l r && !atTerminalB l then 0 else 1
  | _ => 0

/-- Conditions checked only when the right endpoint is the dispatcher-active
front.  `commitStageV3` explicitly admits the two root boundary cases;
`scrubLStageV3` explicitly rejects a root responder. -/
def rightFrontDebtV31 (l r : Cell ψ κ τ) : Nat :=
  match r.ctl.tok with
  | .commit =>
      if successorB l r || atRootB l || atRootB r then 0 else 1
  | .scrubL =>
      if successorB l r && !atRootB r then 0 else 1
  | _ => 0

def activeSideDebtV31 (l r : Cell ψ κ τ) : Nat :=
  leftFrontDebtV31 l r + rightFrontDebtV31 l r

/-- Concrete per-directed-edge phase defect cost.  Every summand is 0/1, so
`phaseDebtV31 l r ≤ 7` is immediate if/when the global bound is needed. -/
def phaseDebtV31 (l r : Cell ψ κ τ) : Nat :=
  phaseMarkDebtV31 l +
  phaseMarkDebtV31 r +
  superpositionDebtV31 l r +
  impossiblePassiveBoundaryDebtV31 l r +
  geometryDebtV31 l r +
  leftFrontDebtV31 l r +
  rightFrontDebtV31 l r

instance mainClearV3Dec (u : Cell ψ κ τ) : Decidable (MainClearV3 u) := by
  unfold MainClearV3
  infer_instance

instance intrinsicFreshAtV3Dec (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    Decidable (IntrinsicFreshAtV3 ring C i) := by
  unfold IntrinsicFreshAtV3
  infer_instance

/-- Number of physically non-main-clear members of the current psi-group. -/
def groupMainDebtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  ((List.range ψ).map (fun k =>
    let j := R2Coherence.groupPos ring (eraseCfgV3 C) i k
    if decide (MainClearV3 (C j)) then 0 else 1)).sum

/-- One unit exactly when the strengthened openR owner-freshness clause fails. -/
def openROwnerFreshDebtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  if decide (OpenROwnerFreshV3 ring C i) then 0 else 1


/-- Weighted current ControllerShapeV3 obligation at one physical cell.
Zero is equivalent to all shape clauses triggered by this cell. -/
def shapeRepairDebtAtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  let u := C i
  let gm := groupMainDebtV32 ring C i
  let ofresh := openROwnerFreshDebtV32 ring C i
  let sealed := if u.ctl.mark = .sealed then gm else 0
  let tok :=
    match u.ctl.tok with
    | .release =>
        (if u.ctl.mark = .releasing then 0 else 1) + gm
    | .scrubL =>
        (if u.ctl.mark = .releasing then 0 else 1) +
          (if atRootB u then 1 else 0) + gm
    | .openR =>
        (if u.ctl.mark = .releasing then 0 else 1) + ofresh
    | _ => 0
  sealed + tok


/-- One unit for a failed current FreshEqualPrefix obligation. -/
def coherenceDebtAtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  if decide
      (R2Coherence.FreshEqualPrefix ring (eraseCfgV3 C) i) then 0 else 1

/-- Exact current proxy debt at one physical cell. -/
def proxyDebtAtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  shapeRepairDebtAtV32 ring C i + coherenceDebtAtV32 ring C i

/-- seek/sweep/commit must pre-pay the dirty group that a later commit would
otherwise turn into a newly-created sealed violation. -/
def latentMainDebtAtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  match (C i).ctl.tok with
  | .seek | .sweep | .commit => groupMainDebtV32 ring C i
  | _ => 0

/-- Strict remaining-work clock for the six active phases. -/
def phaseClockAtV32 (u : Cell ψ κ τ) : Nat :=
  let lab := (raw u).label.val
  let span := ψ + 1
  let right := ψ - 1 - lab
  match u.ctl.tok with
  | .none => 0
  | .seek => 5 * span + lab
  | .sweep => 4 * span + right
  | .commit => 3 * span + lab
  | .release => 2 * span + right
  | .scrubL => span + lab
  | .openR => right

def clockNeededBv32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Bool :=
  let u := C i
  let gm := groupMainDebtV32 ring C i
  let ofresh := openROwnerFreshDebtV32 ring C i
  let markBad : Bool := decide (phaseMarkDebtV31 u ≠ 0)
  let gmBad : Bool := decide (gm ≠ 0)
  let ofreshBad : Bool := decide (ofresh ≠ 0)
  match u.ctl.tok with
  | .none => false
  | .seek | .sweep | .commit => gmBad
  | .release => markBad || gmBad
  | .scrubL => markBad || atRootB u || gmBad
  | .openR => markBad || ofreshBad



def repairClockAtV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  if clockNeededBv32 ring C i then phaseClockAtV32 (C i) else 0

/-- Primary reserve for main debt that an already-live phase can materialize.
Seek/sweep prepay the eventual terminal commit.  A commit at label j can create
one sealed obligation and leave a commit at label j-1, hence `(j+1) * gm`.
Release/scrub/openR prepay a possible restart into a full seek. -/
def phaseMaterializationDebtAtV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  let gm := groupMainDebtV32 ring C i
  let lab := (raw (C i)).label.val
  match (C i).ctl.tok with
  | .none => 0
  | .seek | .sweep => ψ * gm
  | .commit => (lab + 1) * gm
  | .release | .scrubL | .openR => ψ * gm




def phaseMaterializationDebtAtNatV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) (k : Nat) : Nat :=
  if hk : k < n then
    phaseMaterializationDebtAtV33 ring C ⟨k, hk⟩
  else
    0




def phaseMaterializationDebtV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Nat :=
  ((List.range n).map (phaseMaterializationDebtAtNatV33 ring C)).sum


/-- Full primary reserve needed by a newly-created seek, plus one unit.
The +1 is the cash-out premium: when the creator edge fires, this term
vanishes and the child seek carries only `ψ * gm`. -/
def seekCreationPrechargeAtV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  ψ * groupMainDebtV32 ring C i + 1


/-- Exact open/open hazard creator.  V31 holds the physical pair on the hazard
arm, so the current target-group main debt is the debt of the created seek. -/
def openHazardCreatorPrechargeAtV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  let j := ring.rightNeighbor i
  let l := C i
  let r := C j
  if h2 : 2 ≤ ψ then
    let hψ : 0 < ψ :=
      Nat.lt_of_lt_of_le (by decide : 0 < 2) h2
    let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
    if pairHazardV3 l.phys r.phys q.1 q.2 then
      if endpointHazardV3 r.phys q.2 then
        seekCreationPrechargeAtV33 ring C j
      else
        seekCreationPrechargeAtV33 ring C i
    else
      0
  else
    0


/-- One-step predecessor charge, following the actual `rowV3` dispatcher
priority.  Active malformed/restart arms get the full seek reserve +1 so the
clock jump back to `.seek` is paid at the primary stride.  For a nonquiet
release which creates `.commit`, the seek reserve is a conservative upper
bound on the commit reserve because `label+1 ≤ ψ` in admitted geometry. -/
def creatorPrechargeAtV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Nat :=
  let j := ring.rightNeighbor i
  let l := C i
  let r := C j
  if r.ctl.tok = .seek then
    0
  else if l.ctl.tok = .sweep then
    if successorB l r then 0
    else seekCreationPrechargeAtV33 ring C i
  else if r.ctl.tok = .commit then
    0
  else if l.ctl.tok = .release then
    if successorB l r then
      if writerQuiet r then
        0
      else if atRootB l then
        0
      else
        seekCreationPrechargeAtV33 ring C i
    else
      seekCreationPrechargeAtV33 ring C i
  else if r.ctl.tok = .scrubL then
    if successorB l r then
      if atRootB r then
        seekCreationPrechargeAtV33 ring C j
      else
        0
    else
      seekCreationPrechargeAtV33 ring C j
  else if l.ctl.tok = .openR then
    if successorB l r then 0
    else seekCreationPrechargeAtV33 ring C i
  else if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then
      if atRootB l && successorB l r && writerQuiet l && writerQuiet r then
        -- `sealedStageV3` creates a release at l.
        seekCreationPrechargeAtV33 ring C i
      else
        0
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      openHazardCreatorPrechargeAtV33 ring C i
    else if passiveEdgeOKV3 l r then
      -- `normalizePassiveV3` creates a seek at the responder.
      seekCreationPrechargeAtV33 ring C j
    else
      0
  else
    0




def creatorPrechargeAtNatV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) (k : Nat) : Nat :=
  if hk : k < n then
    creatorPrechargeAtV33 ring C ⟨k, hk⟩
  else
    0




def creatorPrechargeV33
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Nat :=
  ((List.range n).map (creatorPrechargeAtNatV33 ring C)).sum


def proxyDebtAtNatV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (k : Nat) : Nat :=
  if hk : k < n then proxyDebtAtV32 ring C ⟨k, hk⟩ else 0


/-- Work tier: latent dirty-group debt plus the phase clock. -/
def workDebtAtNatV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (k : Nat) : Nat :=
  if hk : k < n then
    let i : Fin n := ⟨k, hk⟩
    latentMainDebtAtV32 ring C i + repairClockAtV32 ring C i
  else
    0

-- `workDebtV32` itself is unchanged.


-- `workDebtV32` itself is unchanged.



/-- Zero exactly when the current shape/coherence proxy is satisfied. -/
def proxyDebtV32 (ring : DirectedRing n) (C : FC n ψ κ τ) : Nat :=
  ((List.range n).map (proxyDebtAtNatV32 ring C)).sum


def workDebtV32 (ring : DirectedRing n) (C : FC n ψ κ τ) : Nat :=
  ((List.range n).map (workDebtAtNatV32 ring C)).sum



def edgeDebtAtV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) (k : Nat) : Nat :=
  if hk : k < n then
    let i : Fin n := ⟨k, hk⟩
    phaseDebtV31 (C i) (C (ring.rightNeighbor i))
  else
    0


def edgeDebtRankV31 (ring : DirectedRing n) (C : FC n ψ κ τ) : Nat :=
  ((List.range n).map (edgeDebtAtV31 ring C)).sum


def rankStrideV32 (ψ : Nat) : Nat :=
  8 * (ψ + 1) + 8



/-- Group-aware rank.  The V33 precharge declarations may remain in the
file; they are simply unused by this experiment. -/
def R (ring : DirectedRing n) (C : FC n ψ κ τ) : Nat :=
  let bad := proxyDebtV32 ring C
  if bad = 0 then 0
  else
    rankStrideV32 ψ * bad +
      workDebtV32 ring C + edgeDebtRankV31 ring C

-- run/verification/probes/R2CoherenceV31Recovery.lean



end R2CoherenceV31PhaseDebt
