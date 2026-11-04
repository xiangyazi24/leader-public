import Leader.Wu.ZeroDivisible.K4BoundaryEquality

/-!
Independent round-three lock-cycle candidates over the pinned round-one BEQ
implementation. An arbitrary circular lock has no terminal `depart` cell from
which the original wave can create its first acknowledgement. These candidates
repair that missing progress event without introducing a birth rule, request
encoding, or additional field. They are experimental protocols, not convergence
theorems. The final Head guard retains unconditional pair support conservation.
-/
namespace PPLLAstraDesign3

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2

inductive Design where
  | ack | release | ackFlush | sourceAck | orphanAck | lifecycleAck | readyAck
  deriving DecidableEq

/-- Bootstrap the missing acknowledgement at an occupied locked tail, provided
its predecessor is locked and the path labels are consecutive. Token-free
endpoints avoid rewriting an active comparison. For psi=1 the single-cell
signal has no internal predecessor, so the boundary itself supplies the test.
The rule changes only the responder's wave state; all births still pass through
the existing comparison/CHECK implementation. -/
def ackTail {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some ll _, .some rl _ =>
    if l.leader = false ∧ r.leader = false ∧ l.path2 = none ∧ r.path2 = none ∧
        lockedState l.state ∧ r.state = .lock ∧ rl = ψ - 1 ∧
        (ll + 1 = rl ∨ (ψ = 1 ∧ ll = 0 ∧ rl = 0)) then
      (l, { r with state := .compare1 })
    else (l, r)
  | _, _ => (l, r)

/-- Alternative recovery: release an idle locked source tail at a locked
last/zero boundary. Its path is retained. A later internal interaction can use
the original lock/depart terminal rule to generate the acknowledgement, or the
released signal can move and be regenerated. This rule also changes no leader,
bullet, shield, absence or ID bit. -/
def releaseTail {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some ll _, .some rl _ =>
    if l.leader = false ∧ r.leader = false ∧ l.path2 = none ∧ r.path2 = none ∧
        l.state = .lock ∧ r.state = .lock ∧ ll = ψ - 1 ∧ rl = 0 then
      ({ l with state := .depart }, r)
    else (l, r)
  | _, _ => (l, r)

/-- Recover the legacy congest state, which the R1 comparison replacement no
longer creates or advances. Retain the carrier and token but release its wave
state, so the ordinary departure/lock rules can process it again. -/
def releaseCongest {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if u.leader = false ∧ u.state = .congest then { u with state := .depart } else u

/-- Preserve a newly issued CLEAN command against the later connection-copy
stage. This is the source-lifecycle repair, isolated from the request and
elimination changes. -/
def cleanSource {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let isCmd (t : Option (Int × Nat)) : Bool :=
    match t with | some (lbl, _) => decide (lbl = (-1 : Int)) | none => false
  let l := cleanSigGenConnect l
  let r := cleanSigGenConnect r
  let (l, r) := cleanSigStep3 l r
  let (l, r) := cleanSigStep4 l r
  let (l, r) := if isCmd l.path4 then (l, { r with path4 := none })
    else cleanSigStep5 hψ l r
  let (l, r) := if isCmd r.path5 then ({ l with path5 := none }, r)
    else cleanSigStep6 hψ l r
  (cleanSigCleanApply l, cleanSigCleanApply r)

/-- A done carrier orphaned by loss of its generating predecessor must not be
held forever. Only consecutive physical labels justify this local release. -/
def releaseSource {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r.state = .done ∧ r.label ≠ ⟨0, hψ⟩ ∧ l.label.val + 1 = r.label.val ∧
      l.state ≠ .produce ∧ l.state ≠ .done then
    (l, { r with state := .depart })
  else (l, r)

/-- R1 walled movement with only done source carriers held. A produce cell
holding a path may carry a foreign signal, so it is deliberately not held.
Token movement and application remain the exact R1 operations. -/
def moveSource {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.leader = true ∨ (r.leader = true ∧ r.label ≠ nextLabel) then
    clearCmp l else l
  let r := if r.leader = true then clearCmp r else r
  let (l, r) := if l.state = .done then (l, r)
    else sigMoveStep1With .dropMisaligned l r
  let (l, r) := PPLLFableDesignR1.moveTokens l r
  let (l, r) := leaderWall l r
  let l := sigMoveApplyControlConsume hψ l
  let r := sigMoveApplyControlConsume hψ r
  let l := if r.state = .depart ∧ l.label.val < ψ - 1 ∧ l.state = .CHECK_ready then
    { l with state := .depart } else l
  (l, r)

/-- R1 CHECK with done source carriers excluded from readiness. This prevents
checking a not-yet-departed part of the local generation wave against itself.
Foreign paths on produce cells remain eligible for ordinary CHECK. -/
def checkSource {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let ready (u : AgentState ψ) :=
    if waveState u.state ∨ u.state = .congest ∨ u.state = .done then u
    else checkSigSetReadyGuarded u
  let l := ready l
  let r := ready r
  let l := if r.state = .depart ∧ aligned r ∧ l.state = .equal ∧ aligned l ∧
      l.label.val < ψ - 1 then { l with state := .depart } else l
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := checkSigSetResult l
  let r := checkSigSetResult r
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
    (l, { r with leader := true }) else (l, r)

/-- Preserve a pathless produce cell until the reverse generation wave can
return. All acknowledgement, comparison and token semantics are explicitly R1;
round-trip request interpretation is not imported accidentally. -/
def compareSource {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := match l.path with
    | .bot => if l.state = .produce then l else { l with state := .none }
    | .some _ _ => l
  let (l, r) := PPLLFableDesignR1.maintain l r
  let (l, r) := PPLLFableDesignR1.wave l r
  let (l, r) := PPLLFableDesignR1.dropStray l r
  (PPLLFableDesignR1.landBackward l, PPLLFableDesignR1.landForward κ false true r)

/-- Occupied carriers in state none have no CHECK wave when misaligned and no
boundary departure event. A done carrier with a nonlocal path label cannot be
its own unfinished generation output. Release these orphan states; retain all
payloads so ordinary movement/comparison can process them. -/
def normalizeCarrier {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if u.leader then u else
  match u.path with
  | .bot => releaseCongest u
  | .some pl _ =>
    if u.state = .none ∨ u.state = .congest ∨
        (u.state = .done ∧ pl ≠ u.label.val) then
      { u with state := .depart } else u

/-- An occupied ready suffix behind a departed signal prefix cannot receive
CHECK equality from that prefix. Propagate departure through consecutive path
labels, preventing a fully occupied self-source fragment from freezing. This
rule writes no equality result and creates no leader or comparison token. -/
def releaseReadySuffix {ψ : Nat} (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some ll _, .some rl _ =>
    if l.leader = false ∧ r.leader = false ∧ l.state = .depart ∧
        r.state = .CHECK_ready ∧ ll + 1 = rl then
      (l, { r with state := .depart }) else (l, r)
  | _, _ => (l, r)

/-- Normalize two control states with no live consumer at their current
location. Toss is generated and consumed only at physical label zero; a toss
elsewhere is orphaned. Misaligned toss_done is ignored both by stale-blocker
cleanup and by CHECK readiness, while having no direct continuation. Release
only these follower states and retain every payload/token and p/p_carry bit. -/
def normalizeOrphan {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if u.leader then u else
  if u.state = .toss ∧ u.label.val ≠ 0 then { u with state := .depart } else
  match u.path with
  | .some pl _ =>
    if u.state = .toss_done ∧ pl ≠ u.label.val then { u with state := .depart } else u
  | .bot => u

/-- Give an occupied carrier priority over stale local bookkeeping. GENSIG's
only assignments creating produce require path=bot, while both own-path
creation sites assign done. Thus produce with an occupied path is either
arbitrary debris or a foreign carrier arriving during production. Release it
for transport and permit local generation to restart once its slot is empty.
Local CHECK results require alignment; misaligned results cannot certify the
current carrier. Preserve payloads, tokens and lottery registers. -/
def normalizeLifecycle {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  let u := normalizeCarrier (normalizeOrphan u)
  if u.leader then u else
  match u.path with
  | .bot => u
  | .some pl _ =>
    if u.state = .produce ∨
        ((u.state = .equal ∨ u.state = .larger ∨ u.state = .less) ∧ pl ≠ u.label.val) then
      { u with state := .depart } else u

/-- Distinguish an aligned foreign arrival from a carrier departing its own
source. Occupied produce is foreign-arrival overlap, since GENSIG writes its
own carrier together with done. An aligned arrival must enter ordinary CHECK
readiness; assigning depart would incorrectly exempt it as a self-source and
can circulate a lone head carrier forever. Misaligned arrivals remain in
transport mode. Aligned none is already a CHECK candidate and must not pass
through the post-CHECK carrier release before readiness is evaluated. Other
lifecycle normalization is unchanged. -/
def normalizeReady {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  let u := normalizeOrphan u
  let u := if u.state = .none ∧ aligned u then u else normalizeCarrier u
  if u.leader then u else
  match u.path with
  | .bot => u
  | .some pl _ =>
    if u.state = .produce then
      { u with state := if pl = u.label.val then .none else .depart }
    else if (u.state = .equal ∨ u.state = .larger ∨ u.state = .less) ∧ pl ≠ u.label.val then
      { u with state := .depart } else u

/-- Complete the lock/acknowledgement handshake under stale mixed phases.
An acknowledged prefix is still locked and must lock a departed suffix.
A terminal compare2 cell also supplies an acknowledgement to its locked
predecessor, but retains its own emitter state and any live token. These rules
propagate status only; they never create a token or leader. -/
def completeWave {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some ll _, .some rl _ =>
    let r := if lockedState l.state ∧ rl = ll + 1 ∧ r.state = .depart then
      { r with state := if rl = ψ - 1 then .compare1 else .lock } else r
    let l := if l.state = .lock ∧ r.state = .compare2 ∧ rl = ψ - 1 ∧
        (rl = ll + 1 ∨ (ψ = 1 ∧ ll = 0 ∧ rl = 0)) then
      { l with state := .compare1 } else l
    (l, r)
  | _, _ => (l, r)

/-- Source-preserving comparison with handshake completion after maintenance
and before the original wave rules. The original token readers and emitters
remain R1; a busy tail's token is not cleared by acknowledgement recovery. -/
def compareLifecycle {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := match l.path with
    | .bot => if l.state = .produce then l else { l with state := .none }
    | .some _ _ => l
  let (l, r) := PPLLFableDesignR1.maintain l r
  let (l, r) := completeWave l r
  let (l, r) := PPLLFableDesignR1.wave l r
  let (l, r) := PPLLFableDesignR1.dropStray l r
  (PPLLFableDesignR1.landBackward l, PPLLFableDesignR1.landForward κ false true r)

/-- Choose one local lock-progress proposal. This is run after the existing
full-wall reset and immediately before the original BEQ comparison stage. -/
def repair {ψ : Nat} (d : Design) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match d with
  | .ack => ackTail l r
  | .release => releaseTail l r
  | .ackFlush => ackTail (releaseCongest l) (releaseCongest r)
  | .sourceAck =>
    let q := releaseReadySuffix (normalizeCarrier l) (normalizeCarrier r)
    ackTail q.1 q.2
  | .orphanAck | .lifecycleAck | .readyAck =>
    let q := releaseReadySuffix (normalizeCarrier (normalizeOrphan l))
      (normalizeCarrier (normalizeOrphan r))
    ackTail q.1 q.2

/-- The first three candidates retain the pinned R2 prefix. The sourceAck
orphanAck and lifecycleAck candidates additionally repair source generation
and CLEAN, with all token semantics still R1. LifecycleAck also normalizes
carrier roles before CHECK and completes the wave handshake after maintenance. Every candidate inserts its local lock-progress proposal
before comparison. No request rule from the earlier design is imported. -/
def beforeElimination {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (d : Design)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let src : Bool := decide (d = .sourceAck ∨ d = .orphanAck ∨ d = .lifecycleAck ∨ d = .readyAck)
  let q := pPsiProbeWall hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := if src then cleanSource hψ q.1 q.2 else cleanSig hψ q.1 q.2
  let q := if src then releaseSource hψ q.1 q.2 else q
  let q := eliminateSig hψ q.1 q.2
  let q := if src then moveSource hψ q.1 q.2 else sigMoveF hψ true .dropMisaligned q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := if d = .lifecycleAck then (normalizeLifecycle q.1, normalizeLifecycle q.2)
    else if d = .readyAck then (normalizeReady q.1, normalizeReady q.2) else q
  let q := if src then checkSource hψ q.1 q.2 else checkSigF hψ κ false q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := repair d q.1 q.2
  let q := if d = .lifecycleAck ∨ d = .readyAck then compareLifecycle κ q.1 q.2
    else if src then compareSource κ q.1 q.2 else compareSigF κ false true q.1 q.2
  suppressSigResetKill hψ q.1 q.2

/-- Lock progress followed by the unchanged K4, bundle-carrying WRITE, and
input-relative Head conservation guard. This is a new experimental system;
its safety theorem below does not assert birth suppression or convergence. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (d : Design)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := beforeElimination hψ κ d l r
  let q := k4Kernel hψ q.1 q.2
  let q := writeWithBundle hψ q.1 q.2
  conserve .head l r q

def variants : List (String × Design) :=
  [("astR3AckHeadK4", .ack), ("astR3ReleaseHeadK4", .release),
   ("astR3AckFlushHeadK4", .ackFlush), ("astR3SourceAckHeadK4", .sourceAck),
   ("astR3OrphanAckHeadK4", .orphanAck),
   ("astR3LifecycleAckHeadK4", .lifecycleAck),
   ("astR3ReadyAckHeadK4", .readyAck)]

/-- Every proposal retains a leader in a nonempty input pair, because the
unchanged final Head guard is applied relative to the original input. -/
theorem pipeline_nonempty {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (d : Design)
    (l r : AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (pipeline hψ κ d l r).1.leader = true ∨ (pipeline hψ κ d l r).2.leader = true := by
  exact conserve_nonempty .head l r _ h

end PPLLAstraDesign3
