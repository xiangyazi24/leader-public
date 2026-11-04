import Leader.Wu.Authorization.SeamHygiene
import Leader.Wu.Sim.AuthSeamTransition

/-! Experimental line-outcome and local gap-settle variants. -/
set_option autoImplicit false

namespace PPLLAuthPStarVariant
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthChamp
open PPLLAuthSeam PPLLAuthSim

structure PStarCfg where
  outcomeRelay : Bool := false
  terminalAbort : Bool := false
  a5HoleRelease : Bool := false
  gapSettle : Bool := false
  gapRequireStamp : Bool := true
  gapDeferCleanWitness : Bool := false
  deriving Repr

def outcomeRelay : PStarCfg :=
  { outcomeRelay := true, terminalAbort := true, a5HoleRelease := true }

def gapSettleOnly : PStarCfg := { gapSettle := true }

def gapSettleUnstamped : PStarCfg :=
  { gapSettle := true, gapRequireStamp := false }

def gapSettleDeferCleanWitness : PStarCfg :=
  { gapSettle := true, gapRequireStamp := false, gapDeferCleanWitness := true }

/-- An aligned lineage initiator abandons CHECK/equality when its next physical
    neighbor has no main path. The hole's control state and marks are immaterial;
    the experimental unstamped flag also ignores the initiator's control mark.
    The R7 option defers on a nonnegative CLEAN record at the responder. -/
def settleGap {ψ : Nat} (v : PStarCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  if v.gapSettle && !l.core.leader && !r.core.leader && l.hasPath &&
      aligned l.core && (!v.gapRequireStamp || l.ctrl_mark == l.path_mark) &&
      (l.st == .CHECK_ready || l.st == .equal) &&
      l.core.label.val + 1 == r.core.label.val && !r.hasPath &&
      (!v.gapDeferCleanWitness ||
        !(match r.core.path5 with
          | some (lbl, _) => decide (lbl >= 0)
          | none => false)) then
    (l.lineage .depart, r)
  else (l, r)

/-- A neutral, leaderless, pathless line-A4/A6 transit holder. Its token mark is retained
    independently of the absent main-path mark; no path mark is rewritten. -/
def relayHolder {ψ : Nat} (u : AuthState ψ) : Bool :=
  !u.hasPath && u.st == .none && !u.core.leader &&
    u.path2_scope == .line &&
    (match u.core.path2 with | some t => (t.action == 4 || t.action == 6) | none => false)

/-- Retain the in-flight line A4/A6 at sanitation and skip control application until it
    reaches an occupied holder with a matching path mark. This relaxes AuthF holder
    validation only for the transient pathless relay state. -/
def sanitizeVariant {ψ : Nat} (cc : ChampCfg) (v : PStarCfg) (u : AuthState ψ) : AuthState ψ :=
  if v.outcomeRelay && relayHolder u then strictScopeOne cc u else champSanitizeP2 cc u

def applyVariant {ψ : Nat} (hψ : ψ > 0) (v : PStarCfg) (u : AuthState ψ) : AuthState ψ :=
  if v.outcomeRelay && relayHolder u then u else applyControlAuth hψ u

/-- Admit a line outcome into a neutral hole, including from a relay holder.
    Sanitation and control preserve that holder until onward delivery. -/
def entryVariant {ψ : Nat} (c : SeamCfg) (v : PStarCfg)
    (src dst : AuthState ψ) (t : Path2Info) : Entry :=
  if v.a5HoleRelease && t.action == 5 && src.path2_scope == .line &&
      src.st == .CHECK_ready && src.hasPath && aligned src.core &&
      src.path_mark == src.path2_mark && p2Valid src &&
      !dst.hasPath && dst.core.path2 == none && dst.st == .none &&
      !src.core.leader && !dst.core.leader then .ok
  else if v.outcomeRelay && (t.action == 4 || t.action == 6) && src.path2_scope == .line &&
      (p2Valid src || (v.outcomeRelay && relayHolder src)) &&
      !dst.hasPath && dst.core.path2 == none && dst.st == .none &&
      !src.core.leader && !dst.core.leader then .ok
  else entryS c src dst t

/-- `seamMoveTokensAuth` with hole entry and local terminal abort acknowledgments. -/
def moveTokensVariant {ψ : Nat} (c : SeamCfg) (v : PStarCfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let cc := c.base.claimCheck
  let failA4 : Bool := match l.core.path2 with
    | some tl => c.base.retire && tl.action == 4 && l.path2_scope == .line && p2Valid l &&
        canMoveR l.core tl && r.hasPath && l.path2_mark != r.path_mark
    | none => false
  let failA2 : Bool := match r.core.path2 with
    | some tr => c.base.retire && tr.action == 2 && r.path2_scope == .session && p2Valid r &&
        canMoveL r.core tr && l.hasPath &&
        (waveState l.st || l.st == .CHECK_ready || l.st == .equal || l.st == .larger || l.st == .less) &&
        l.ctrl_mark != r.path2_mark && !claimable cc l
    | none => false
  if failA4 || failA2 then
    ((if failA4 then clearCmpAuth l else l), (if failA2 then clearCmpAuth r else r))
  else
  let eR : Entry := match l.core.path2 with
    | some tl => if canMoveR l.core tl then entryVariant c v l r tl else .ok
    | none => .ok
  let eL : Entry := match r.core.path2 with
    | some tr => if canMoveL r.core tr then entryVariant c v r l tr else .ok
    | none => .ok
  let terminalA4 : Bool := v.terminalAbort && !l.core.leader && !r.core.leader &&
    l.hasPath && aligned l.core && l.path_mark == r.path2_mark &&
    l.core.label.val + 1 == r.core.label.val &&
    r.core.label.val == ψ - 1 && relayHolder r &&
    (match r.core.path2 with | some t => t.action == 4 | none => false)
  let terminalA6 : Bool := v.terminalAbort && !l.core.leader && !r.core.leader &&
    r.hasPath && aligned r.core && r.path_mark == l.path2_mark &&
    l.core.label.val + 1 == r.core.label.val &&
    l.core.label.val == 0 && relayHolder l &&
    (match l.core.path2 with | some t => t.action == 6 | none => false)
  let releaseA5 : Bool := v.a5HoleRelease && !l.core.leader && !r.core.leader &&
    l.st == .CHECK_ready && l.hasPath && aligned l.core &&
    l.core.label.val + 1 == r.core.label.val &&
    !r.hasPath && r.st == .none && r.core.path2 == none &&
    l.path_mark == l.path2_mark && eR == .ok &&
    (match l.core.path2 with
      | some t => t.action == 5 && l.path2_scope == .line && p2Valid l
      | none => false)
  let l := if terminalA6 then l.dropP2 else if eR == .reject then l.dropP2 else l
  let r := if terminalA4 then r.dropP2 else if eL == .reject then r.dropP2 else r
  let l := if releaseA5 || (terminalA4 && (l.st == .CHECK_ready || (isHead l && verdict l))) then
    l.lineage .depart else l
  let r := if terminalA6 && (r.st == .CHECK_ready || (isHead r && verdict r)) then
    r.lineage .depart else r
  match l.core.path2, r.core.path2 with
  | some tl, some tr =>
    if canMoveR l.core tl && canMoveL r.core tr then
      (receive eL r l (dec tr), receive eR l r (dec tl))
    else if canMoveR l.core tl && rightward tr && canMoveR r.core tr then
      (l.dropP2, r)
    else if canMoveL r.core tr && leftward tl && canMoveL l.core tl then
      (l, r.dropP2)
    else (l, r)
  | some tl, none =>
    if canMoveR l.core tl then (l.dropP2, receive eR l r (dec tl)) else (l, r)
  | none, some tr =>
    if canMoveL r.core tr then (receive eL r l (dec tr), r.dropP2) else (l, r)
  | none, none => (l, r)

/-- `seamMoveSourceAuth` with only sanitation, MOVE, and control changed. -/
def moveSourceVariant {ψ : Nat} (hψ : ψ > 0) (c : SeamCfg) (v : PStarCfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let cc := toChamp c
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.core.leader = true || (r.core.leader = true && r.core.label != nextLabel) then
    clearCmpAuth l else l
  let r := if r.core.leader = true then clearCmpAuth r else r
  let (l, r) := validateCheck l r
  let l := sanitizeVariant cc v l
  let r := sanitizeVariant cc v r
  let preL := l
  let preR := r
  let (l, r) := if l.st = .done then (l, r) else step1Auth l r
  let l := if c.lotteryScrub then
      match preL.core.path, preR.core.path, l.core.path with
      | .some _ _, .bot, .bot => { l with core := { l.core with p := false, p_carry := false } }
      | _, _, _ => l
    else l
  let l := if c.a2Preempt then
      let incoming2 : Bool := match r.core.path2 with
        | some t => r.path2_scope == .session && p2Valid r && t.action == 2 && canMoveL r.core t
        | none => false
      let linePre : Bool := l.hasPath && l.ctrl_mark == l.path_mark &&
        (l.st == .depart || l.st == .equal || l.st == .less) &&
        (match l.core.path2 with
          | none => true
          | some t' => t'.action == 6 && l.path2_scope == .line && l.path2_mark == l.path_mark)
      if incoming2 && linePre then (claimA2 r.path2_mark l).dropP2 else l
    else l
  let (l, r) := moveTokensVariant c v l r
  let (l, r) := leaderWallAuth l r
  let l := applyVariant hψ v l
  let r := applyVariant hψ v r
  let l := if r.st = .depart && l.core.label.val < ψ - 1 && l.st = .CHECK_ready &&
      (!c.lineageRelease || r.path_mark == l.path_mark) then
    l.lineage .depart else l
  (l, r)

/- Exact armed/episode pipeline copies; MOVE and the optional gap cut differ. -/
def beforeA {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) (v : PStarCfg) (l r : AuthState ψ)
    (er : Fin 3) (armed : Bool) : ((AuthState ψ × AuthState ψ) × Fin 3) × Bool :=
  let cc := toChamp c
  let q := lift2 (pPsiProbeWall hψ) l r
  let q := genSigAuth hψ κ q.1 q.2
  let q := (hygieneOne c q.1, hygieneOne c q.2)
  let q := seamCleanSourceAuth hψ c q.1 q.2
  let q := lift2Life (releaseSource hψ) q.1 q.2
  let q := lift2 (eliminateSig hψ) q.1 q.2
  let q := moveSourceVariant hψ c v q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
  let q := checkSourceAuth hψ c.base q.1 q.2
  let q := champDisappearAuth hψ cc q.1 q.2
  let q := settleGap v q.1 q.2
  let q := seamRepairAuth c q.1 q.2
  let ((q, er), charged) := compareLifecycleA κ c q.1 q.2 er armed
  ((suppressSigResetKillAuth hψ q.1 q.2, er), charged)


def beforeTA {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) (v : PStarCfg) (l r : AuthState ψ)
    (er : Fin 3) (armed : Bool) : (((AuthState ψ × AuthState ψ) × Fin 3) × (Bool × Bool)) × Bool :=
  let cc := toChamp c
  let p := (l, r)
  let q := lift2 (pPsiProbeWall hψ) p.1 p.2
  let t := touch2 (false, false) p q
  let p := q
  let q := genSigAuth hψ κ p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := (hygieneOne c p.1, hygieneOne c p.2)
  let t := touch2 t p q
  let p := q
  let q := seamCleanSourceAuth hψ c p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := lift2Life (releaseSource hψ) p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := lift2 (eliminateSig hψ) p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := moveSourceVariant hψ c v p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := (liftLife dropStale p.1, liftLife dropStale p.2)
  let t := touch2 t p q
  let p := q
  let q := preCheckResetAuth p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := (liftLife normalizeReady p.1, liftLife normalizeReady p.2)
  let t := touch2 t p q
  let p := q
  let q := checkSourceAuth hψ c.base p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := champDisappearAuth hψ cc p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := settleGap v p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := seamRepairAuth c p.1 p.2
  let t := touch2 t p q
  let p := q
  let ((q, er), charged) := compareLifecycleA κ c p.1 p.2 er armed
  let t := touch2 t p q
  let p := q
  let q := suppressSigResetKillAuth hψ p.1 p.2
  let t := touch2 t p q
  (((q, er), t), charged)


def stepTA {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) (v : PStarCfg) (l r : AuthState ψ) (el er : Fin 3)
    (armed : Bool) :
    ((AuthState ψ × AuthState ψ) × (Fin 3 × Fin 3)) × Bool :=
  let (((p, er), t), charged) := beforeTA hψ κ c v l r er armed
  let q := lift2 (k4Kernel hψ) p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := lift2 (writeWithBundle hψ) p.1 p.2
  let t := touch2 t p q
  let p := q
  let q := conserveAuth l r p
  let t := touch2 t p q
  let el := if t.1 then 0 else el
  let er := if t.2 then 0 else er
  ((q, (el, er)), charged)


def stepEA {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) (v : PStarCfg) (l r : AuthState ψ) (el er : Fin 3)
    (armed : Bool) :
    ((AuthState ψ × AuthState ψ) × (Fin 3 × Fin 3)) × Bool :=
  let ((q, er), charged) := beforeA hψ κ c v l r er armed
  let q := lift2 (k4Kernel hψ) q.1 q.2
  let q := lift2 (writeWithBundle hψ) q.1 q.2
  let q := conserveAuth l r q
  let el := if q.1.core.path = l.core.path then el else 0
  let er := if q.2.core.path = r.core.path then er else 0
  ((q, (el, er)), charged)


def stepA {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) (v : PStarCfg) (l r : AuthState ψ) (el er : Fin 3)
    (al ar : Nat) : ((AuthState ψ × AuthState ψ) × (Fin 3 × Fin 3)) × (Nat × Nat) :=
  let al := latchArm c l al
  let ar := latchArm c r ar
  let armed := (c.episodeResetArm && (l.core.reset_cmd || r.core.reset_cmd)) ||
    (c.episodeLatch && (al > 0 || ar > 0))
  let ((q, ctr), charged) :=
    if !c.episodeCap then ((seamStep hψ κ c l r, (el, er)), false) else
    if c.episodeResetTouch then stepTA hψ κ c v l r el er armed else
    stepEA hψ κ c v l r el er armed
  let al := latchDrain c charged al
  let ar := latchDrain c charged ar
  ((q, ctr), (latchArm c q.1 al, latchArm c q.2 ar))


/-- Bounded adapter preserving both EpisodeCap and latch sidecars. -/
def transition {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg) (v : PStarCfg) :
    AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ) :=
  if !(v.outcomeRelay || v.terminalAbort || v.a5HoleRelease || v.gapSettle) || !c.episodeCap then
    PPLLAuthSimSeam.seamTransitionCfg hψ κ c
  else fun a b => do
    let ((q, ep), ar) := stepA hψ κ c v (toState a) (toState b)
      a.m.episodes b.m.episodes a.m.armed b.m.armed
    let a' ← (reifyCore (κ := κ) q.1.core).mapError fun e =>
      s!"PStar: left output out of domain ({e})"
    let b' ← (reifyCore (κ := κ) q.2.core).mapError fun e =>
      s!"PStar: right output out of domain ({e})"
    pure (⟨a', { marksOf q.1 with episodes := ep.1, armed := ar.1 }⟩,
          ⟨b', { marksOf q.2 with episodes := ep.2, armed := ar.2 }⟩)

end PPLLAuthPStarVariant
