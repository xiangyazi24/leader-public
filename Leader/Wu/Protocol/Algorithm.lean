import Leader.Wu.Protocol.State

/-!
# Concrete P_PLL Transition Function

Concrete transcription of all 20 algorithms from Wu's thesis. `ppll l r`
composes 11 sub-algorithms sequentially on each interacting pair.  A line-by-
line fidelity audit is ongoing: comments below mark places where the printed
pseudocode is ill-typed or omits an apparently necessary token-consumption
assignment. See `FORMALIZATION_AUDIT.md`; do not describe this module merely
compiling as proof that every transcription choice is faithful.
-/

namespace PPLL

variable {ψ : Nat}

private def finMax {n : Nat} (a b : Fin n) : Fin n :=
  if a.val ≥ b.val then a else b

def writeActionToState : WriteAction → WriteState
  | .overwrite => .overwrite
  | .move_flip => .move_flip
  | .move => .move
  | .increment_group => .increment_group
  | .none => .none

/-! ## Algorithm 2: P'_ψ -/

def pPsi (hψ : ψ > 0) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  if r.label ≠ nextLabel then
    let r := if r.probe = true then
      { r with leader := true, label := ⟨0, hψ⟩, probe := false }
    else r
    let l := if l.phase = false then
      if l.leader = false then { l with phase := true, probe := true }
      else { l with phase := true }
    else l
    let r := if r.leader = false then
      { r with label := nextLabel, phase := false }
    else r
    (l, r)
  else
    if r.probe = true then
      ({ l with probe := true }, { r with probe := false })
    else (l, r)

/-! ## Algorithm 3: WAIT -/

def wait (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r := if r.label = ⟨0, hψ⟩ then
    { r with reset := true, h_field := false }
  else r
  let l := if l.label = ⟨0, hψ⟩ then
    if l.h_field = true then { l with h_field := false, carry := true }
    else { l with h_field := true }
  else l
  -- Algorithm 3 omits `l.carry ← 0` after consumption. We clear the token in
  -- each branch; the literal persistent-carry reading would repeatedly fire.
  let (l, r) := if l.carry = true then
    if r.h_field = true then
      if r.label = ⟨ψ - 1, by omega⟩ then
        ({ l with carry := false },
         { r with h_field := false, count := r.count + 1 })
      else
        ({ l with carry := false },
         { r with h_field := false, carry := true })
    else
      ({ l with carry := false }, { r with h_field := true })
  else (l, r)
  let (l, r) := if l.reset = true then
    let r := if r.label ≠ ⟨ψ - 1, by omega⟩ then
      { r with reset := true }
    else r
    ({ l with reset := false }, { r with h_field := false })
  else (l, r)
  let r := if r.label = ⟨ψ - 1, by omega⟩ ∧ r.count = κ then
    { r with wait := false }
  else r
  let (l, r) := if r.wait = false ∧ l.label ≠ ⟨ψ - 1, by omega⟩ then
    ({ l with wait := false }, { r with wait := true })
  else (l, r)
  (l, r)

/-! ## Algorithm 4: GENSIG -/

def genSig (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := wait hψ κ l r
  let l :=
    if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧
       l.wait = false ∧ l.path = .bot then
      { l with state := .produce }
    else l
  let r :=
    if r.label ≠ ⟨0, hψ⟩ ∧ l.state = .produce ∧ r.path = .bot then
      { r with state := .produce }
    else r
  let r :=
    if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .produce then
      { r with state := .done,
               path := .some r.label.val (if r.bit then 1 else 0) }
    else r
  let (l, r) :=
    if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.state = .produce ∧
       r.state = .done then
      ({ l with state := .done,
                path := .some l.label.val (if l.bit then 1 else 0) },
       { r with state := .depart })
    else (l, r)
  let l :=
    if l.label = ⟨0, hψ⟩ ∧ l.state = .done then
      { l with state := .depart, wait := true }
    else l
  (l, r)

/-! ## Algorithm 5: CLEAN_SIG -/

def cleanSigGenConnect (u : AgentState ψ) : AgentState ψ := match u.path with
  | .some pathLabel _ =>
    let u := if pathLabel ≠ 0 then
      { u with path4 := some (Int.ofNat pathLabel, 1) } else u
    if pathLabel ≠ ψ - 1 then
      { u with path5 := some (Int.ofNat pathLabel, 1) } else u
  | .bot => u

def cleanSigCleanApply (u : AgentState ψ) : AgentState ψ := match u.path with
  | .bot => u
  | .some pathLabel _ =>
    let u := match u.path4 with
      | some (lbl, _) =>
        if lbl = (-1 : Int) then
          let u := if pathLabel = 0 then { u with path4 := none } else u
          { u with path := .bot }
        else u
      | none => u
    match u.path5 with
    | some (lbl, _) =>
      if lbl = (-1 : Int) then
        let u := if pathLabel = ψ - 1 then { u with path5 := none } else u
        { u with path := .bot }
      else u
    | none => u

def cleanSigStep3 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match r.path4, l.path with
  | some (p4Label, p4Bit), .some lLabel _ =>
    if p4Label ≠ (-1 : Int) then
      let r := if p4Label ≠ Int.ofNat (lLabel + 1) then
        { r with path5 := some ((-1 : Int), 1 - p4Bit) } else r
      (l, { r with path4 := none })
    else (l, r)
  | _, _ => (l, r)

def cleanSigStep4 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path5, r.path with
  | some (p5Label, p5Bit), .some rLabel _ =>
    if p5Label ≠ (-1 : Int) then
      let l := if p5Label ≠ Int.ofNat rLabel - 1 then
        { l with path4 := some ((-1 : Int), 1 - p5Bit) } else l
      ({ l with path5 := none }, r)
    else (l, r)
  | _, _ => (l, r)

def cleanSigStep5 (hψ : ψ > 0) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match r.path4 with
  | some p4 =>
    let r := { r with path4 := none }
    if l.label = (⟨0, hψ⟩ : Fin ψ) then
      if p4.2 = 1 then ({ l with path4 := some (p4.1, 0) }, r)
      else ({ l with path4 := none }, r)
    else ({ l with path4 := some p4 }, r)
  | none => (l, r)

def cleanSigStep6 (hψ : ψ > 0) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path5 with
  | some p5 =>
    let l := { l with path5 := none }
    if r.label = (⟨ψ - 1, by omega⟩ : Fin ψ) then
      if p5.2 = 1 then (l, { r with path5 := some (p5.1, 0) })
      else (l, { r with path5 := none })
    else (l, { r with path5 := some p5 })
  | none => (l, r)

def cleanSig (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := cleanSigGenConnect l
  let r := cleanSigGenConnect r
  let (l, r) := cleanSigStep3 l r
  let (l, r) := cleanSigStep4 l r
  let (l, r) := cleanSigStep5 hψ l r
  let (l, r) := cleanSigStep6 hψ l r
  let l := cleanSigCleanApply l
  let r := cleanSigCleanApply r
  (l, r)

/-! ## Algorithm 9: ELIMINATE_SIG -/

def eliminateSig (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r.state = .eliminate_signal then
    let l := if l.label ≠ ⟨ψ - 1, by omega⟩ then
      { l with state := MainState.eliminate_signal }
    else l
    (l, { r with path := PathInfo.bot, state := MainState.none })
  else (l, r)

/-! ## Algorithm 12: CHECK_BIT -/

def checkBit (agentBit : Bool) (signalBit : Nat) : MainState :=
  let b := if agentBit then 1 else 0
  if b = signalBit then .equal
  else if b > signalBit then .larger
  else .less

def checkBitWS (agentBit : Bool) (signalBit : Nat) : WriteState :=
  let b := if agentBit then 1 else 0
  if b = signalBit then .equal
  else if b > signalBit then .larger
  else .less

/-! ## Algorithm 11: CHECK -/

def checkSigSetReady (u : AgentState ψ) : AgentState ψ :=
  match u.path with
  | .some label _ =>
    if u.label.val = label ∧ u.state ≠ .depart ∧ u.state ≠ .equal ∧
       u.state ≠ .larger ∧ u.state ≠ .less then
      { u with state := .CHECK_ready }
    else u
  | .bot => u

def checkSigCheckL (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ :=
  match u.path with
  | .some 0 pathBit =>
    if u.label = ⟨0, hψ⟩ ∧ u.state = .CHECK_ready then
      { u with state := checkBit u.bit pathBit }
    else u
  | _ => u

def checkSigCheckR (hψ : ψ > 0) (l r : AgentState ψ) : AgentState ψ :=
  match r.path with
  | .some _ pathBit =>
    if l.label.val < ψ - 1 ∧ l.state = .equal then
      if r.state = .CHECK_ready then
        { r with state := checkBit r.bit pathBit }
      else r
    else r
  | _ => r

def checkSigSetResult (u : AgentState ψ) : AgentState ψ :=
  let u := if u.state = .larger then
    { u with path2 := some ⟨0, 0, 0, 4⟩ }
  else u
  if u.state = .less then
    { u with path2 := some ⟨0, 0, 0, 6⟩ }
  else u

/-- Final leader-creation assignment of Algorithm 11. -/
def checkSigSetLeader (hψ : ψ > 0) (r : AgentState ψ) : AgentState ψ :=
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
    { r with leader := true }
  else r

def checkSigStaged (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := checkSigSetReady l
  let r := checkSigSetReady r
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := checkSigSetResult l
  let r := checkSigSetResult r
  (l, checkSigSetLeader hψ r)

def checkSig (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := checkSigSetReady l
  let r := checkSigSetReady r
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := checkSigSetResult l
  let r := checkSigSetResult r
  let r :=
    if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
      { r with leader := true }
    else r
  (l, r)

theorem checkSig_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    checkSig hψ l r = checkSigStaged hψ l r := by
  rfl

/-! ## Algorithm 13: DISAPPEAR -/

/-- Responder toss completion and action-5 generation. -/
def disappearStartR (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r :=
    if r.state = .toss ∧ r.label = ⟨0, hψ⟩ then
      { r with state := .toss_done,
               path2 := some ⟨0, 0, 0, 5⟩, p := false }
    else r
  (l, r)

/-- Initiator toss counter preparation. -/
def disappearStartL (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l :=
    if l.state = .toss ∧ l.label = ⟨0, hψ⟩ then
      if l.p = true then { l with p := false, p_carry := true }
      else { l with p := true }
    else l
  (l, r)

/-- Single-use carry stage of Algorithm 13. -/
def disappearCarry (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if l.p_carry = true then
    if r.p = true then
      if r.label = ⟨ψ - 1, by omega⟩ then
        ({ l with p_carry := false },
         { r with p := false, state := .eliminate_signal })
      else
        ({ l with p_carry := false },
         { r with p := false, p_carry := true })
    else
      ({ l with p_carry := false }, { r with p := true })
  else (l, r)

def disappearStaged (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := disappearStartR hψ l r
  let q := disappearStartL hψ q.1 q.2
  disappearCarry hψ q.1 q.2

def disappear (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r :=
    if r.state = .toss ∧ r.label = ⟨0, hψ⟩ then
      { r with state := .toss_done,
               path2 := some ⟨0, 0, 0, 5⟩, p := false }
    else r
  let l :=
    if l.state = .toss ∧ l.label = ⟨0, hψ⟩ then
      if l.p = true then { l with p := false, p_carry := true }
      else { l with p := true }
    else l
  -- As in WAIT, Algorithm 13 omits clearing a consumed carry token. This is
  -- the inferred single-use-token interpretation, not a literal assignment.
  let (l, r) := if l.p_carry = true then
    if r.p = true then
      if r.label = ⟨ψ - 1, by omega⟩ then
        ({ l with p_carry := false },
         { r with p := false, state := .eliminate_signal })
      else
        ({ l with p_carry := false },
         { r with p := false, p_carry := true })
    else
      ({ l with p_carry := false }, { r with p := true })
  else (l, r)
  (l, r)

theorem disappear_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    disappear hψ l r = disappearStaged hψ l r := by
  rfl

/-! ## Algorithm 7: CMP_UPDATE -/

def cmpUpdatePropagate (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if l.label = ⟨ψ - 1, by omega⟩ ∧ l.state = .congest then
    (l, { r with state := .lock })
  else if r.label = ⟨ψ - 1, by omega⟩ ∧ l.state = .lock then
    (l, { r with state := .compare1 })
  else if l.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .compare1 then
    ({ l with state := .compare2 }, r)
  else
    if l.state = .congest ∨ l.state = .lock then
      (l, { r with state := l.state })
    else if r.state = .compare1 ∨ r.state = .compare2 then
      ({ l with state := r.state }, r)
    else (l, r)

def cmpUpdateSetPath2 (hψ : ψ > 0) (l : AgentState ψ) : AgentState ψ :=
  match l.path with
  | .some pathLabel pathBit =>
    if l.label = ⟨0, hψ⟩ ∧ l.state = .compare2 then
      { l with path2 := some ⟨pathLabel, pathBit, ψ, 1⟩ }
    else l
  | .bot => l

def cmpUpdate (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ then { l with state := .congest } else l
  let (l, r) := cmpUpdatePropagate hψ l r
  let l := cmpUpdateSetPath2 hψ l
  (l, r)

/-! ## Algorithm 8: COMPARE_BIT -/

def compareBitUpdateL (hψ : ψ > 0) (l : AgentState ψ) : AgentState ψ :=
  match l.path2, l.path with
  | some p2, .some pathLabel pathBit =>
    if p2.action = 2 ∧ p2.position = 0 then
      { l with path2 := some ⟨pathLabel, pathBit, ψ, 1⟩ }
    else l
  | _, _ => l

def compareBitUpdateR (hψ : ψ > 0) (r : AgentState ψ) : AgentState ψ :=
  match r.path2 with
  | some p2 =>
    if p2.position = 0 then
      let rBitNat := if r.bit then 1 else 0
      if rBitNat > p2.bit then
        { r with path2 := some ⟨0, 0, 0, 3⟩ }
      else if rBitNat < p2.bit then
        { r with path2 := some ⟨0, 0, 0, 4⟩ }
      else
        if r.label = ⟨ψ - 1, by omega⟩ then
          { r with path2 := some ⟨0, 0, 0, 3⟩ }
        else
          { r with path2 := some ⟨0, 0, ψ - 1, 2⟩ }
    else r
  | none => r

def compareBit (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r := compareBitUpdateR hψ r
  let l := compareBitUpdateL hψ l
  (l, r)

/-! ## Algorithm 6: COMPARE -/

def compareSigInit (l : AgentState ψ) : AgentState ψ :=
  match l.path with
  | .bot => { l with state := .none }
  | .some _ _ => l

def compareSigDispatch (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match l.path2, r.path2 with
  | some _, _ => compareBit hψ l r
  | _, some _ => compareBit hψ l r
  | _, _ => (l, r)

def compareSig (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let (l, r) := cmpUpdate hψ l r
      compareSigDispatch hψ l r
    | .bot => (l, r)

/-! ## Algorithm 10: SIGMOVE -/

def sigMoveStep1 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some pathLabel _, .bot =>
    if l.state ≠ MainState.lock ∧ l.state ≠ MainState.compare1 ∧ l.state ≠ MainState.CHECK_ready then
      if r.state ≠ MainState.produce ∨ pathLabel ≠ ψ - 1 then
        ({ l with path := .bot, state := .none }, { r with path := l.path })
      else (l, r)
    else (l, r)
  | _, _ => (l, r)

def sigMoveApplyControl (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ := match u.path2 with
  | some p2 =>
    let u := if u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ (p2.action = 3 ∨ p2.action = 4) then
      { u with state := MainState.eliminate_signal } else u
    let u := if u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ p2.action = 5 then
      { u with state := MainState.depart } else u
    if u.label = (⟨0, hψ⟩ : Fin ψ) ∧ p2.action = 6 then
      { u with state := MainState.toss } else u
  | none => u

def sigMoveStep2 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path2 with
  | some p2 =>
    if p2.action = 1 ∧ p2.position ≠ 0 then
      ({ l with path2 := none },
       { r with path2 := some { p2 with position := p2.position - 1 } })
    else (l, r)
  | none => (l, r)

def sigMoveStep3 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match r.path2 with
  | some p2 =>
    if p2.action = 2 ∧ p2.position ≠ 0 then
      ({ l with path2 := some { p2 with position := p2.position - 1 } },
       { r with path2 := none })
    else (l, r)
  | none => (l, r)

def sigMoveStep4 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match r.path2 with
  | some p2 =>
    if p2.action = 3 ∨ p2.action = 6 then
      ({ l with path2 := r.path2 }, { r with path2 := none })
    else (l, r)
  | none => (l, r)

def sigMoveStep5 (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path2 with
  | some p2 =>
    if p2.action = 4 ∨ p2.action = 5 then
      ({ l with path2 := none }, { r with path2 := l.path2 })
    else (l, r)
  | none => (l, r)

def sigMove (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := sigMoveStep1 l r
  let (l, r) := sigMoveStep2 l r
  let (l, r) := sigMoveStep3 l r
  let (l, r) := sigMoveStep4 l r
  let (l, r) := sigMoveStep5 l r
  let l := sigMoveApplyControl hψ l
  let r := sigMoveApplyControl hψ r
  let l := if r.state = MainState.depart then
    if l.label.val < ψ - 1 ∧ l.state = MainState.CHECK_ready then
      { l with state := MainState.depart }
    else l
  else l
  (l, r)

/-! ## Algorithm 14: SUPPRESS_SIG -/

/-- Leader reset-command generation stage of Algorithm 14. -/
def suppressSigStart (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (if l.leader = true then { l with reset_cmd := true } else l, r)

/-- Reset-command movement stage of Algorithm 14. -/
def suppressSigMoveReset (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.reset_cmd = true then
    ({ l with reset_cmd := false }, { r with reset_cmd := true })
  else (l, r)

/-- Terminal count reset and echo generation stage of Algorithm 14. -/
def suppressSigTerminal (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.reset_cmd = true then
    ({ l with echo := true }, { r with count := 0 })
  else (l, r)

/-- Echo/reset cancellation and movement stage of Algorithm 14. -/
def suppressSigEcho (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.echo = true then
    if r.reset_cmd = true then
      (l, { r with echo := false, reset_cmd := false })
    else
      ({ l with echo := true }, { r with echo := false })
  else (l, r)

/-- Leader echo-consumption stage of Algorithm 14. -/
def suppressSigFinish (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (if l.leader = true then { l with echo := false } else l, r)

/-- Staged form of Algorithm 14 used for compositional proofs. -/
def suppressSigStaged (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := suppressSigStart l r
  let q := suppressSigMoveReset q.1 q.2
  let q := suppressSigTerminal hψ q.1 q.2
  let q := suppressSigEcho q.1 q.2
  suppressSigFinish q.1 q.2

/-- Algorithm 14 in the literal assignment order. -/
def suppressSig (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.leader = true then { l with reset_cmd := true } else l
  let (l, r) := if l.reset_cmd = true then
    ({ l with reset_cmd := false }, { r with reset_cmd := true })
  else (l, r)
  let (l, r) :=
    if r.label = ⟨ψ - 1, by omega⟩ ∧ r.reset_cmd = true then
      ({ l with echo := true }, { r with count := 0 })
    else (l, r)
  let (l, r) := if r.echo = true then
    if r.reset_cmd = true then
      (l, { r with echo := false, reset_cmd := false })
    else
      ({ l with echo := true }, { r with echo := false })
  else (l, r)
  let l := if l.leader = true then { l with echo := false } else l
  (l, r)

/-- The staged proof form is definitionally the same transition. -/
theorem suppressSig_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    suppressSig hψ l r = suppressSigStaged hψ l r := by
  rfl

/-! ## Algorithm 15: EliminateLeaders' -/

def eliminateLeaders (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.leader = true ∧ l.signal_B = ⟨1, by omega⟩ then
    { l with bullet := ⟨2, by omega⟩, shield := true,
             signal_B := ⟨0, by omega⟩ }
  else l
  let r := if r.leader = true ∧ r.signal_B = ⟨1, by omega⟩ then
    { r with bullet := ⟨1, by omega⟩, shield := false,
             signal_B := ⟨0, by omega⟩ }
  else r
  let (l, r) :=
    if r.bullet.val > 0 ∧ l.leader = true then
      if r.bullet = ⟨2, by omega⟩ ∧ l.shield = false then
        ({ l with leader := false }, { r with bullet := ⟨1, by omega⟩ })
      else (l, r)
    else if r.bullet.val > 0 ∧ l.leader = false then
      if r.label = nextLabel then
        ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ },
         { r with bullet := ⟨0, by omega⟩ })
      else
        (l, { r with bullet := ⟨0, by omega⟩ })
    else (l, r)
  let r := if r.label = nextLabel ∨ l.leader = true then
    let leaderVal : Fin 2 :=
      if l.leader = true then ⟨1, by omega⟩ else ⟨0, by omega⟩
    { r with signal_B := finMax (finMax l.signal_B r.signal_B) leaderVal }
  else r
  (l, r)

/-! ## Algorithm 17: GROUP_INFO -/

/-- Leader-relative marker generation at the start of Algorithm 17. -/
def groupInfoStart (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if r.leader = true then
    if r.label ≠ nextLabel then { l with last_set := true }
    else { l with last_unset := true }
  else l
  (l, r)

/-- `last_set` movement stage of Algorithm 17. -/
def groupInfoSet (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r.last_set = true then
    let r := { r with last := true }
    if l.label ≠ ⟨ψ - 1, by omega⟩ then
      ({ l with last_set := true }, { r with last_set := false })
    else
      ({ l with last_unset := true }, { r with last_set := false })
  else (l, r)

/-- `last_unset` movement stage of Algorithm 17. -/
def groupInfoUnset (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.last_unset = true then
    let r := { r with last := false, last_unset := false }
    if l.leader ≠ true then
      ({ l with last_unset := true }, r)
    else (l, r)
  else (l, r)

def groupInfoStaged (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := groupInfoStart hψ l r
  let q := groupInfoSet hψ q.1 q.2
  groupInfoUnset q.1 q.2

def groupInfo (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if r.leader = true then
    if r.label ≠ nextLabel then { l with last_set := true }
    else { l with last_unset := true }
  else l
  -- Algorithm 17 does not print `r.last_set ← 0`; propagation is interpreted
  -- as moving (rather than copying forever) the control token.
  let (l, r) := if r.last_set = true then
    let r := { r with last := true }
    if l.label ≠ ⟨ψ - 1, by omega⟩ then
      ({ l with last_set := true }, { r with last_set := false })
    else
      ({ l with last_unset := true }, { r with last_set := false })
  else (l, r)
  let (l, r) := if r.last_unset = true then
    let r := { r with last := false, last_unset := false }
    if l.leader ≠ true then
      ({ l with last_unset := true }, r)
    else (l, r)
  else (l, r)
  (l, r)

theorem groupInfo_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    groupInfo hψ l r = groupInfoStaged hψ l r := by
  rfl

/-! ## Algorithm 18: GENSIG_WRITESEQ -/

/-- Production-state initialization stage of Algorithm 18. -/
def gensigWriteseqStart (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ l.gen_ws = true ∧ l.path3 = none then
    { l with write_state := .produce }
  else l
  let r := if r.label ≠ ⟨0, hψ⟩ ∧ l.write_state = .produce ∧ r.path3 = none then
    { r with write_state := .produce }
  else r
  (l, r)

/-- Terminal overwriting-path emission and bit-carry stage. -/
def gensigWriteseqEmit (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r := if r.label = ⟨ψ - 1, by omega⟩ ∧ r.write_state = .produce then
    let p3 : Path3Info := ⟨r.label.val, if r.bit then 1 else 0, 1⟩
    let r := { r with write_state := .done, path3 := some p3 }
    let r := if r.bit = true then { r with b_carry := true } else r
    { r with bit := !r.bit }
  else r
  (l, r)

/-- Backward overwriting-path propagation and carry stage. -/
def gensigWriteseqPropagate (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.write_state = .produce ∧
       r.write_state = .done then
    let p3 : Path3Info := ⟨l.label.val, if l.bit then 1 else 0, 1⟩
    let l := { l with write_state := .done, path3 := some p3 }
    let (l, r) := if r.b_carry = true then
      let l := if l.bit = true then { l with b_carry := true } else l
      ({ l with bit := !l.bit }, { r with b_carry := false })
    else (l, r)
    (l, { r with write_state := .depart })
  else (l, r)

/-- Source departure stage of Algorithm 18. -/
def gensigWriteseqFinish (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ l.write_state = .done then
    { l with write_state := .depart, gen_ws := false }
  else l
  (l, r)

def gensigWriteseqStaged (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := gensigWriteseqStart hψ l r
  let q := gensigWriteseqEmit hψ q.1 q.2
  let q := gensigWriteseqPropagate hψ q.1 q.2
  gensigWriteseqFinish hψ q.1 q.2

def gensigWriteseq (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ l.gen_ws = true ∧ l.path3 = none then
    { l with write_state := .produce }
  else l
  let r := if r.label ≠ ⟨0, hψ⟩ ∧ l.write_state = .produce ∧ r.path3 = none then
    { r with write_state := .produce }
  else r
  let r := if r.label = ⟨ψ - 1, by omega⟩ ∧ r.write_state = .produce then
    let p3 : Path3Info := ⟨r.label.val, if r.bit then 1 else 0, 1⟩
    let r := { r with write_state := .done, path3 := some p3 }
    let r := if r.bit = true then { r with b_carry := true } else r
    { r with bit := !r.bit }
  else r
  let (l, r) :=
    if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.write_state = .produce ∧
       r.write_state = .done then
      let p3 : Path3Info := ⟨l.label.val, if l.bit then 1 else 0, 1⟩
      let l := { l with write_state := .done, path3 := some p3 }
      let (l, r) := if r.b_carry = true then
        let l := if l.bit = true then { l with b_carry := true } else l
        ({ l with bit := !l.bit }, { r with b_carry := false })
      else (l, r)
      (l, { r with write_state := .depart })
    else (l, r)
  let l := if l.label = ⟨0, hψ⟩ ∧ l.write_state = .done then
    { l with write_state := .depart, gen_ws := false }
  else l
  (l, r)

theorem gensigWriteseq_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    gensigWriteseq hψ l r = gensigWriteseqStaged hψ l r := by
  rfl

/-! ## Algorithm 19: WRITE_ACTION -/

def writeActionApplyOverwrite (r : AgentState ψ) : AgentState ψ :=
  match r.path3 with
  | some p3 =>
    { r with bit := (p3.bit == 1),
             path3 := some { p3 with flag := 1 - p3.flag } }
  | none => r

def writeActionApplyMoveFlip (r : AgentState ψ) : AgentState ψ :=
  match r.path3 with
  | some p3 =>
    { r with path3 := some { p3 with flag := 1 - p3.flag } }
  | none => r

/-- Terminal write-command activation factored from Algorithm 19. -/
def writeActionActivate (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ :=
  if u.label = ⟨ψ - 1, by omega⟩ then
    { u with write_state := writeActionToState u.write, write := .none }
  else u

/-- Action execution/propagation after both local activations. -/
def writeActionExecute (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if l.label < r.label ∨ r.label = ⟨0, hψ⟩ then
    let r := if r.write_state = .overwrite then
      writeActionApplyOverwrite r
    else r
    let r := if r.write_state = .move_flip then
      writeActionApplyMoveFlip r
    else r
    let r := if r.write_state = .increment_group then
      if r.bit = true then { r with bit := false }
      else { r with bit := true, write_state := .depart }
    else r
    let l := if r.label ≠ ⟨0, hψ⟩ then { l with write_state := r.write_state } else l
    (l, { r with write_state := .depart })
  else (l, r)

def writeActionStaged (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  writeActionExecute hψ (writeActionActivate hψ l) (writeActionActivate hψ r)

def writeAction (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let activate (u : AgentState ψ) : AgentState ψ :=
    if u.label = ⟨ψ - 1, by omega⟩ then
      { u with write_state := writeActionToState u.write, write := .none }
    else u
  let l := activate l
  let r := activate r
  let (l, r) := if l.label < r.label ∨ r.label = ⟨0, hψ⟩ then
    let r := if r.write_state = .overwrite then
      writeActionApplyOverwrite r
    else r
    let r := if r.write_state = .move_flip then
      writeActionApplyMoveFlip r
    else r
    let r := if r.write_state = .increment_group then
      -- Binary increment carries through a 1 and stops only after flipping a 0.
      if r.bit = true then { r with bit := false }
      else { r with bit := true, write_state := .depart }
    else r
    let l := if r.label ≠ ⟨0, hψ⟩ then { l with write_state := r.write_state } else l
    (l, { r with write_state := .depart })
  else (l, r)
  (l, r)

theorem writeAction_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    writeAction hψ l r = writeActionStaged hψ l r := by
  rfl

/-! ## Algorithm 20: MOVE_WSIG -/

def moveWsigTransfer (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path3, r.path3 with
  | some _, none =>
    if l.write_state = WriteState.depart then
      if r.ws_echo = false then
        let r := { r with path3 := l.path3, write_state := l.write_state }
        let l := { l with path3 := none, write_state := .none, write := .none }
        -- Printed line 17 says `l.label = 1`; `last` is the control field
        -- generated by GROUP_INFO and is the likely intended guard. This
        -- non-literal correction still requires author confirmation.
        let l := if l.last = true ∧ l.leader ≠ true then
          { l with ws_echo := true } else l
        (l, r)
      else
        ({ l with path3 := none, write := .none, write_state := .none }, r)
    else (l, r)
  | _, _ => (l, r)

def moveWsigCheckGenWs (l r : AgentState ψ) : AgentState ψ :=
  match l.path3 with
  | some p3 => if p3.label = 0 then { r with gen_ws := true } else r
  | none => r

/-- Algorithm 20 line 7 prints assignment `l.last ← 1` inside a guard.
We interpret it as the equality test `l.last = 1`. -/
def moveWsigCheckLast (l : AgentState ψ) : AgentState ψ :=
  match l.path3 with
  | some p3 =>
    if l.label.val = p3.label ∧ l.last = true then
      { l with path3 := none, write := .none, write_state := .none }
    else l
  | none => l

/-- Leader-consumption stage at the start of Algorithm 20. -/
def moveWsigStart (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.leader = true then
    let r := moveWsigCheckGenWs l r
    ({ l with path3 := none, write := .none, write_state := .none }, r)
  else (l, r)

/-- Write-token movement after path3 transfer in Algorithm 20. -/
def moveWsigMoveWrite (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.label < r.label then
    ({ l with write := .none }, { r with write := l.write })
  else (l, r)

/-- Leader signal_ws generation after path3 transfer. -/
def moveWsigLeaderSignal (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (if r.leader = true then { l with signal_ws := true } else l, r)

/-- signal_ws movement stage of Algorithm 20. -/
def moveWsigSignalMove (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.signal_ws = true then
    let l := if l.leader = true then { l with gen_ws := true }
             else { l with signal_ws := true }
    (l, { r with signal_ws := false })
  else (l, r)

/-- ws_echo movement/cancellation stage of Algorithm 20. -/
def moveWsigEchoMove (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.ws_echo = true then
    if l.leader = true then
      (l, { r with ws_echo := false })
    else
      ({ l with ws_echo := true }, { r with ws_echo := false })
  else (l, r)

/-- Algorithm-20 tail after path3 transfer; it changes no bounded raw payload. -/
def moveWsigFinish (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := moveWsigMoveWrite l r
  let q := moveWsigLeaderSignal q.1 q.2
  let q := moveWsigSignalMove q.1 q.2
  moveWsigEchoMove q.1 q.2

def moveWsigStaged (_hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := moveWsigStart l r
  let l := moveWsigCheckLast q.1
  let q := moveWsigTransfer l q.2
  moveWsigFinish q.1 q.2

def moveWsig (_hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := if r.leader = true then
    let r := moveWsigCheckGenWs l r
    ({ l with path3 := none, write := .none, write_state := .none }, r)
  else (l, r)
  let l := moveWsigCheckLast l
  let (l, r) := moveWsigTransfer l r
  let (l, r) := if l.label < r.label then
    ({ l with write := .none }, { r with write := l.write })
  else (l, r)
  let l := if r.leader = true then { l with signal_ws := true } else l
  let (l, r) := if r.signal_ws = true then
    let l := if l.leader = true then { l with gen_ws := true }
             else { l with signal_ws := true }
    (l, { r with signal_ws := false })
  else (l, r)
  let (l, r) := if r.ws_echo = true then
    if l.leader = true then
      (l, { r with ws_echo := false })
    else
      ({ l with ws_echo := true }, { r with ws_echo := false })
  else (l, r)
  (l, r)

theorem moveWsig_eq_staged (hψ : ψ > 0) (l r : AgentState ψ) :
    moveWsig hψ l r = moveWsigStaged hψ l r := by
  rfl

/-! ## Algorithm 16: WRITE_SEQ -/

def writeSeqSetWriteReady (u : AgentState ψ) : AgentState ψ :=
  match u.path3 with
  | some p3 =>
    if u.label.val = p3.label ∧ u.write_state ≠ .depart then
      { u with write_state := .ready }
    else { u with write_state := .none }
  | none => { u with write_state := .none }

def writeSeqCheckBit (r : AgentState ψ) : AgentState ψ :=
  match r.path3 with
  | some p3 => { r with write_state := checkBitWS r.bit p3.bit }
  | none => r

def writeSeqSetWriteAct (u : AgentState ψ) : AgentState ψ :=
  let u := if u.write_state = .larger then
    match u.path3 with
    | some p3 =>
      if p3.flag = 1 then { u with write := .overwrite }
      else { u with write := .move_flip }
    | none => u
  else u
  if u.write_state = .less then { u with write := .move } else u

def writeSeqFinalR (r : AgentState ψ) : AgentState ψ :=
  match r.path3 with
  | some p3 =>
    if p3.flag = 1 then { r with write := .move_flip }
    else { r with write := .increment_group }
  | none => r

/-- Responder-leader migration prefix of Algorithm 16. -/
def writeSeqLeaderMove (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r.leader = true ∧ r.label ≠ ⟨0, hψ⟩ then
    ({ l with leader := true }, { r with leader := false })
  else (l, r)

/-- Conditional Algorithm-18 call factored from Algorithm 16. -/
def writeSeqGenerate (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if l.leader = true ∧ l.gen_ws = true then
    gensigWriteseq hψ l r
  else (l, r)

/-- Local ready-state setup in Algorithm 16. -/
def writeSeqReady (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (writeSeqSetWriteReady l, writeSeqSetWriteReady r)

/-- Bit comparison portion of Algorithm 16. -/
def writeSeqCompare (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r := if r.label = ⟨0, hψ⟩ ∧ r.write_state = .ready then
    writeSeqCheckBit r
  else r
  let r := if l.label.val < ψ - 1 ∧ l.write_state = .equal ∧
              r.write_state = .ready then
    writeSeqCheckBit r
  else r
  (l, r)

/-- Write-command selection portion of Algorithm 16. -/
def writeSeqCommands (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := writeSeqSetWriteAct l
  let r := writeSeqSetWriteAct r
  let r := if r.label = ⟨ψ - 1, by omega⟩ ∧ r.write_state = .equal then
    writeSeqFinalR r
  else r
  (l, r)

/-- CHECK/command-preparation portion of Algorithm 16, before Algorithm 19. -/
def writeSeqPrepare (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := writeSeqReady l r
  let q := writeSeqCompare hψ q.1 q.2
  writeSeqCommands hψ q.1 q.2

/-- Algorithm-16 prefix through command preparation. Factoring this exact
stage boundary prevents later frame proofs from unfolding Algorithms 17–20 as
one enormous term; it does not change the printed call order. -/
def writeSeqThroughPrepare (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := writeSeqLeaderMove hψ l r
  let q := groupInfo hψ q.1 q.2
  let q := writeSeqGenerate hψ q.1 q.2
  writeSeqPrepare hψ q.1 q.2

/-- Algorithm-16 suffix: execute the prepared write and move its signal. -/
def writeSeqAfterPrepare (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := writeAction hψ l r
  moveWsig hψ q.1 q.2

/-- Exact Algorithm-16 composition at the factored prefix/suffix boundary. -/
def writeSeq (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := writeSeqThroughPrepare hψ l r
  writeSeqAfterPrepare hψ q.1 q.2

/-- Expose the exact factored Algorithm-16 boundary without unfolding either
large side at downstream call sites. -/
theorem writeSeq_eq_afterPrepare (hψ : ψ > 0) (l r : AgentState ψ) :
    writeSeq hψ l r = writeSeqAfterPrepare hψ
      (writeSeqThroughPrepare hψ l r).1
      (writeSeqThroughPrepare hψ l r).2 := by
  rfl

/-! ## Algorithm 1: P_PLL — Top-Level Composition -/

/-- Algorithm-1 prefix immediately before CHECK. This named boundary is
extensionally just the first five printed calls and supports the concrete
leader-creation audit. -/
def ppllBeforeCheck (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := pPsi hψ l r
  let (l, r) := genSig hψ κ l r
  let (l, r) := cleanSig hψ l r
  let (l, r) := eliminateSig hψ l r
  sigMove hψ l r

/-- Algorithm-1 boundary immediately after CHECK. -/
def ppllAfterCheck (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := ppllBeforeCheck hψ κ l r
  checkSig hψ q.1 q.2

/-- Algorithm-1 boundary immediately before EliminateLeaders'. -/
def ppllBeforeEliminateLeaders (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let (l, r) := ppllAfterCheck hψ κ l r
  let (l, r) := disappear hψ l r
  let (l, r) := compareSig hψ l r
  suppressSig hψ l r

/-- Algorithm-1 boundary immediately before WRITE_SEQ. -/
def ppllBeforeWriteSeq (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := ppllBeforeEliminateLeaders hψ κ l r
  eliminateLeaders hψ q.1 q.2

/-- The complete Algorithm-1 transition, factored only at named audit
boundaries; call order is unchanged. -/
def ppll (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := ppllBeforeWriteSeq hψ κ l r
  writeSeq hψ q.1 q.2

/-- Concrete population-protocol package for P_PLL. Correctness properties are
proved separately; constructing this record makes no closedness claim. -/
def protocol (hψ : ψ > 0) (κ : Nat) : PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := ppll hψ κ
  output := AgentState.outputFn

end PPLL
