import Leader.Wu.Protocol.Repairs
import Leader.Wu.Birth.ClosedLeaderlessRingTwo
import Leader.Wu.Birth.LeaderlessEscapeJamProjection

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAll10Consume

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by decide

def jamGuard {ψ : Nat} (u : AgentState ψ) : Bool :=
  decide (u.state = MainState.depart) && u.wait && u.path4.isNone && u.path5.isNone

def fixCell {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if jamGuard u then { u with path4 := some ((-1 : Int), 1), path5 := some ((-1 : Int), 1) } else u

def genSigRepairedA {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := wait hψ κ l r
  let l :=
    if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧
       l.path = .bot then
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

/-! ## Pre-R7 compare guard (ZZRepairAll8 original) -/

def cmpUpdateGuarded {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ (l.state ≠ .depart ∨ l.leader = false) then
    { l with state := .congest }
  else l
  let q := cmpUpdatePropagate hψ l r
  (cmpUpdateSetPath2 hψ q.1, q.2)

def compareSigGuarded {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let q := cmpUpdateGuarded hψ l r
      compareSigDispatch hψ q.1 q.2
    | .bot => (l, r)

/-! ## Consume-on-apply: clear path2 after control action fires -/

def sigMoveApplyControlConsume {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ :=
  match u.path2 with
  | some p2 =>
    let hit1 := u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ (p2.action = 3 ∨ p2.action = 4)
    let hit2 := u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ p2.action = 5
    let hit3 := u.label = (⟨0, hψ⟩ : Fin ψ) ∧ p2.action = 6
    let u := if hit1 then { u with state := MainState.eliminate_signal } else u
    let u := if hit2 then { u with state := MainState.depart } else u
    let u := if hit3 then { u with state := MainState.toss } else u
    if hit1 ∨ hit2 ∨ hit3 then { u with path2 := none } else u
  | none => u

def sigMoveConsume {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := sigMoveStep1 l r
  let (l, r) := sigMoveStep2 l r
  let (l, r) := sigMoveStep3 l r
  let (l, r) := sigMoveStep4 l r
  let (l, r) := sigMoveStep5 l r
  let l := sigMoveApplyControlConsume hψ l
  let r := sigMoveApplyControlConsume hψ r
  let l := if r.state = MainState.depart then
    if l.label.val < ψ - 1 ∧ l.state = MainState.CHECK_ready then
      { l with state := MainState.depart }
    else l
  else l
  (l, r)

/-! ## Clean (same as ZZRepairAll8) -/

def cleanSigGenConnectBot {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  match u.path with
  | .some pathLabel _ =>
    let u := if pathLabel ≠ ψ - 1 then { u with path4 := some (Int.ofNat pathLabel, 1) } else u
    if pathLabel ≠ 0 then { u with path5 := some (Int.ofNat pathLabel, 1) } else u
  | .bot => { u with path5 := some ((-1 : Int), 1) }

def cleanSig7 {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := cleanSigGenConnectBot l
  let r := cleanSigGenConnectBot r
  let (l, r) := cleanSigStep3 l r
  let (l, r) := cleanSigStep4 l r
  let (l, r) := cleanSigStep5 hψ l r
  let (l, r) := cleanSigStep6 hψ l r
  let l := cleanSigCleanApply l
  let r := cleanSigCleanApply r
  (l, r)

/-! ## Full pipeline -/

def ppllSaturatedBeforeCheckAll5Consume {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := (fixCell l, fixCell r)
  let q := pPsi hψ q.1 q.2
  let q := genSigRepairedA hψ κ q.1 q.2
  let q := cleanSig7 hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  sigMoveConsume hψ q.1 q.2

def ppllIntegratedBeforeSuppressAll5Consume {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheckAll5Consume hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  compareSigGuarded hψ q.1 q.2

def ppllIntegratedRepairAll5Consume {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllIntegratedBeforeSuppressAll5Consume hψ κ l r
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

def protocolAll10Consume : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ppllIntegratedRepairAll5Consume hψ2 2
  output := AgentState.outputFn

private def ring2 : DirectedRing 2 := ⟨by decide⟩

/-! ## Test configurations -/

open ZZRepairAllProj

def C : protocolAll10Consume.Configuration 2 := fun _ => BoundedAgentState.erase (Q16405.s)

def poison : Path2Info := ⟨0, 0, 1, 5⟩

def poisonCell (lab : Fin 2) : AgentState 2 :=
  { leader := false
    probe := false
    phase := true
    bit := false
    wait := false
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := lab
    h_field := false
    path2 := some poison
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := ⟨0, by decide⟩
    bullet := ⟨0, by decide⟩
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

def poisonCfg : protocolAll10Consume.Configuration 2 :=
  fun i => poisonCell i

def trap0 : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false, probe := false, phase := true, bit := false, wait := true,
      state := .congest, label := (0 : Fin 2), path := .some 1 0,
      path2 := none, path3 := none, path4 := none, path5 := none }

def trap1 : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false, probe := false, phase := true, bit := false, wait := true,
      state := .congest, label := (1 : Fin 2), path := .some 0 0,
      path2 := none, path3 := none, path4 := none, path5 := none }

def trapCfg : protocolAll10Consume.Configuration 2 :=
  fun i => if i = (0 : Fin 2) then trap0 else trap1

def stuck0 : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false, state := MainState.depart, wait := true,
      label := (0 : Fin 2), path := PathInfo.bot,
      path2 := none, path3 := none, path4 := none, path5 := none }

def stuck0Cfg : protocolAll10Consume.Configuration 2 := fun _ => stuck0

/-! ## Escape helpers -/

def hasLeader (C : protocolAll10Consume.Configuration 2) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

def escapesAux : Nat → protocolAll10Consume.Configuration 2 → Bool
  | 0, C => hasLeader C
  | k + 1, C =>
      hasLeader C ||
      escapesAux k (protocolAll10Consume.step ring2 C (0 : Fin 2)) ||
      escapesAux k (protocolAll10Consume.step ring2 C (1 : Fin 2))

/-! ## K1: poison escapes at depth 2 under consume -/

theorem poison_escapes_consume :
    escapesAux 2 poisonCfg = true := by decide +kernel

#print axioms poison_escapes_consume

/-! ## K2: leader at position 0 after two (edge 0, edge 0) steps -/

theorem poison_leader_step2 :
    ((protocolAll10Consume.step ring2
      (protocolAll10Consume.step ring2 poisonCfg (0 : Fin 2)) (0 : Fin 2)) (0 : Fin 2)).leader = true := by
  decide +kernel

#print axioms poison_leader_step2

/-! ## K3/K4: regression — witness, jam, trap, stuck0 still escape at depth 8 -/

theorem witness_escapes8 :
    escapesAux 8 C = true := by decide +kernel

theorem jam_escapes8 :
    escapesAux 8 (fun j => BoundedAgentState.erase (ZZRepairAllProj.jamCfg j)) = true := by
  decide +kernel

theorem trap_escapes8 :
    escapesAux 8 trapCfg = true := by decide +kernel

theorem stuck0_escapes8 :
    escapesAux 8 stuck0Cfg = true := by decide +kernel

#print axioms witness_escapes8
#print axioms jam_escapes8
#print axioms trap_escapes8
#print axioms stuck0_escapes8

end ZZRepairAll10Consume
