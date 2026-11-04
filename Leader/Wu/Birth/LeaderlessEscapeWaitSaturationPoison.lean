import Leader.Wu.Birth.LeaderlessEscapePoisonStuck

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAll9W

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by
  decide

private def ring2 : DirectedRing 2 :=
  ⟨by decide⟩

/-- All8's `genSigRepairedA`, with exactly one wiring change:
use the already-existing saturating WAIT candidate. -/
def genSigRepairedAW {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let (l, r) := waitSaturated hψ κ l r
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
      { r with
          state := .done
          path := .some r.label.val (if r.bit then 1 else 0) }
    else r
  let (l, r) :=
    if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.state = .produce ∧
       r.state = .done then
      ({ l with
          state := .done
          path := .some l.label.val (if l.bit then 1 else 0) },
       { r with state := .depart })
    else (l, r)
  let l :=
    if l.label = ⟨0, hψ⟩ ∧ l.state = .done then
      { l with state := .depart, wait := true }
    else l
  (l, r)

/-- All8 before-CHECK wiring, changing only the GENSIG helper above. -/
def ppllSaturatedBeforeCheckAll5W {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := (ZZRepairAll8.fixCell l, ZZRepairAll8.fixCell r)
  let q := pPsi hψ q.1 q.2
  let q := genSigRepairedAW hψ κ q.1 q.2
  let q := ZZRepairAll8.cleanSig7 hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  sigMove hψ q.1 q.2

def ppllIntegratedBeforeSuppressAll5W {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheckAll5W hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  ZZRepairAll8.compareSigGuarded hψ q.1 q.2

def ppllIntegratedRepairAll5W {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllIntegratedBeforeSuppressAll5W hψ κ l r
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

/-- Seventh-version WAIT-wiring candidate: All8 plus only WAIT saturation. -/
def protocolAll9W : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ppllIntegratedRepairAll5W hψ2 2
  output := AgentState.outputFn

def C9W : protocolAll9W.Configuration 2 :=
  fun _ => BoundedAgentState.erase Q16405.s

def jamCfg9W : protocolAll9W.Configuration 2 :=
  fun j => BoundedAgentState.erase (ZZRepairAllProj.jamCfg j)

/-- Same trap pair used by All8, merely retyped for protocolAll9W. -/
def trap0W : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false
      probe := false
      phase := true
      bit := false
      wait := true
      state := .congest
      label := (0 : Fin 2)
      path := .some 1 0
      path2 := none
      path3 := none
      path4 := none
      path5 := none }

def trap1W : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false
      probe := false
      phase := true
      bit := false
      wait := true
      state := .congest
      label := (1 : Fin 2)
      path := .some 0 0
      path2 := none
      path3 := none
      path4 := none
      path5 := none }

def trapCfg9W : protocolAll9W.Configuration 2 :=
  fun i => if i = (0 : Fin 2) then trap0W else trap1W

/-- Same first widened-batch stuck cell used by All8. -/
def stuck0W : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false
      state := .depart
      wait := true
      label := (0 : Fin 2)
      path := PathInfo.bot
      path2 := none
      path3 := none
      path4 := none
      path5 := none }

def stuck0Cfg9W : protocolAll9W.Configuration 2 :=
  fun _ => stuck0W

def poisonCfg9W : protocolAll9W.Configuration 2 :=
  fun i => ZZPoison5All8.poisonCell i

def hasLeaderBool (C : protocolAll9W.Configuration 2) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

def escapesAux : Nat → protocolAll9W.Configuration 2 → Bool
  | 0, C => hasLeaderBool C
  | fuel + 1, C =>
      hasLeaderBool C ||
      escapesAux fuel
        (protocolAll9W.step ring2 C (0 : Fin 2)) ||
      escapesAux fuel
        (protocolAll9W.step ring2 C (1 : Fin 2))

/-- WAIT saturation alone does not free the action-5/position-1 poison by depth 8. -/
theorem poison_escapesAux8_9w :
    escapesAux 8 poisonCfg9W = false := by
  decide +kernel

#print axioms ZZRepairAll9W.poison_escapesAux8_9w

end ZZRepairAll9W
