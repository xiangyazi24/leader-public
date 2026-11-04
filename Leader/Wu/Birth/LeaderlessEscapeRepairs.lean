import Leader.Wu.Protocol.Repairs
import Leader.Wu.Birth.ClosedLeaderlessRingTwo

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAll

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by decide

/-- Repair 2: clear wait when path = .bot. -/
def clearWaitBot {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if u.path = PathInfo.bot then { u with wait := false } else u

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

def ppllSaturatedBeforeCheckAll {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsi hψ l r
  let q := (clearWaitBot q.1, clearWaitBot q.2)
  let q := genSigRepairedA hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  sigMove hψ q.1 q.2

def ppllIntegratedBeforeSuppressAll {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheckAll hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  compareSigGuarded hψ q.1 q.2

def ppllIntegratedRepairAll {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllIntegratedBeforeSuppressAll hψ κ l r
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

def protocolAll : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ppllIntegratedRepairAll hψ2 2
  output := AgentState.outputFn

private def ring2 : DirectedRing 2 := ⟨by decide⟩

def C : protocolAll.Configuration 2 := fun _ => BoundedAgentState.erase (Q16405.s)

theorem witness_escapes :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 2, ∃ i : Fin 2,
      ((protocolAll.step ring2
        (protocolAll.step ring2
          (protocolAll.step ring2
            (protocolAll.step ring2
              (protocolAll.step ring2
                (protocolAll.step ring2
                  (protocolAll.step ring2
                    (protocolAll.step ring2 C e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

def leaderDeparting : AgentState 2 :=
  { BoundedAgentState.erase (Q16405.s) with
      leader := true, state := MainState.depart, label := (0 : Fin 2),
      path := PathInfo.some 0 0 }

theorem leader_depart_not_recongested :
    (cmpUpdateGuarded hψ2 leaderDeparting leaderDeparting).1.state = MainState.depart := by
  decide +kernel

#print axioms ZZRepairAll.witness_escapes
#print axioms ZZRepairAll.leader_depart_not_recongested

end ZZRepairAll
