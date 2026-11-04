import Leader.Wu.Protocol.Repairs
import Leader.Wu.Birth.ClosedLeaderlessRingTwo
import Leader.Wu.Birth.LeaderlessEscapeJamProjection

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAll8

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by decide

/-- The jam guard: a departing, waiting cell whose two auxiliary path fields
are both absent — this is the jam shape, not the original witness shape. -/
def jamGuard {ψ : Nat} (u : AgentState ψ) : Bool :=
  decide (u.state = MainState.depart) && u.wait && u.path4.isNone && u.path5.isNone

/-- Repair 4: when the XOR guard is false (both auxiliary paths are in the same
presence state), rebuild both to the CLEAN mark `some (-1, 1)`; when it is true
(clean-like cells) leave the cell untouched. -/
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


def cmpUpdateGuardedR7 {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ (l.state ≠ .depart ∨ l.leader = false) ∧
      l.state ≠ .CHECK_ready ∧ l.state ≠ .equal ∧
      l.state ≠ .larger ∧ l.state ≠ .less then
    { l with state := .congest }
  else l
  let q := cmpUpdatePropagate hψ l r
  (cmpUpdateSetPath2 hψ q.1, q.2)

def compareSigGuardedR7 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let q := cmpUpdateGuardedR7 hψ l r
      compareSigDispatch hψ q.1 q.2
    | .bot => (l, r)


/-- Fifth repair: `cleanSigGenConnect` with the two auxiliary writes swapped so
that the mark lands on the CLEAN side of the cell (site0: path5, site1: path4). -/
def cleanSigGenConnectSwap {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  match u.path with
  | .some pathLabel _ =>
    let u := if pathLabel ≠ ψ - 1 then
      { u with path4 := some (Int.ofNat pathLabel, 1) } else u
    if pathLabel ≠ 0 then
      { u with path5 := some (Int.ofNat pathLabel, 1) } else u
  | .bot => u

/-- Sixth repair: the `.bot` branch plants an asymmetric seed (only `path5`)
so that the XOR of the two auxiliary path fields becomes true. -/
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

def ppllSaturatedBeforeCheckAll5R7 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := (fixCell l, fixCell r)
  let q := pPsi hψ q.1 q.2
  let q := genSigRepairedA hψ κ q.1 q.2
  let q := cleanSig7 hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  sigMove hψ q.1 q.2

def ppllIntegratedBeforeSuppressAll5R7 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheckAll5R7 hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  compareSigGuardedR7 hψ q.1 q.2

def ppllIntegratedRepairAll5R7 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllIntegratedBeforeSuppressAll5R7 hψ κ l r
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

def protocolAll9R7 : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ppllIntegratedRepairAll5R7 hψ2 2
  output := AgentState.outputFn

private def ring2 : DirectedRing 2 := ⟨by decide⟩

def C : protocolAll9R7.Configuration 2 := fun _ => BoundedAgentState.erase (Q16405.s)


namespace ZZRepairAll8

open ZZRepairAllProj

theorem witness_escapes6 :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 2, ∃ i : Fin 2,
      ((protocolAll9R7.step ring2
        (protocolAll9R7.step ring2
          (protocolAll9R7.step ring2
            (protocolAll9R7.step ring2
              (protocolAll9R7.step ring2
                (protocolAll9R7.step ring2
                  (protocolAll9R7.step ring2
                    (protocolAll9R7.step ring2 C e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

theorem jam_escapes6 :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 2, ∃ i : Fin 2,
      ((protocolAll9R7.step ring2
        (protocolAll9R7.step ring2
          (protocolAll9R7.step ring2
            (protocolAll9R7.step ring2
              (protocolAll9R7.step ring2
                (protocolAll9R7.step ring2
                  (protocolAll9R7.step ring2
                    (protocolAll9R7.step ring2
                      (fun j => BoundedAgentState.erase (ZZRepairAllProj.jamCfg j)) e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

#print axioms ZZRepairAll8.witness_escapes6
#print axioms ZZRepairAll8.jam_escapes6

end ZZRepairAll8

namespace ZZRepairAll8

open ZZRepairAllProj

/-- The two trap cells (the fourth repair misses them). -/
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

def trapCfg : protocolAll9R7.Configuration 2 :=
  fun i => if i = (0 : Fin 2) then trap0 else trap1

theorem witness_escapes7 :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 2, ∃ i : Fin 2,
      ((protocolAll9R7.step ring2
        (protocolAll9R7.step ring2 (protocolAll9R7.step ring2 (protocolAll9R7.step ring2
          (protocolAll9R7.step ring2 (protocolAll9R7.step ring2 (protocolAll9R7.step ring2
            (protocolAll9R7.step ring2 C e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

theorem jam_escapes7 :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 2, ∃ i : Fin 2,
      ((protocolAll9R7.step ring2
        (protocolAll9R7.step ring2 (protocolAll9R7.step ring2 (protocolAll9R7.step ring2
          (protocolAll9R7.step ring2 (protocolAll9R7.step ring2 (protocolAll9R7.step ring2
            (protocolAll9R7.step ring2
              (fun j => BoundedAgentState.erase (ZZRepairAllProj.jamCfg j)) e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

theorem trap_escapes7 :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 2, ∃ i : Fin 2,
      ((protocolAll9R7.step ring2
        (protocolAll9R7.step ring2 (protocolAll9R7.step ring2 (protocolAll9R7.step ring2
          (protocolAll9R7.step ring2 (protocolAll9R7.step ring2 (protocolAll9R7.step ring2
            (protocolAll9R7.step ring2 trapCfg e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

#print axioms ZZRepairAll8.witness_escapes7
#print axioms ZZRepairAll8.jam_escapes7
#print axioms ZZRepairAll8.trap_escapes7

end ZZRepairAll8

namespace ZZRepairAll8

open ZZRepairAllProj

/-- The first stuck configuration of the widened batch (state = .depart,
wait = true, path = .bot, all auxiliary paths absent, label 0). -/
def stuck0 : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false, state := MainState.depart, wait := true,
      label := (0 : Fin 2), path := PathInfo.bot,
      path2 := none, path3 := none, path4 := none, path5 := none }

def stuck0Cfg : protocolAll9R7.Configuration 2 := fun _ => stuck0
/-! ## R7: poison and regressions under the strengthened guard -/

def jamCfg : protocolAll9R7.Configuration 2 :=
  fun j => BoundedAgentState.erase (ZZRepairAllProj.jamCfg j)

def poison : Path2Info :=
  ⟨0, 0, 1, 5⟩

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

def poisonCfg : protocolAll9R7.Configuration 2 :=
  fun i => poisonCell i

def hasLeader (C : protocolAll9R7.Configuration 2) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

def escapesAux : Nat → protocolAll9R7.Configuration 2 → Bool
  | 0, C => hasLeader C
  | k + 1, C =>
      hasLeader C ||
      escapesAux k (protocolAll9R7.step ring2 C (0 : Fin 2)) ||
      escapesAux k (protocolAll9R7.step ring2 C (1 : Fin 2))


theorem poison_stays_r7 :
    escapesAux 8 poisonCfg = false := by decide +kernel

#print axioms poison_stays_r7

end ZZRepairAll8
