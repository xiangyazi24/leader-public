import Leader.Wu.Birth.LeaderlessEscapePoisonStuck


set_option autoImplicit false
set_option Elab.async false


namespace ZZRepairAll9W


open PPLL PPLLRepair


private theorem hψ2 : 0 < 2 := by
  decide


private def ring2 : DirectedRing 2 :=
  ⟨by decide⟩


/-- All8's genSigRepairedA, with exactly one wiring change:
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


def ppllIntegratedBeforeSuppressAll5W {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheckAll5W hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  ZZRepairAll8.compareSigGuarded hψ q.1 q.2


def ppllIntegratedRepairAll5W {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllIntegratedBeforeSuppressAll5W hψ κ l r
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2


def protocolAll9W : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ppllIntegratedRepairAll5W hψ2 2
  output := AgentState.outputFn


private abbrev RawCfg := protocolAll9W.Configuration 2


/-- Poison, reused literally from ZZPoison5All8. -/
def poisonCfg9W : RawCfg :=
  fun i => ZZPoison5All8.poisonCell i


/-- Exact release5 token shape from Leader/Wu/Birth/LeaderlessEscapeReleaseTokenStuck.lean. -/
def release5Token9W : Path2Info :=
  { label := 0
    bit := 0
    position := 1
    action := 5 }


/-- Exact release5 cell shape, restated locally to keep one import. -/
def release5Cell9W (lab : Fin 2) : AgentState 2 :=
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
    path2 := some release5Token9W
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
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


def release5Cfg9W : RawCfg :=
  fun i => release5Cell9W i


def hasLeaderBool (C : RawCfg) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader


def escapesAux : Nat → RawCfg → Bool
  | 0, C => hasLeaderBool C
  | fuel + 1, C =>
      hasLeaderBool C ||
      escapesAux fuel
        (protocolAll9W.step ring2 C (0 : Fin 2)) ||
      escapesAux fuel
        (protocolAll9W.step ring2 C (1 : Fin 2))


theorem poison_no_escape8_9w :
    escapesAux 8 poisonCfg9W = false := by
  decide +kernel


theorem release5_no_escape8_9w :
    escapesAux 8 release5Cfg9W = false := by
  decide +kernel


#print axioms ZZRepairAll9W.poison_no_escape8_9w
#print axioms ZZRepairAll9W.release5_no_escape8_9w


end ZZRepairAll9W
