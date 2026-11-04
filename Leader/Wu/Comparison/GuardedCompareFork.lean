import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZC5bForkLayer

open PPLL PPLLRepair

private def commonTail {ψ : Nat} (hψ : ψ > 0)
    (q : AgentState ψ × AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

theorem final_eq_of_beforeSuppress_eq
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ)
    (h :
      ZZRepairAll8.ppllIntegratedBeforeSuppressAll5 hψ κ l r =
        ppllIntegratedBeforeSuppress hψ κ l r) :
    ZZRepairAll8.ppllIntegratedRepairAll5 hψ κ l r =
      ppllIntegratedRepair hψ κ l r := by
  calc
    ZZRepairAll8.ppllIntegratedRepairAll5 hψ κ l r =
        commonTail hψ
          (ZZRepairAll8.ppllIntegratedBeforeSuppressAll5 hψ κ l r) := by
      rfl
    _ =
        commonTail hψ
          (ppllIntegratedBeforeSuppress hψ κ l r) :=
      congrArg (commonTail hψ) h
    _ = ppllIntegratedRepair hψ κ l r := by
      rfl

theorem fixCell_eq_self_of_guard_false
    {ψ : Nat} (u : AgentState ψ)
    (h : ZZRepairAll8.jamGuard u = false) :
    ZZRepairAll8.fixCell u = u := by
  unfold ZZRepairAll8.fixCell
  rw [h]
  rfl

theorem fixCell_eq_mark_of_guard_true
    {ψ : Nat} (u : AgentState ψ)
    (h : ZZRepairAll8.jamGuard u = true) :
    ZZRepairAll8.fixCell u =
      { u with
          path4 := some ((-1 : Int), 1)
          path5 := some ((-1 : Int), 1) } := by
  unfold ZZRepairAll8.fixCell
  rw [h]
  rfl

theorem first_pPsi_same_of_no_jam
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl : ZZRepairAll8.jamGuard l = false)
    (hr : ZZRepairAll8.jamGuard r = false) :
    pPsi hψ (ZZRepairAll8.fixCell l) (ZZRepairAll8.fixCell r) =
      pPsi hψ l r := by
  rw [fixCell_eq_self_of_guard_false l hl]
  rw [fixCell_eq_self_of_guard_false r hr]

private def all5GenStart {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l :=
    if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧
       l.path = .bot then
      { l with state := .produce }
    else l
  let r :=
    if r.label ≠ ⟨0, hψ⟩ ∧
       l.state = .produce ∧ r.path = .bot then
      { r with state := .produce }
    else r
  (l, r)

private theorem all5GenStart_left_produce
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hleader : l.leader = false)
    (hlabel : l.label = ⟨0, hψ⟩)
    (hpath : l.path = .bot) :
    (all5GenStart hψ l r).1.state = .produce := by
  unfold all5GenStart
  rw [if_pos ⟨hleader, hlabel, hpath⟩]

private theorem mainGenStart_left_fixed_of_wait_true
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hwait : l.wait = true) :
    (genSigSaturatedStart hψ l r).1.state = l.state := by
  have hfalse :
      ¬ (l.leader = false ∧
         l.label = ⟨0, hψ⟩ ∧
         l.wait = false ∧
         l.path = .bot) := by
    intro h
    have hb : true = false :=
      hwait.symm.trans h.2.2.1
    cases hb
  unfold genSigSaturatedStart
  rw [if_neg hfalse]

theorem gen_start_diff_of_wait_true
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hleader : l.leader = false)
    (hlabel : l.label = ⟨0, hψ⟩)
    (hpath : l.path = .bot)
    (hwait : l.wait = true)
    (hstate : l.state ≠ .produce) :
    all5GenStart hψ l r ≠
      genSigSaturatedStart hψ l r := by
  intro heq
  have hpair :=
    congrArg
      (fun q : AgentState ψ × AgentState ψ => q.1.state)
      heq
  have hall :=
    all5GenStart_left_produce
      hψ l r hleader hlabel hpath
  have hmain :=
    mainGenStart_left_fixed_of_wait_true
      hψ l r hwait
  have hs : MainState.produce = l.state :=
    hall.symm.trans (hpair.trans hmain)
  exact hstate hs.symm

theorem clean_bot_connector_shape
    {ψ : Nat} (u : AgentState ψ)
    (hpath : u.path = .bot) :
    cleanSigGenConnect u = u ∧
      ZZRepairAll8.cleanSigGenConnectBot u =
        { u with path5 := some ((-1 : Int), 1) } := by
  unfold cleanSigGenConnect ZZRepairAll8.cleanSigGenConnectBot
  rw [hpath]
  exact ⟨rfl, rfl⟩

private theorem compareSigInit_eq_of_some
    {ψ : Nat} (l : AgentState ψ)
    (pathLabel pathBit : Nat)
    (hpath : l.path = PathInfo.some pathLabel pathBit) :
    compareSigInit l = l := by
  unfold compareSigInit
  rw [hpath]

private theorem compareAll5_eq_dispatch_of_some
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (ll lb rl rb : Nat)
    (hl : l.path = PathInfo.some ll lb)
    (hr : r.path = PathInfo.some rl rb) :
    ZZRepairAll8.compareSigGuarded hψ l r =
      compareSigDispatch hψ
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).2 := by
  simp only [ZZRepairAll8.compareSigGuarded,
    compareSigInit_eq_of_some l ll lb hl,
    hl, hr]

private theorem compareMain_eq_dispatch_of_some
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (ll lb rl rb : Nat)
    (hl : l.path = PathInfo.some ll lb)
    (hr : r.path = PathInfo.some rl rb) :
    compareSigNoSourceRearm hψ l r =
      compareSigDispatch hψ
        (cmpUpdateNoSourceRearm hψ l r).1
        (cmpUpdateNoSourceRearm hψ l r).2 := by
  simp only [compareSigNoSourceRearm,
    compareSigInit_eq_of_some l ll lb hl,
    hl, hr]

private def all5CmpSeed {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ) : AgentState ψ :=
  if l.label = ⟨0, hψ⟩ ∧
      (l.state ≠ .depart ∨ l.leader = false) then
    { l with state := .congest }
  else l

private def mainCmpSeed {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ) : AgentState ψ :=
  if l.label = ⟨0, hψ⟩ ∧
      l.state ≠ .depart then
    { l with state := .congest }
  else l

private def cmpTail {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := cmpUpdatePropagate hψ l r
  (cmpUpdateSetPath2 hψ q.1, q.2)

private theorem cmpUpdateGuarded_eq_tail
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    ZZRepairAll8.cmpUpdateGuarded hψ l r =
      cmpTail hψ (all5CmpSeed hψ l) r := by
  rfl

private theorem cmpUpdateMain_eq_tail
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    cmpUpdateNoSourceRearm hψ l r =
      cmpTail hψ (mainCmpSeed hψ l) r := by
  rfl

theorem cmp_seed_fork_of_depart_follower_zero
    {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ)
    (hlabel : l.label = ⟨0, hψ⟩)
    (hstate : l.state = .depart)
    (hleader : l.leader = false) :
    all5CmpSeed hψ l =
        { l with state := .congest } ∧
      mainCmpSeed hψ l = l := by
  have hall :
      l.label = ⟨0, hψ⟩ ∧
        (l.state ≠ .depart ∨ l.leader = false) :=
    ⟨hlabel, Or.inr hleader⟩
  have hmain :
      ¬ (l.label = ⟨0, hψ⟩ ∧
         l.state ≠ .depart) := by
    intro h
    exact h.2 hstate
  unfold all5CmpSeed mainCmpSeed
  rw [if_pos hall]
  rw [if_neg hmain]
  exact ⟨rfl, rfl⟩

theorem cmp_seed_same_of_state_ne_depart
    {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ)
    (hstate : l.state ≠ .depart) :
    all5CmpSeed hψ l =
      mainCmpSeed hψ l := by
  by_cases hlabel :
      l.label = ⟨0, hψ⟩
  · unfold all5CmpSeed mainCmpSeed
    rw [if_pos ⟨hlabel, Or.inl hstate⟩]
    rw [if_pos ⟨hlabel, hstate⟩]
  · unfold all5CmpSeed mainCmpSeed
    rw [if_neg (fun h => hlabel h.1)]
    rw [if_neg (fun h => hlabel h.1)]

theorem cmp_update_same_of_seed_same
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hseed :
      all5CmpSeed hψ l =
        mainCmpSeed hψ l) :
    ZZRepairAll8.cmpUpdateGuarded hψ l r =
      cmpUpdateNoSourceRearm hψ l r := by
  calc
    ZZRepairAll8.cmpUpdateGuarded hψ l r =
        cmpTail hψ (all5CmpSeed hψ l) r :=
      cmpUpdateGuarded_eq_tail hψ l r
    _ =
        cmpTail hψ (mainCmpSeed hψ l) r :=
      congrArg (fun x => cmpTail hψ x r) hseed
    _ = cmpUpdateNoSourceRearm hψ l r :=
      (cmpUpdateMain_eq_tail hψ l r).symm

theorem compare_same_of_some_of_cmp_same
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (ll lb rl rb : Nat)
    (hl : l.path = PathInfo.some ll lb)
    (hr : r.path = PathInfo.some rl rb)
    (hcmp :
      ZZRepairAll8.cmpUpdateGuarded hψ l r =
        cmpUpdateNoSourceRearm hψ l r) :
    ZZRepairAll8.compareSigGuarded hψ l r =
      compareSigNoSourceRearm hψ l r := by
  rw [compareAll5_eq_dispatch_of_some
    hψ l r ll lb rl rb hl hr]
  rw [compareMain_eq_dispatch_of_some
    hψ l r ll lb rl rb hl hr]
  rw [hcmp]

private theorem h2 : 0 < (2 : Nat) := by
  decide

private def forkL : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false
      label := (0 : Fin 2)
      state := .depart
      path := .some 0 0
      path2 := none }

private def forkR : AgentState 2 :=
  { BoundedAgentState.erase Q16405.s with
      leader := false
      label := (1 : Fin 2)
      state := .none
      path := .some 1 0
      path2 := none }

theorem compare_fork_witness :
    ZZRepairAll8.compareSigGuarded h2 forkL forkR ≠
      compareSigNoSourceRearm h2 forkL forkR := by
  decide +kernel

#print axioms ZZC5bForkLayer.final_eq_of_beforeSuppress_eq
#print axioms ZZC5bForkLayer.first_pPsi_same_of_no_jam
#print axioms ZZC5bForkLayer.gen_start_diff_of_wait_true
#print axioms ZZC5bForkLayer.clean_bot_connector_shape
#print axioms ZZC5bForkLayer.cmp_seed_fork_of_depart_follower_zero
#print axioms ZZC5bForkLayer.compare_fork_witness

end ZZC5bForkLayer
