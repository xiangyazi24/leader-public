import Leader.Wu.Protocol.CompareStageFrames
import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZT1CompareStage

open PPLL

/-!
`ZZWaitStaged.trapProj` has eight fields.  COMPARE may change `state` and
`path2`, so this is exactly the subprojection that the complete guarded
COMPARE stage must frame.  Keeping `leader` here gives the stronger equality
used by `compareSigGuarded_no_leader`.
-/
abbrev compareProj {ψ : Nat} (u : AgentState ψ) :=
  (u.leader, u.label, u.bit, u.path, u.path3, u.write)

/-! ## 1. Matcher-free staged definitions -/

/-- The guarded label-zero state assignment, packaged as a pair stage. -/
def cmpGuardStart {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  ((if l.label = ⟨0, hψ⟩ ∧
        (l.state ≠ MainState.depart ∨ l.leader = false) then
      { l with state := MainState.congest }
    else l),
   r)

/-- The final `path2` writer, packaged as a pair stage. -/
def cmpGuardFinish {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (cmpUpdateSetPath2 hψ l, r)

/-- Pair-staged form of `ZZRepairAll8.cmpUpdateGuarded`. -/
def cmpUpdateGuardedStaged {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := cmpGuardStart hψ l r
  let q := cmpUpdatePropagate hψ q.1 q.2
  cmpGuardFinish hψ q.1 q.2

theorem cmpUpdateGuarded_eq_staged
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    ZZRepairAll8.cmpUpdateGuarded hψ l r =
      cmpUpdateGuardedStaged hψ l r := by
  rfl

/-- Initializer packaged as a pair stage. -/
def compareInitPair {ψ : Nat}
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (compareSigInit l, r)

/-- The branch in which both main paths are present. -/
def compareGuardActive {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ZZRepairAll8.cmpUpdateGuarded hψ l r
  compareSigDispatch hψ q.1 q.2

/-- The responder-main-path dispatch. -/
def compareGuardRight {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match r.path with
  | .some _ _ => compareGuardActive hψ l r
  | .bot => (l, r)

/-- The initiator-main-path dispatch. -/
def compareGuardLeft {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  match l.path with
  | .bot => (l, r)
  | .some _ _ => compareGuardRight hψ l r

/-- Matcher-free staged form of `ZZRepairAll8.compareSigGuarded`. -/
def compareSigGuardedStaged {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := compareInitPair l r
  compareGuardLeft hψ q.1 q.2

theorem compareSigGuarded_eq_staged
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    ZZRepairAll8.compareSigGuarded hψ l r =
      compareSigGuardedStaged hψ l r := by
  rfl

/-! ## 2. Six-field projection frames -/

theorem compareProj_eq_of_fields
    {ψ : Nat} {u v : AgentState ψ}
    (hleader : u.leader = v.leader)
    (hlabel : u.label = v.label)
    (hbit : u.bit = v.bit)
    (hpath : u.path = v.path)
    (hpath3 : u.path3 = v.path3)
    (hwrite : u.write = v.write) :
    compareProj u = compareProj v := by
  simp only [compareProj, Prod.mk.injEq]
  exact ⟨hleader, hlabel, hbit, hpath, hpath3, hwrite⟩

theorem compareSigInit_proj
    {ψ : Nat} (u : AgentState ψ) :
    compareProj (compareSigInit u) = compareProj u := by
  exact compareProj_eq_of_fields
    (ZZT0Compare.compareSigInit_leader u)
    (ZZT0Compare.compareSigInit_label u)
    (ZZT0Compare.compareSigInit_bit u)
    (ZZT0Compare.compareSigInit_path u)
    (ZZT0Compare.compareSigInit_path3 u)
    (ZZT0Compare.compareSigInit_write u)

theorem cmpGuardStart_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (cmpGuardStart hψ l r).1,
     compareProj (cmpGuardStart hψ l r).2) =
      (compareProj l, compareProj r) := by
  simp only [cmpGuardStart]
  split <;> rfl

theorem cmpUpdatePropagate_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (cmpUpdatePropagate hψ l r).1,
     compareProj (cmpUpdatePropagate hψ l r).2) =
      (compareProj l, compareProj r) := by
  have hleader := ZZT0Compare.cmpUpdatePropagate_leader hψ l r
  have hlabel := ZZT0Compare.cmpUpdatePropagate_label hψ l r
  have hbit := ZZT0Compare.cmpUpdatePropagate_bit hψ l r
  have hpath := ZZT0Compare.cmpUpdatePropagate_path hψ l r
  have hpath3 := ZZT0Compare.cmpUpdatePropagate_path3 hψ l r
  have hwrite := ZZT0Compare.cmpUpdatePropagate_write hψ l r
  apply Prod.ext
  · exact compareProj_eq_of_fields
      hleader.1 hlabel.1 hbit.1 hpath.1 hpath3.1 hwrite.1
  · exact compareProj_eq_of_fields
      hleader.2 hlabel.2 hbit.2 hpath.2 hpath3.2 hwrite.2

theorem cmpUpdateSetPath2_proj
    {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    compareProj (cmpUpdateSetPath2 hψ u) = compareProj u := by
  cases hpath : u.path with
  | bot =>
      simp only [cmpUpdateSetPath2, hpath]
  | some pathLabel pathBit =>
      simp only [cmpUpdateSetPath2, hpath]
      split
      · exact compareProj_eq_of_fields
          rfl rfl rfl hpath.symm rfl rfl
      · rfl

theorem cmpGuardFinish_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (cmpGuardFinish hψ l r).1,
     compareProj (cmpGuardFinish hψ l r).2) =
      (compareProj l, compareProj r) := by
  simp only [cmpGuardFinish]
  apply Prod.ext
  · exact cmpUpdateSetPath2_proj hψ l
  · rfl

theorem cmpUpdateGuarded_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (ZZRepairAll8.cmpUpdateGuarded hψ l r).1,
     compareProj (ZZRepairAll8.cmpUpdateGuarded hψ l r).2) =
      (compareProj l, compareProj r) := by
  rw [cmpUpdateGuarded_eq_staged]
  simp only [cmpUpdateGuardedStaged]
  rw [cmpGuardFinish_proj, cmpUpdatePropagate_proj, cmpGuardStart_proj]

theorem compareBitUpdateL_proj
    {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) :
    compareProj (compareBitUpdateL hψ l) = compareProj l := by
  cases hpath2 : l.path2 with
  | none =>
      simp only [compareBitUpdateL, hpath2]
  | some p2 =>
      cases hpath : l.path with
      | bot =>
          simp only [compareBitUpdateL, hpath2, hpath]
      | some pathLabel pathBit =>
          simp only [compareBitUpdateL, hpath2, hpath]
          split
          · exact compareProj_eq_of_fields
              rfl rfl rfl hpath.symm rfl rfl
          · rfl

theorem compareBitUpdateR_proj
    {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ) :
    compareProj (compareBitUpdateR hψ r) = compareProj r := by
  cases hpath2 : r.path2 with
  | none =>
      simp only [compareBitUpdateR, hpath2]
  | some p2 =>
      simp only [compareBitUpdateR, hpath2]
      repeat (first | rfl | split)

theorem compareBit_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (compareBit hψ l r).1,
     compareProj (compareBit hψ l r).2) =
      (compareProj l, compareProj r) := by
  simp only [compareBit]
  apply Prod.ext
  · exact compareBitUpdateL_proj hψ l
  · exact compareBitUpdateR_proj hψ r

theorem compareSigDispatch_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (compareSigDispatch hψ l r).1,
     compareProj (compareSigDispatch hψ l r).2) =
      (compareProj l, compareProj r) := by
  cases hl : l.path2 with
  | none =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
      | some p2 =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_proj hψ l r
  | some p2 =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_proj hψ l r
      | some p2r =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_proj hψ l r

theorem compareInitPair_proj
    {ψ : Nat} (l r : AgentState ψ) :
    (compareProj (compareInitPair l r).1,
     compareProj (compareInitPair l r).2) =
      (compareProj l, compareProj r) := by
  simp only [compareInitPair]
  apply Prod.ext
  · exact compareSigInit_proj l
  · rfl

theorem compareGuardActive_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (compareGuardActive hψ l r).1,
     compareProj (compareGuardActive hψ l r).2) =
      (compareProj l, compareProj r) := by
  simp only [compareGuardActive]
  rw [compareSigDispatch_proj, cmpUpdateGuarded_proj]

theorem compareGuardRight_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (compareGuardRight hψ l r).1,
     compareProj (compareGuardRight hψ l r).2) =
      (compareProj l, compareProj r) := by
  cases hpath : r.path with
  | bot =>
      simp only [compareGuardRight, hpath]
  | some pathLabel pathBit =>
      simp only [compareGuardRight, hpath]
      exact compareGuardActive_proj hψ l r

theorem compareGuardLeft_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (compareGuardLeft hψ l r).1,
     compareProj (compareGuardLeft hψ l r).2) =
      (compareProj l, compareProj r) := by
  cases hpath : l.path with
  | bot =>
      simp only [compareGuardLeft, hpath]
  | some pathLabel pathBit =>
      simp only [compareGuardLeft, hpath]
      exact compareGuardRight_proj hψ l r

theorem compareSigGuarded_proj
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareProj (ZZRepairAll8.compareSigGuarded hψ l r).1,
     compareProj (ZZRepairAll8.compareSigGuarded hψ l r).2) =
      (compareProj l, compareProj r) := by
  rw [compareSigGuarded_eq_staged]
  simp only [compareSigGuardedStaged]
  rw [compareGuardLeft_proj, compareInitPair_proj]

/-- Requested item 1. -/
theorem compareSigGuarded_frames
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    ((ZZRepairAll8.compareSigGuarded hψ l r).1.label = l.label ∧
     (ZZRepairAll8.compareSigGuarded hψ l r).2.label = r.label) ∧
    ((ZZRepairAll8.compareSigGuarded hψ l r).1.bit = l.bit ∧
     (ZZRepairAll8.compareSigGuarded hψ l r).2.bit = r.bit) ∧
    ((ZZRepairAll8.compareSigGuarded hψ l r).1.path = l.path ∧
     (ZZRepairAll8.compareSigGuarded hψ l r).2.path = r.path) ∧
    ((ZZRepairAll8.compareSigGuarded hψ l r).1.path3 = l.path3 ∧
     (ZZRepairAll8.compareSigGuarded hψ l r).2.path3 = r.path3) ∧
    ((ZZRepairAll8.compareSigGuarded hψ l r).1.write = l.write ∧
     (ZZRepairAll8.compareSigGuarded hψ l r).2.write = r.write) := by
  have h := compareSigGuarded_proj hψ l r
  simp only [compareProj, Prod.mk.injEq] at h
  exact
    ⟨⟨h.1.2.1, h.2.2.1⟩,
     ⟨h.1.2.2.1, h.2.2.2.1⟩,
     ⟨h.1.2.2.2.1, h.2.2.2.2.1⟩,
     ⟨h.1.2.2.2.2.1, h.2.2.2.2.2.1⟩,
     ⟨h.1.2.2.2.2.2, h.2.2.2.2.2.2⟩⟩

/-- Stronger than item 3: COMPARE frames both leader fields unconditionally. -/
theorem compareSigGuarded_leader
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.leader = l.leader ∧
      (ZZRepairAll8.compareSigGuarded hψ l r).2.leader = r.leader := by
  have h := compareSigGuarded_proj hψ l r
  simp only [compareProj, Prod.mk.injEq] at h
  exact ⟨h.1.1, h.2.1⟩

/-- Requested item 3. -/
theorem compareSigGuarded_no_leader
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) (hr : r.leader = false) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.leader = false ∧
      (ZZRepairAll8.compareSigGuarded hψ l r).2.leader = false := by
  have h := compareSigGuarded_leader hψ l r
  exact ⟨h.1.trans hl, h.2.trans hr⟩

/-! ## 3. Exact `path2` effects on `none/A5` -/

theorem compareBitUpdateL_eq_of_action_ne_two
    {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) (p : Path2Info)
    (hpath2 : u.path2 = some p)
    (haction : p.action ≠ 2) :
    compareBitUpdateL hψ u = u := by
  cases hpath : u.path with
  | bot =>
      simp only [compareBitUpdateL, hpath2, hpath]
  | some pathLabel pathBit =>
      have hguard : ¬ (p.action = 2 ∧ p.position = 0) := by
        intro h
        exact haction h.1
      simp only [compareBitUpdateL, hpath2, hpath, if_neg hguard]

theorem compareBitUpdateL_after_setPath2_of_A5
    {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ)
    (hpath2 : u.path2 = none ∨
      u.path2 = some ZZT0Compare.A5) :
    compareBitUpdateL hψ (cmpUpdateSetPath2 hψ u) =
      cmpUpdateSetPath2 hψ u := by
  cases hpath : u.path with
  | bot =>
      have hset : cmpUpdateSetPath2 hψ u = u := by
        simp only [cmpUpdateSetPath2, hpath]
      rw [hset]
      exact ZZT0Compare.compareBitUpdateL_notA2 hψ u hpath2
  | some pathLabel pathBit =>
      simp only [cmpUpdateSetPath2, hpath]
      split
      · exact compareBitUpdateL_eq_of_action_ne_two
          hψ
          { u with
            path := PathInfo.some pathLabel pathBit,
            path2 := some ⟨pathLabel, pathBit, ψ, 1⟩ }
          ⟨pathLabel, pathBit, ψ, 1⟩
          rfl
          (by
            change (1 : Nat) ≠ 2
            omega)
      · exact ZZT0Compare.compareBitUpdateL_notA2 hψ u hpath2

theorem cmpGuardStart_path2
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpGuardStart hψ l r).1.path2 = l.path2 ∧
      (cmpGuardStart hψ l r).2.path2 = r.path2 := by
  unfold cmpGuardStart
  by_cases h :
      l.label = ⟨0, hψ⟩ ∧
        (l.state ≠ MainState.depart ∨ l.leader = false)
  · rw [if_pos h]
    exact ⟨rfl, rfl⟩
  · rw [if_neg h]
    exact ⟨rfl, rfl⟩

theorem cmpGuardStart_path
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpGuardStart hψ l r).1.path = l.path ∧
      (cmpGuardStart hψ l r).2.path = r.path := by
  unfold cmpGuardStart
  by_cases h :
      l.label = ⟨0, hψ⟩ ∧
        (l.state ≠ MainState.depart ∨ l.leader = false)
  · rw [if_pos h]
    exact ⟨rfl, rfl⟩
  · rw [if_neg h]
    exact ⟨rfl, rfl⟩

theorem cmpUpdateGuarded_right_path2
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (ZZRepairAll8.cmpUpdateGuarded hψ l r).2.path2 = r.path2 := by
  let s := cmpGuardStart hψ l r
  let p := cmpUpdatePropagate hψ s.1 s.2
  have hs : s.2.path2 = r.path2 :=
    (cmpGuardStart_path2 hψ l r).2
  have hp : p.2.path2 = s.2.path2 :=
    (ZZT0Compare.cmpUpdatePropagate_path2 hψ s.1 s.2).2
  rw [cmpUpdateGuarded_eq_staged]
  change p.2.path2 = r.path2
  exact hp.trans hs

theorem cmpUpdateGuarded_left_path2_range
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩ := by
  let s := cmpGuardStart hψ l r
  let p := cmpUpdatePropagate hψ s.1 s.2
  have hsPath2 : s.1.path2 = l.path2 :=
    (cmpGuardStart_path2 hψ l r).1
  have hpPath2 : p.1.path2 = s.1.path2 :=
    (ZZT0Compare.cmpUpdatePropagate_path2 hψ s.1 s.2).1
  have hpath2 : p.1.path2 = l.path2 :=
    hpPath2.trans hsPath2
  have hsPath : s.1.path = l.path :=
    (cmpGuardStart_path hψ l r).1
  have hpPath : p.1.path = s.1.path :=
    (ZZT0Compare.cmpUpdatePropagate_path hψ s.1 s.2).1
  have hpath : p.1.path = l.path :=
    hpPath.trans hsPath
  rw [cmpUpdateGuarded_eq_staged]
  change
    (cmpUpdateSetPath2 hψ p.1).path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (cmpUpdateSetPath2 hψ p.1).path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩
  cases hpMain : p.1.path with
  | bot =>
      simp only [cmpUpdateSetPath2, hpMain]
      exact Or.inl hpath2
  | some pathLabel pathBit =>
      simp only [cmpUpdateSetPath2, hpMain]
      split
      · exact Or.inr
          ⟨pathLabel, pathBit,
           hpath.symm.trans hpMain,
           rfl⟩
      · exact Or.inl hpath2

theorem cmpUpdateGuarded_left_dispatch_inert_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath2 : l.path2 = none ∨
      l.path2 = some ZZT0Compare.A5) :
    compareBitUpdateL hψ
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1 =
      (ZZRepairAll8.cmpUpdateGuarded hψ l r).1 := by
  let s := cmpGuardStart hψ l r
  let p := cmpUpdatePropagate hψ s.1 s.2
  have hs : s.1.path2 = l.path2 :=
    (cmpGuardStart_path2 hψ l r).1
  have hp : p.1.path2 = s.1.path2 :=
    (ZZT0Compare.cmpUpdatePropagate_path2 hψ s.1 s.2).1
  have hpA5 : p.1.path2 = none ∨
      p.1.path2 = some ZZT0Compare.A5 := by
    rcases hpath2 with hnone | hA5
    · exact Or.inl (hp.trans (hs.trans hnone))
    · exact Or.inr (hp.trans (hs.trans hA5))
  rw [cmpUpdateGuarded_eq_staged]
  change compareBitUpdateL hψ (cmpUpdateSetPath2 hψ p.1) =
    cmpUpdateSetPath2 hψ p.1
  exact compareBitUpdateL_after_setPath2_of_A5 hψ p.1 hpA5

theorem cmpUpdateGuarded_right_dispatch_inert_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    compareBitUpdateR hψ
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).2 =
      (ZZRepairAll8.cmpUpdateGuarded hψ l r).2 := by
  have hframe := cmpUpdateGuarded_right_path2 hψ l r
  have hout :
      (ZZRepairAll8.cmpUpdateGuarded hψ l r).2.path2 = none ∨
      (ZZRepairAll8.cmpUpdateGuarded hψ l r).2.path2 =
        some ZZT0Compare.A5 := by
    rcases hpath2 with hnone | hA5
    · exact Or.inl (hframe.trans hnone)
    · exact Or.inr (hframe.trans hA5)
  exact ZZT0Compare.compareBitUpdateR_pos1
    hψ (ZZRepairAll8.cmpUpdateGuarded hψ l r).2 hout

theorem compareBit_eq_of_updates
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hleft : compareBitUpdateL hψ l = l)
    (hright : compareBitUpdateR hψ r = r) :
    compareBit hψ l r = (l, r) := by
  simp only [compareBit]
  rw [hleft, hright]

theorem compareSigDispatch_eq_of_updates
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hleft : compareBitUpdateL hψ l = l)
    (hright : compareBitUpdateR hψ r = r) :
    compareSigDispatch hψ l r = (l, r) := by
  cases hl : l.path2 with
  | none =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
      | some p2 =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_eq_of_updates hψ l r hleft hright
  | some p2 =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_eq_of_updates hψ l r hleft hright
      | some p2r =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_eq_of_updates hψ l r hleft hright

theorem compareBit_left_path2_of_updateL
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hleft : compareBitUpdateL hψ l = l) :
    (compareBit hψ l r).1.path2 = l.path2 := by
  simp only [compareBit]
  rw [hleft]

theorem compareSigDispatch_left_path2_of_updateL
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hleft : compareBitUpdateL hψ l = l) :
    (compareSigDispatch hψ l r).1.path2 = l.path2 := by
  cases hl : l.path2 with
  | none =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
      | some p2 =>
          simp only [compareSigDispatch, hl, hr]
          simpa only [hl] using
            (compareBit_left_path2_of_updateL hψ l r hleft)
  | some p2 =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
          simpa only [hl] using
            (compareBit_left_path2_of_updateL hψ l r hleft)
      | some p2r =>
          simp only [compareSigDispatch, hl, hr]
          simpa only [hl] using
            (compareBit_left_path2_of_updateL hψ l r hleft)

theorem compareBit_right_path2_of_updateR
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hright : compareBitUpdateR hψ r = r) :
    (compareBit hψ l r).2.path2 = r.path2 := by
  simp only [compareBit]
  rw [hright]

theorem compareSigDispatch_right_path2_of_updateR
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hright : compareBitUpdateR hψ r = r) :
    (compareSigDispatch hψ l r).2.path2 = r.path2 := by
  cases hl : l.path2 with
  | none =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
      | some p2 =>
          simp only [compareSigDispatch, hl, hr]
          simpa only [hr] using
            (compareBit_right_path2_of_updateR hψ l r hright)
  | some p2 =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
          simpa only [hr] using
            (compareBit_right_path2_of_updateR hψ l r hright)
      | some p2r =>
          simp only [compareSigDispatch, hl, hr]
          simpa only [hr] using
            (compareBit_right_path2_of_updateR hψ l r hright)

theorem compareGuardActive_right_path2_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    (compareGuardActive hψ l r).2.path2 = r.path2 := by
  let q := ZZRepairAll8.cmpUpdateGuarded hψ l r
  have hqFrame : q.2.path2 = r.path2 :=
    cmpUpdateGuarded_right_path2 hψ l r
  have hqA5 : q.2.path2 = none ∨
      q.2.path2 = some ZZT0Compare.A5 := by
    rcases hpath2 with hnone | hA5
    · exact Or.inl (hqFrame.trans hnone)
    · exact Or.inr (hqFrame.trans hA5)
  have hright : compareBitUpdateR hψ q.2 = q.2 :=
    ZZT0Compare.compareBitUpdateR_pos1 hψ q.2 hqA5
  have hdispatch :
      (compareSigDispatch hψ q.1 q.2).2.path2 = q.2.path2 :=
    compareSigDispatch_right_path2_of_updateR
      hψ q.1 q.2 hright
  change (compareSigDispatch hψ q.1 q.2).2.path2 = r.path2
  exact hdispatch.trans hqFrame

theorem compareGuardRight_right_path2_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    (compareGuardRight hψ l r).2.path2 = r.path2 := by
  cases hpath : r.path with
  | bot =>
      simp only [compareGuardRight, hpath]
  | some pathLabel pathBit =>
      simp only [compareGuardRight, hpath]
      exact compareGuardActive_right_path2_on_A5 hψ l r hpath2

theorem compareGuardLeft_right_path2_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    (compareGuardLeft hψ l r).2.path2 = r.path2 := by
  cases hpath : l.path with
  | bot =>
      simp only [compareGuardLeft, hpath]
  | some pathLabel pathBit =>
      simp only [compareGuardLeft, hpath]
      exact compareGuardRight_right_path2_on_A5 hψ l r hpath2

/-- The responder half of requested item 2 is globally true. -/
theorem compareSigGuarded_right_path2_inert_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    (ZZRepairAll8.compareSigGuarded hψ l r).2.path2 = r.path2 := by
  rw [compareSigGuarded_eq_staged]
  change (compareGuardLeft hψ (compareSigInit l) r).2.path2 = r.path2
  exact compareGuardLeft_right_path2_on_A5
    hψ (compareSigInit l) r hpath2

theorem compareGuardActive_path2_effect_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlPath2 : l.path2 = none ∨
      l.path2 = some ZZT0Compare.A5)
    (hrPath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    (compareGuardActive hψ l r).1.path2 =
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.path2 ∧
      (compareGuardActive hψ l r).2.path2 = r.path2 := by
  let q := ZZRepairAll8.cmpUpdateGuarded hψ l r
  have hleft : compareBitUpdateL hψ q.1 = q.1 :=
    cmpUpdateGuarded_left_dispatch_inert_on_A5 hψ l r hlPath2
  have hright : compareBitUpdateR hψ q.2 = q.2 :=
    cmpUpdateGuarded_right_dispatch_inert_on_A5 hψ l r hrPath2
  have hdispatch : compareSigDispatch hψ q.1 q.2 = (q.1, q.2) :=
    compareSigDispatch_eq_of_updates hψ q.1 q.2 hleft hright
  have hqRight : q.2.path2 = r.path2 :=
    cmpUpdateGuarded_right_path2 hψ l r
  change
    (compareSigDispatch hψ q.1 q.2).1.path2 = q.1.path2 ∧
      (compareSigDispatch hψ q.1 q.2).2.path2 = r.path2
  exact
    ⟨congrArg (fun z : AgentState ψ × AgentState ψ => z.1.path2)
       hdispatch,
     (congrArg (fun z : AgentState ψ × AgentState ψ => z.2.path2)
       hdispatch).trans hqRight⟩

theorem compareGuardActive_left_path2_range_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlPath2 : l.path2 = none ∨
      l.path2 = some ZZT0Compare.A5) :
    (compareGuardActive hψ l r).1.path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (compareGuardActive hψ l r).1.path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩ := by
  let q := ZZRepairAll8.cmpUpdateGuarded hψ l r
  have hleft : compareBitUpdateL hψ q.1 = q.1 :=
    cmpUpdateGuarded_left_dispatch_inert_on_A5 hψ l r hlPath2
  have hdispatch :
      (compareSigDispatch hψ q.1 q.2).1.path2 = q.1.path2 :=
    compareSigDispatch_left_path2_of_updateL
      hψ q.1 q.2 hleft
  have hq := cmpUpdateGuarded_left_path2_range hψ l r
  change
    (compareSigDispatch hψ q.1 q.2).1.path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (compareSigDispatch hψ q.1 q.2).1.path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩
  rcases hq with hsame | hwrite
  · exact Or.inl (hdispatch.trans hsame)
  · rcases hwrite with ⟨pathLabel, pathBit, hpath, hout⟩
    exact Or.inr
      ⟨pathLabel, pathBit, hpath, hdispatch.trans hout⟩

theorem compareSigInit_eq_of_some
    {ψ : Nat} (l : AgentState ψ) (pathLabel pathBit : Nat)
    (hpath : l.path = PathInfo.some pathLabel pathBit) :
    compareSigInit l = l := by
  simp only [compareSigInit, hpath]

theorem compareGuardLeft_eq_right_of_some
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (pathLabel pathBit : Nat)
    (hpath : l.path = PathInfo.some pathLabel pathBit) :
    compareGuardLeft hψ l r = compareGuardRight hψ l r := by
  simp only [compareGuardLeft, hpath]

theorem compareGuardRight_eq_active_of_some
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (pathLabel pathBit : Nat)
    (hpath : r.path = PathInfo.some pathLabel pathBit) :
    compareGuardRight hψ l r = compareGuardActive hψ l r := by
  simp only [compareGuardRight, hpath]

theorem compareGuardLeft_eq_self_of_bot
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath : l.path = PathInfo.bot) :
    compareGuardLeft hψ l r = (l, r) := by
  simp only [compareGuardLeft, hpath]

theorem compareGuardRight_eq_self_of_bot
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hpath : r.path = PathInfo.bot) :
    compareGuardRight hψ l r = (l, r) := by
  simp only [compareGuardRight, hpath]

/--
The actual poison-shape immortality theorem.  It is stronger than an A5-only
statement: no hypothesis on either `path2` is needed when one main path is bot.
-/
theorem compareSigGuarded_path2_inert_of_path_bot
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hbot : l.path = PathInfo.bot ∨ r.path = PathInfo.bot) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.path2 = l.path2 ∧
      (ZZRepairAll8.compareSigGuarded hψ l r).2.path2 = r.path2 := by
  have hinitPath := ZZT0Compare.compareSigInit_path l
  have hinitPath2 := ZZT0Compare.compareSigInit_path2 l
  rw [compareSigGuarded_eq_staged]
  change
    (compareGuardLeft hψ (compareSigInit l) r).1.path2 = l.path2 ∧
      (compareGuardLeft hψ (compareSigInit l) r).2.path2 = r.path2
  rcases hbot with hlbot | hrbot
  · have hl0bot : (compareSigInit l).path = PathInfo.bot :=
      hinitPath.trans hlbot
    rw [compareGuardLeft_eq_self_of_bot
      hψ (compareSigInit l) r hl0bot]
    exact ⟨hinitPath2, rfl⟩
  · cases hleft : (compareSigInit l).path with
    | bot =>
        rw [compareGuardLeft_eq_self_of_bot
          hψ (compareSigInit l) r hleft]
        exact ⟨hinitPath2, rfl⟩
    | some pathLabel pathBit =>
        rw [compareGuardLeft_eq_right_of_some
          hψ (compareSigInit l) r pathLabel pathBit hleft]
        rw [compareGuardRight_eq_self_of_bot
          hψ (compareSigInit l) r hrbot]
        exact ⟨hinitPath2, rfl⟩

theorem compareSigGuarded_left_path2_range_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlPath2 : l.path2 = none ∨
      l.path2 = some ZZT0Compare.A5) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (ZZRepairAll8.compareSigGuarded hψ l r).1.path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩ := by
  have hinitPath := ZZT0Compare.compareSigInit_path l
  have hinitPath2 := ZZT0Compare.compareSigInit_path2 l
  have hinitA5 : (compareSigInit l).path2 = none ∨
      (compareSigInit l).path2 = some ZZT0Compare.A5 := by
    rcases hlPath2 with hnone | hA5
    · exact Or.inl (hinitPath2.trans hnone)
    · exact Or.inr (hinitPath2.trans hA5)
  rw [compareSigGuarded_eq_staged]
  change
    (compareGuardLeft hψ (compareSigInit l) r).1.path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (compareGuardLeft hψ (compareSigInit l) r).1.path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩
  cases hleft : (compareSigInit l).path with
  | bot =>
      rw [compareGuardLeft_eq_self_of_bot
        hψ (compareSigInit l) r hleft]
      exact Or.inl hinitPath2
  | some pathLabel pathBit =>
      rw [compareGuardLeft_eq_right_of_some
        hψ (compareSigInit l) r pathLabel pathBit hleft]
      cases hright : r.path with
      | bot =>
          rw [compareGuardRight_eq_self_of_bot
            hψ (compareSigInit l) r hright]
          exact Or.inl hinitPath2
      | some rPathLabel rPathBit =>
          rw [compareGuardRight_eq_active_of_some
            hψ (compareSigInit l) r rPathLabel rPathBit hright]
          have hactive :=
            compareGuardActive_left_path2_range_on_A5
              hψ (compareSigInit l) r hinitA5
          rcases hactive with hsame | hwrite
          · exact Or.inl (hsame.trans hinitPath2)
          · rcases hwrite with
              ⟨outLabel, outBit, houtPath, houtPath2⟩
            exact Or.inr
              ⟨outLabel, outBit,
               hinitPath.symm.trans houtPath,
               houtPath2⟩

/--
Strongest simple whole-wrapper replacement for the false two-sided inertness
claim: the right token is immortal; the left token is either immortal or is
exactly the action-1 record emitted by `cmpUpdateSetPath2` from its main path.
-/
theorem compareSigGuarded_path2_effect_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlPath2 : l.path2 = none ∨
      l.path2 = some ZZT0Compare.A5)
    (hrPath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    ((ZZRepairAll8.compareSigGuarded hψ l r).1.path2 = l.path2 ∨
      ∃ pathLabel pathBit,
        l.path = PathInfo.some pathLabel pathBit ∧
        (ZZRepairAll8.compareSigGuarded hψ l r).1.path2 =
          some ⟨pathLabel, pathBit, ψ, 1⟩) ∧
    (ZZRepairAll8.compareSigGuarded hψ l r).2.path2 = r.path2 := by
  exact
    ⟨compareSigGuarded_left_path2_range_on_A5
       hψ l r hlPath2,
     compareSigGuarded_right_path2_inert_on_A5
       hψ l r hrPath2⟩

/-- Exact active-branch effect, useful when both main paths are known present. -/
theorem compareSigGuarded_active_path2_effect_on_A5
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (lPathLabel lPathBit rPathLabel rPathBit : Nat)
    (hlPath : l.path = PathInfo.some lPathLabel lPathBit)
    (hrPath : r.path = PathInfo.some rPathLabel rPathBit)
    (hlPath2 : l.path2 = none ∨
      l.path2 = some ZZT0Compare.A5)
    (hrPath2 : r.path2 = none ∨
      r.path2 = some ZZT0Compare.A5) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.path2 =
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.path2 ∧
      (ZZRepairAll8.compareSigGuarded hψ l r).2.path2 = r.path2 := by
  have hinit :=
    compareSigInit_eq_of_some l lPathLabel lPathBit hlPath
  rw [compareSigGuarded_eq_staged]
  change
    (compareGuardLeft hψ (compareSigInit l) r).1.path2 =
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.path2 ∧
      (compareGuardLeft hψ (compareSigInit l) r).2.path2 = r.path2
  rw [hinit]
  rw [compareGuardLeft_eq_right_of_some
    hψ l r lPathLabel lPathBit hlPath]
  rw [compareGuardRight_eq_active_of_some
    hψ l r rPathLabel rPathBit hrPath]
  exact compareGuardActive_path2_effect_on_A5
    hψ l r hlPath2 hrPath2

end ZZT1CompareStage

#print axioms ZZT1CompareStage.cmpUpdateGuarded_eq_staged
#print axioms ZZT1CompareStage.compareSigGuarded_eq_staged
#print axioms ZZT1CompareStage.compareProj_eq_of_fields
#print axioms ZZT1CompareStage.compareSigInit_proj
#print axioms ZZT1CompareStage.cmpGuardStart_proj
#print axioms ZZT1CompareStage.cmpUpdatePropagate_proj
#print axioms ZZT1CompareStage.cmpUpdateSetPath2_proj
#print axioms ZZT1CompareStage.cmpGuardFinish_proj
#print axioms ZZT1CompareStage.cmpUpdateGuarded_proj
#print axioms ZZT1CompareStage.compareBitUpdateL_proj
#print axioms ZZT1CompareStage.compareBitUpdateR_proj
#print axioms ZZT1CompareStage.compareBit_proj
#print axioms ZZT1CompareStage.compareSigDispatch_proj
#print axioms ZZT1CompareStage.compareInitPair_proj
#print axioms ZZT1CompareStage.compareGuardActive_proj
#print axioms ZZT1CompareStage.compareGuardRight_proj
#print axioms ZZT1CompareStage.compareGuardLeft_proj
#print axioms ZZT1CompareStage.compareSigGuarded_proj
#print axioms ZZT1CompareStage.compareSigGuarded_frames
#print axioms ZZT1CompareStage.compareSigGuarded_leader
#print axioms ZZT1CompareStage.compareSigGuarded_no_leader
#print axioms ZZT1CompareStage.compareBitUpdateL_eq_of_action_ne_two
#print axioms ZZT1CompareStage.compareBitUpdateL_after_setPath2_of_A5
#print axioms ZZT1CompareStage.cmpGuardStart_path2
#print axioms ZZT1CompareStage.cmpGuardStart_path
#print axioms ZZT1CompareStage.cmpUpdateGuarded_right_path2
#print axioms ZZT1CompareStage.cmpUpdateGuarded_left_path2_range
#print axioms ZZT1CompareStage.cmpUpdateGuarded_left_dispatch_inert_on_A5
#print axioms ZZT1CompareStage.cmpUpdateGuarded_right_dispatch_inert_on_A5
#print axioms ZZT1CompareStage.compareBit_eq_of_updates
#print axioms ZZT1CompareStage.compareSigDispatch_eq_of_updates
#print axioms ZZT1CompareStage.compareBit_left_path2_of_updateL
#print axioms ZZT1CompareStage.compareSigDispatch_left_path2_of_updateL
#print axioms ZZT1CompareStage.compareBit_right_path2_of_updateR
#print axioms ZZT1CompareStage.compareSigDispatch_right_path2_of_updateR
#print axioms ZZT1CompareStage.compareGuardActive_right_path2_on_A5
#print axioms ZZT1CompareStage.compareGuardRight_right_path2_on_A5
#print axioms ZZT1CompareStage.compareGuardLeft_right_path2_on_A5
#print axioms ZZT1CompareStage.compareSigGuarded_right_path2_inert_on_A5
#print axioms ZZT1CompareStage.compareGuardActive_path2_effect_on_A5
#print axioms ZZT1CompareStage.compareGuardActive_left_path2_range_on_A5
#print axioms ZZT1CompareStage.compareSigInit_eq_of_some
#print axioms ZZT1CompareStage.compareGuardLeft_eq_right_of_some
#print axioms ZZT1CompareStage.compareGuardRight_eq_active_of_some
#print axioms ZZT1CompareStage.compareGuardLeft_eq_self_of_bot
#print axioms ZZT1CompareStage.compareGuardRight_eq_self_of_bot
#print axioms ZZT1CompareStage.compareSigGuarded_path2_inert_of_path_bot
#print axioms ZZT1CompareStage.compareSigGuarded_left_path2_range_on_A5
#print axioms ZZT1CompareStage.compareSigGuarded_path2_effect_on_A5
#print axioms ZZT1CompareStage.compareSigGuarded_active_path2_effect_on_A5
