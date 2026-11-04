import Leader.Wu.ZeroDivisible.CheckRepair

/-!
# Forward successor-edge cleanup of MainState.done

The physical 0-to-1 generator cut removes head done and makes any remaining
responder done releasable. CLEAN frames that cut, and releaseSource clears it.
The remaining actual R5 stages cannot create MainState.done. The writer's
WriteState.done is a distinct field and does not affect this invariant.
-/
namespace PPLLAstraR5Repair.ForwardDone
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
set_option autoImplicit false
set_option linter.unusedSimpArgs false

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl


private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl


private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by
  split <;> rfl


private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl


/-- The two fields framed by the read-only comparison and writer stages. -/
private def CoreView {ψ : Nat} (u : AgentState ψ) := (u.state, u.path)


private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    CoreView (if p then a else b) =
      if p then CoreView a else CoreView b := by
  split <;> rfl


attribute [local simp] fst_ite snd_ite state_ite path_ite view_ite

private theorem view_state {ψ : Nat} {a b : AgentState ψ}
    (h : CoreView a = CoreView b) : a.state = b.state :=
  congrArg Prod.fst h


private theorem view_path {ψ : Nat} {a b : AgentState ψ}
    (h : CoreView a = CoreView b) : a.path = b.path :=
  congrArg Prod.snd h


/-- A cell may keep or delete its path. Any output done must already
have been present on that same input cell. -/
private def CellMono {ψ : Nat} (before after : AgentState ψ) : Prop :=
  (after.path = before.path ∨ after.path = .bot) ∧
  (after.state = .done → before.state = .done)


private def PairMono {ψ : Nat}
    (l r l' r' : AgentState ψ) : Prop :=
  CellMono l l' ∧ CellMono r r'


private theorem cellMono_refl {ψ : Nat} (u : AgentState ψ) :
    CellMono u u := by
  simp [CellMono]


private theorem cellMono_of_view {ψ : Nat} {a b : AgentState ψ}
    (h : CoreView b = CoreView a) :
    CellMono a b := by
  constructor
  · exact Or.inl (view_path h)
  · intro hb
    rw [view_state h] at hb
    exact hb


private theorem cellMono_trans {ψ : Nat} {a b c : AgentState ψ}
    (hab : CellMono a b) (hbc : CellMono b c) :
    CellMono a c := by
  constructor
  · rcases hbc.1 with hcb | hbot
    · rcases hab.1 with hba | hbot'
      · exact Or.inl (hcb.trans hba)
      · exact Or.inr (hcb.trans hbot')
    · exact Or.inr hbot
  · intro hc
    exact hab.2 (hbc.2 hc)


private theorem pairMono_refl {ψ : Nat} (l r : AgentState ψ) :
    PairMono l r l r :=
  ⟨cellMono_refl l, cellMono_refl r⟩


private theorem pairMono_trans {ψ : Nat}
    {l r a b c d : AgentState ψ}
    (h1 : PairMono l r a b) (h2 : PairMono a b c d) :
    PairMono l r c d :=
  ⟨cellMono_trans h1.1 h2.1, cellMono_trans h1.2 h2.2⟩


private def NoDone {ψ : Nat} (l r : AgentState ψ) : Prop :=
  l.state ≠ .done ∧ r.state ≠ .done

private theorem noDone_mono {ψ : Nat} {l r a b : AgentState ψ}
    (h : NoDone l r) (hm : PairMono l r a b) : NoDone a b :=
  ⟨fun ha => h.1 (hm.1.2 ha), fun hb => h.2 (hm.2.2 hb)⟩

private theorem eliminate_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    PairMono l r (eliminateSig hp l r).1 (eliminateSig hp l r).2 := by
  unfold PairMono CellMono eliminateSig
  split <;> simp <;> split <;> simp


private theorem drop_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (dropStale u) := by
  unfold dropStale
  split <;> simp_all [CellMono]



private theorem precheck_mono {ψ : Nat} (l r : AgentState ψ) :
    PairMono l r (preCheckReset l r).1 (preCheckReset l r).2 := by
  unfold preCheckReset
  repeat (split <;> simp_all [PairMono, CellMono, clearCmp])
  all_goals grind [PairMono, CellMono, clearCmp]



private theorem moveTokens_view {ψ : Nat} (l r : AgentState ψ) :
    CoreView (moveTokens l r).1 = CoreView l ∧
    CoreView (moveTokens l r).2 = CoreView r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [moveTokens, hl, hr, CoreView, fst_ite, snd_ite, view_ite] <;>
    repeat (first | split) <;> simp_all [CoreView]


private theorem leaderWall_mono {ψ : Nat} (l r : AgentState ψ) :
    PairMono l r (leaderWall l r).1 (leaderWall l r).2 := by
  simp [PairMono, CellMono, leaderWall, clearCmp]
  repeat (first | split) <;> simp_all [CellMono, clearCmp]


private theorem control_mono {ψ : Nat} (hp : ψ > 0)
    (u : AgentState ψ) :
    CellMono u (sigMoveApplyControlConsume hp u) := by
  cases h : u.path2 <;>
    simp [CellMono, sigMoveApplyControlConsume, h] <;>
    repeat (first | split) <;> simp_all [CellMono]


private theorem step1F_noDone {ψ : Nat} (z : PPLLFableZDiv.Cfg)
    (l r : AgentState ψ) (h : NoDone l r) :
    NoDone (PPLLFableZDiv.sigMoveStep1F z l r).1
      (PPLLFableZDiv.sigMoveStep1F z l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [PPLLFableZDiv.sigMoveStep1F, hl, hr, NoDone]
  all_goals repeat (first | split) <;> simp_all [NoDone]
  all_goals grind [NoDone]

private theorem moveSourceF_noDone {ψ : Nat}
    (hp : ψ > 0) (z : PPLLFableZDiv.Cfg)
    (l r : AgentState ψ)
    (h : NoDone l r) :
    NoDone
      (PPLLFableZDiv.moveSourceF hp z l r).1
      (PPLLFableZDiv.moveSourceF hp z l r).2 := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hp⟩
  let a := if l.leader = true ∨
      (r.leader = true ∧ r.label ≠ nextLabel) then clearCmp l else l
  let b := if r.leader = true then clearCmp r else r
  have ha : CellMono l a := by
    dsimp [a]
    split <;> simp [CellMono, clearCmp]
  have hb : CellMono r b := by
    dsimp [b]
    split <;> simp [CellMono, clearCmp]
  have h0 : NoDone a b :=
    noDone_mono h ⟨ha, hb⟩


  let s := if a.state = .done then (a, b)
    else PPLLFableZDiv.sigMoveStep1F z a b
  have hs : NoDone s.1 s.2 := by
    dsimp [s]
    split
    · exact h0
    · exact step1F_noDone z a b h0


  let t := moveTokens s.1 s.2
  have ht : NoDone t.1 t.2 := by
    exact noDone_mono hs
      ⟨cellMono_of_view (moveTokens_view s.1 s.2).1,
       cellMono_of_view (moveTokens_view s.1 s.2).2⟩


  let w := leaderWall t.1 t.2
  have hw : NoDone w.1 w.2 :=
    noDone_mono ht (leaderWall_mono t.1 t.2)


  let x := sigMoveApplyControlConsume hp w.1
  let y := sigMoveApplyControlConsume hp w.2
  have hxy : NoDone x y := by
    exact noDone_mono hw
      ⟨control_mono hp w.1, control_mono hp w.2⟩


  let x' :=
    if y.state = .depart ∧ x.label.val < ψ - 1 ∧
        x.state = .CHECK_ready then
      { x with state := .depart }
    else x
  have hx : CellMono x x' := by
    dsimp [x']
    split <;> simp [CellMono]
  have hfin : NoDone x' y :=
    noDone_mono hxy ⟨hx, cellMono_refl y⟩


  simpa [PPLLFableZDiv.moveSourceF, nextLabel, a, b, s, t, w, x, y, x']
    using hfin


private theorem releaseCongest_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (releaseCongest u) := by
  simp [CellMono, releaseCongest]
  split <;> simp


private theorem normalizeOrphan_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (normalizeOrphan u) := by
  cases hp : u.path <;>
    simp [CellMono, normalizeOrphan, hp] <;>
    repeat (first | split) <;> simp_all [CellMono]


private theorem normalizeCarrier_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (normalizeCarrier u) := by
  cases hp : u.path <;>
    simp [CellMono, normalizeCarrier, releaseCongest, hp] <;>
    repeat (first | split) <;> simp_all [CellMono]


private theorem normalizeReady_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (normalizeReady u) := by
  generalize ho : normalizeOrphan u = o
  have hO := normalizeOrphan_mono u
  rw [ho] at hO
  let c := if o.state = .none ∧ aligned o then o else normalizeCarrier o
  have hC : CellMono o c := by
    dsimp [c]
    split
    · exact cellMono_refl o
    · exact normalizeCarrier_mono o
  have hOC := cellMono_trans hO hC
  have hF : CellMono c (normalizeReady u) := by
    simp only [normalizeReady, ho]
    change CellMono c
      (if c.leader then c else
       match c.path with
       | .bot => c
       | .some pl _ =>
         if c.state = .produce then
           { c with state := if pl = c.label.val then .none else .depart }
         else if (c.state = .equal ∨ c.state = .larger ∨ c.state = .less) ∧
             pl ≠ c.label.val then
           { c with state := .depart }
         else c)
    cases hp : c.path <;>
      simp [CellMono, hp] <;>
      repeat (first | split) <;> simp_all [CellMono]
    all_goals grind
  exact cellMono_trans hOC hF


private def r5Ready {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if waveState u.state ∨ u.state = .congest ∨ u.state = .done then u
  else checkSigSetReadyGuarded u


private theorem readyGuarded_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (checkSigSetReadyGuarded u) := by
  cases hp : u.path <;>
    simp [CellMono, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, hp] <;>
    repeat (first | split) <;> simp_all [CellMono]


private theorem r5Ready_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (r5Ready u) := by
  unfold r5Ready
  split
  · exact cellMono_refl u
  · exact readyGuarded_mono u


private theorem releaseEqual_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CellMono l (releaseEqual hp l r) := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [CellMono, releaseEqual, hl, hr] <;>
    repeat (first | split) <;> simp_all [CellMono]


private theorem checkL_mono {ψ : Nat} (hp : ψ > 0)
    (u : AgentState ψ) :
    CellMono u (checkSigCheckL hp u) := by
  unfold checkSigCheckL
  repeat (first | split) <;> simp_all [CellMono,checkBit]
  all_goals repeat (split <;> simp_all)
  all_goals grind


private theorem checkR_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CellMono r (checkSigCheckR hp l r) := by
  unfold checkSigCheckR
  repeat (first | split) <;> simp_all [CellMono,checkBit]
  all_goals repeat (split <;> simp_all)
  all_goals grind


private theorem setResult_view {ψ : Nat} (c : Cfg)
    (u : AgentState ψ) :
    CoreView (setResult c u) = CoreView u := by
  cases h : u.path2 <;>
    simp [setResult, preserveToken, h, checkSigSetResult,
      CoreView, view_ite]


private theorem checkSource_mono {ψ : Nat} (hp : ψ > 0)
    (c : Cfg) (l r : AgentState ψ) :
    PairMono l r (checkSource hp c l r).1 (checkSource hp c l r).2 := by
  let l0 := r5Ready l
  let r0 := r5Ready r
  have h0 : PairMono l r l0 r0 :=
    ⟨r5Ready_mono l, r5Ready_mono r⟩
  let l1 := releaseEqual hp l0 r0
  have h1 : PairMono l0 r0 l1 r0 :=
    ⟨releaseEqual_mono hp l0 r0, cellMono_refl r0⟩
  let l2 := checkSigCheckL hp l1
  have h2 : PairMono l1 r0 l2 r0 :=
    ⟨checkL_mono hp l1, cellMono_refl r0⟩
  let r1 := checkSigCheckR hp l2 r0
  have h3 : PairMono l2 r0 l2 r1 :=
    ⟨cellMono_refl l2, checkR_mono hp l2 r0⟩
  let l3 := setResult c l2
  let r2 := setResult c r1
  have h4 : PairMono l2 r1 l3 r2 :=
    ⟨cellMono_of_view (setResult_view c l2),
     cellMono_of_view (setResult_view c r1)⟩
  let out :=
    if r2.label = ⟨ψ - 1, by omega⟩ ∧ r2.state = .equal then
      (l3, { r2 with leader := true })
    else (l3, r2)
  have h5 : PairMono l3 r2 out.1 out.2 := by
    dsimp [out]
    split <;> simp [PairMono, CellMono]
  have h :=
    pairMono_trans h0
      (pairMono_trans h1
        (pairMono_trans h2
          (pairMono_trans h3
            (pairMono_trans h4 h5))))
  simpa [checkSource, r5Ready, l0, r0, l1, l2, r1, l3, r2, out]
    using h


private theorem disappear_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    PairMono l r (disappear hp l r).1 (disappear hp l r).2 := by
  unfold disappear
  repeat (first | split) <;>
    simp_all [PairMono, CellMono]
  all_goals repeat (split <;> simp_all)
  all_goals grind


private theorem releaseReadySuffix_mono {ψ : Nat}
    (l r : AgentState ψ) :
    PairMono l r (releaseReadySuffix l r).1 (releaseReadySuffix l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [PairMono, CellMono, releaseReadySuffix, hl, hr] <;>
    repeat (first | split) <;> simp_all [PairMono, CellMono]


private theorem ackTail_mono {ψ : Nat}
    (l r : AgentState ψ) :
    PairMono l r (ackTail l r).1 (ackTail l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [PairMono, CellMono, ackTail, hl, hr] <;>
    repeat (first | split) <;> simp_all [PairMono, CellMono]


private theorem repairReady_mono {ψ : Nat}
    (l r : AgentState ψ) :
    PairMono l r (repair .readyAck l r).1 (repair .readyAck l r).2 := by
  let l0 := normalizeOrphan l
  let r0 := normalizeOrphan r
  let l1 := normalizeCarrier l0
  let r1 := normalizeCarrier r0
  let q := releaseReadySuffix l1 r1
  let out := ackTail q.1 q.2
  have h0 : PairMono l r l0 r0 :=
    ⟨normalizeOrphan_mono l, normalizeOrphan_mono r⟩
  have h1 : PairMono l0 r0 l1 r1 :=
    ⟨normalizeCarrier_mono l0, normalizeCarrier_mono r0⟩
  have h2 : PairMono l1 r1 q.1 q.2 :=
    releaseReadySuffix_mono l1 r1
  have h3 : PairMono q.1 q.2 out.1 out.2 :=
    ackTail_mono q.1 q.2
  have h := pairMono_trans h0 (pairMono_trans h1 (pairMono_trans h2 h3))
  simpa [repair, l0, r0, l1, r1, q, out] using h


private theorem maintain_mono {ψ : Nat}
    (l r : AgentState ψ) :
    PairMono l r (maintain l r).1 (maintain l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain,hl,hr,PairMono,CellMono,fst_ite,snd_ite,state_ite,path_ite]
  all_goals repeat (split <;> simp_all)
  all_goals grind



private theorem completeWave_mono {ψ : Nat}
    (l r : AgentState ψ) :
    PairMono l r (completeWave l r).1 (completeWave l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [PairMono, CellMono, completeWave, hl, hr] <;>
    repeat (first | split) <;> simp_all [PairMono, CellMono]


private theorem wave_mono {ψ : Nat}
    (l r : AgentState ψ) :
    PairMono l r (wave l r).1 (wave l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [PairMono, CellMono, wave, hl, hr,
      lockedState, lockerState] <;>
    repeat (first | split) <;> simp_all [PairMono, CellMono]


private theorem dropStray_view {ψ : Nat}
    (l r : AgentState ψ) :
    CoreView (dropStray l r).1 = CoreView l ∧
    CoreView (dropStray l r).2 = CoreView r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, CoreView]


private theorem landBackward_view {ψ : Nat} (u : AgentState ψ) :
    CoreView (landBackward u) = CoreView u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landBackward, hp, ht, CoreView]


private theorem landForward_view {ψ : Nat} (κ : Nat)
    (u : AgentState ψ) :
    CoreView (landForward κ false true u) = CoreView u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht, CoreView] <;>
    repeat (first | split) <;> simp_all [CoreView]


private theorem compareLifecycle_mono {ψ : Nat} (κ : Nat)
    (l r : AgentState ψ) :
    PairMono l r
      (compareLifecycle κ l r).1
      (compareLifecycle κ l r).2 := by
  let l0 : AgentState ψ :=
    match l.path with
    | .bot => if l.state = .produce then l else { l with state := .none }
    | .some _ _ => l
  have h0 : CellMono l l0 := by
    cases hp : l.path <;>
      simp [l0, hp, CellMono] <;>
      repeat (first | split) <;> simp_all [CellMono]
  let q1 := maintain l0 r
  let q2 := completeWave q1.1 q1.2
  let q3 := wave q2.1 q2.2
  let q4 := dropStray q3.1 q3.2
  let out := (landBackward q4.1, landForward κ false true q4.2)
  have h1 : PairMono l0 r q1.1 q1.2 := maintain_mono l0 r
  have h2 : PairMono q1.1 q1.2 q2.1 q2.2 := completeWave_mono q1.1 q1.2
  have h3 : PairMono q2.1 q2.2 q3.1 q3.2 := wave_mono q2.1 q2.2
  have h4 : PairMono q3.1 q3.2 q4.1 q4.2 :=
    ⟨cellMono_of_view (dropStray_view q3.1 q3.2).1,
     cellMono_of_view (dropStray_view q3.1 q3.2).2⟩
  have h5 : PairMono q4.1 q4.2 out.1 out.2 :=
    ⟨cellMono_of_view (landBackward_view q4.1),
     cellMono_of_view (landForward_view κ q4.2)⟩
  have h :=
    pairMono_trans ⟨h0, cellMono_refl r⟩
      (pairMono_trans h1
        (pairMono_trans h2
          (pairMono_trans h3
            (pairMono_trans h4 h5))))
  change PairMono l r out.1 out.2
  exact h


private theorem suppress_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    PairMono l r
      (suppressSigResetKill hp l r).1
      (suppressSigResetKill hp l r).2 := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [PairMono, CellMono, suppressSigResetKill, suppressSigStart,
      suppressSigMoveReset, suppressSigTerminal, suppressSigEcho,
      suppressSigFinish, clearCmp, h1, h2, h3, h4,
      fst_ite, snd_ite, state_ite, path_ite] <;>
    repeat (first | split) <;> simp_all [PairMono, CellMono, clearCmp]


private theorem kernel_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (k4Kernel hp l r).1 = CoreView l ∧
    CoreView (k4Kernel hp l r).2 = CoreView r := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [CoreView, fst_ite, snd_ite, state_ite, path_ite,
    ite_self, and_self]


namespace Writer


private theorem writeActionApplyOverwrite_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (writeActionApplyOverwrite u) = CoreView u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl


private theorem writeActionApplyMoveFlip_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (writeActionApplyMoveFlip u) = CoreView u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl


private theorem moveWsigCheckLast_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (moveWsigCheckLast u) = CoreView u := by
  cases hp : u.path3 <;>
    simp [moveWsigCheckLast, hp, CoreView]


private theorem writeSeqSetWriteReady_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (writeSeqSetWriteReady u) = CoreView u := by
  cases hp : u.path3 <;>
    simp [writeSeqSetWriteReady, hp, CoreView]


private theorem writeSeqCheckBit_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (writeSeqCheckBit u) = CoreView u := by
  cases hp : u.path3 <;>
    simp [writeSeqCheckBit, hp, CoreView]


private theorem writeSeqSetWriteAct_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (writeSeqSetWriteAct u) = CoreView u := by
  cases hp : u.path3 <;>
    simp [writeSeqSetWriteAct, hp, CoreView]


private theorem writeSeqFinalR_view {ψ : Nat}
    (u : AgentState ψ) :
    CoreView (writeSeqFinalR u) = CoreView u := by
  cases hp : u.path3 <;>
    simp [writeSeqFinalR, hp, CoreView]


private theorem moveWsigCheckGenWs_view {ψ : Nat}
    (l r : AgentState ψ) :
    CoreView (moveWsigCheckGenWs l r) = CoreView r := by
  cases hp : l.path3 <;>
    simp [moveWsigCheckGenWs, hp, CoreView]


private theorem moveWsigTransfer_view {ψ : Nat}
    (l r : AgentState ψ) :
    CoreView (moveWsigTransfer l r).1 = CoreView l ∧
    CoreView (moveWsigTransfer l r).2 = CoreView r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp [moveWsigTransfer, hl, hr, CoreView, fst_ite, snd_ite, view_ite]


private theorem groupInfo_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (groupInfo hp l r).1 = CoreView l ∧
    CoreView (groupInfo hp l r).2 = CoreView r := by
  simp only [groupInfo, fst_ite, snd_ite, view_ite, CoreView,
    state_ite, path_ite, ite_self, and_self]


private theorem gensigWriteseq_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (gensigWriteseq hp l r).1 = CoreView l ∧
    CoreView (gensigWriteseq hp l r).2 = CoreView r := by
  simp only [gensigWriteseq, fst_ite, snd_ite, view_ite, CoreView,
    state_ite, path_ite, ite_self, and_self]


private theorem writeAction_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (writeAction hp l r).1 = CoreView l ∧
    CoreView (writeAction hp l r).2 = CoreView r := by
  simp only [writeAction, fst_ite, snd_ite, view_ite, CoreView,
    state_ite, path_ite, ite_self, and_self,
    (view_state (writeActionApplyOverwrite_view _)), (view_path (writeActionApplyOverwrite_view _)), (view_state (writeActionApplyMoveFlip_view _)), (view_path (writeActionApplyMoveFlip_view _))]


private theorem moveWsig_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (moveWsig hp l r).1 = CoreView l ∧
    CoreView (moveWsig hp l r).2 = CoreView r := by
  simp only [moveWsig, fst_ite, snd_ite, view_ite, CoreView,
    state_ite, path_ite, ite_self, and_self,
    (view_state (moveWsigCheckGenWs_view _ _)), (view_path (moveWsigCheckGenWs_view _ _)), (view_state (moveWsigCheckLast_view _)), (view_path (moveWsigCheckLast_view _)),
    (view_state (moveWsigTransfer_view _ _).1), (view_path (moveWsigTransfer_view _ _).1), (view_state (moveWsigTransfer_view _ _).2), (view_path (moveWsigTransfer_view _ _).2)]


private theorem writeSeq_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (writeSeq hp l r).1 = CoreView l ∧
    CoreView (writeSeq hp l r).2 = CoreView r := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare,
    writeSeqReady, writeSeqCompare, writeSeqCommands,
    fst_ite, snd_ite, view_ite, CoreView, state_ite, path_ite,
    ite_self, and_self,
    (view_state (groupInfo_view _ _ _).1), (view_path (groupInfo_view _ _ _).1), (view_state (groupInfo_view _ _ _).2), (view_path (groupInfo_view _ _ _).2),
    (view_state (gensigWriteseq_view _ _ _).1), (view_path (gensigWriteseq_view _ _ _).1), (view_state (gensigWriteseq_view _ _ _).2), (view_path (gensigWriteseq_view _ _ _).2),
    (view_state (writeAction_view _ _ _).1), (view_path (writeAction_view _ _ _).1), (view_state (writeAction_view _ _ _).2), (view_path (writeAction_view _ _ _).2),
    (view_state (moveWsig_view _ _ _).1), (view_path (moveWsig_view _ _ _).1), (view_state (moveWsig_view _ _ _).2), (view_path (moveWsig_view _ _ _).2),
    (view_state (writeSeqSetWriteReady_view _)), (view_path (writeSeqSetWriteReady_view _)), (view_state (writeSeqCheckBit_view _)), (view_path (writeSeqCheckBit_view _)),
    (view_state (writeSeqSetWriteAct_view _)), (view_path (writeSeqSetWriteAct_view _)), (view_state (writeSeqFinalR_view _)), (view_path (writeSeqFinalR_view _))]


theorem writeWithBundle_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (writeWithBundle hp l r).1 = CoreView l ∧
    CoreView (writeWithBundle hp l r).2 = CoreView r := by
  have h := writeSeq_view hp l r
  simp only [writeWithBundle, fst_ite, snd_ite, view_ite, CoreView,
    state_ite, path_ite, view_state h.1, view_path h.1, view_state h.2, view_path h.2, ite_self, and_self]


end Writer


private theorem conserve_mono {ψ : Nat}
    (l r : AgentState ψ) (q : AgentState ψ × AgentState ψ) :
    PairMono q.1 q.2
      (conserve .head l r q).1
      (conserve .head l r q).2 := by
  unfold conserve
  split
  · simp [PairMono, CellMono, replacement, clearCmp]
  · exact pairMono_refl q.1 q.2


private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by
  split <;> rfl

namespace Prefix
private def view {ψ : Nat} (u : AgentState ψ) := (u.label,u.state)
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    view (if p then a else b) = if p then view a else view b := by split <;> rfl
private theorem path4_view {ψ : Nat} (u : AgentState ψ) : view {u with path4 := none} = view u := rfl
private theorem path5_view {ψ : Nat} (u : AgentState ψ) : view {u with path5 := none} = view u := rfl

private theorem pPsi_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩) :
    view (pPsiProbeWall hp l r).1 = view l ∧ view (pPsiProbeWall hp l r).2 = view r := by
  simp [pPsiProbeWall,pPsi,fst_ite,snd_ite,view_ite,view,label_ite,state_ite,hn]

private theorem wait_views {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    view (waitSaturated hp κ l r).1 = view l ∧
    view (waitSaturated hp κ l r).2 = view r := by
  simp only [waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,waitSaturatedReset,waitSaturatedFinish]
  simp only [fst_ite,snd_ite,view_ite,view,label_ite,state_ite,ite_self,and_self]

private theorem cleanSigGenConnect_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigGenConnect u)) = (view u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem cleanSigCleanApply_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigCleanApply u)) = (view u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [view_ite, view, label_ite, state_ite]

private theorem clean3_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep3 l r).1) = (view l) ∧
    (view (cleanSigStep3 l r).2) = (view r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean4_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep4 l r).1) = (view l) ∧
    (view (cleanSigStep4 l r).2) = (view r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean5_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep5 hψ l r).1) = (view l) ∧
    (view (cleanSigStep5 hψ l r).2) = (view r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean6_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep6 hψ l r).1) = (view l) ∧
    (view (cleanSigStep6 hψ l r).2) = (view r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (cleanSig hψ l r).1) = (view l) ∧
    (view (cleanSig hψ l r).2) = (view r) := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_view, cleanSigCleanApply_view,
    (clean3_views _ _).1, (clean3_views _ _).2,
    (clean4_views _ _).1, (clean4_views _ _).2,
    (clean5_views _ _ _).1, (clean5_views _ _ _).2,
    (clean6_views _ _ _).1, (clean6_views _ _ _).2, and_self]

private theorem cleanSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (cleanSource hp l r).1 = view l ∧ view (cleanSource hp l r).2 = view r := by
  simp only [cleanSource]
  simp only [fst_ite,snd_ite,view_ite,path4_view,path5_view,cleanSigGenConnect_view,cleanSigCleanApply_view,
    (clean3_views _ _).1,(clean3_views _ _).2,(clean4_views _ _).1,(clean4_views _ _).2,
    (clean5_views _ _ _).1,(clean5_views _ _ _).2,(clean6_views _ _ _).1,(clean6_views _ _ _).2,ite_self,and_self]

private def genTail {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :=
  let q := genSigSaturatedEmit hp l r
  let q := genSigSaturatedPropagate hp q.1 q.2
  genSigSaturatedFinish hp q.1 q.2

end Prefix

private def StateMono {ψ : Nat} (l r a b : AgentState ψ) : Prop :=
  (a.state = .done → l.state = .done) ∧
  (b.state = .done → r.state = .done)

private theorem stateMono_refl {ψ : Nat} (l r : AgentState ψ) :
    StateMono l r l r := ⟨id, id⟩

private theorem stateMono_trans {ψ : Nat} {l r a b c d : AgentState ψ}
    (h₁ : StateMono l r a b) (h₂ : StateMono a b c d) :
    StateMono l r c d :=
  ⟨fun hc => h₁.1 (h₂.1 hc), fun hd => h₁.2 (h₂.2 hd)⟩

private theorem stateMono_of_pairMono {ψ : Nat} {l r a b : AgentState ψ}
    (h : PairMono l r a b) : StateMono l r a b :=
  ⟨h.1.2, h.2.2⟩

private theorem step1F_stateMono {ψ : Nat} (z : PPLLFableZDiv.Cfg)
    (l r : AgentState ψ) :
    StateMono l r
      (PPLLFableZDiv.sigMoveStep1F z l r).1
      (PPLLFableZDiv.sigMoveStep1F z l r).2 := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [StateMono, PPLLFableZDiv.sigMoveStep1F, hl, hr]
  all_goals repeat (first | split | simp_all [StateMono])

private theorem moveSourceF_stateMono {ψ : Nat}
    (hp : ψ > 0) (z : PPLLFableZDiv.Cfg)
    (l r : AgentState ψ) :
    StateMono l r
      (PPLLFableZDiv.moveSourceF hp z l r).1
      (PPLLFableZDiv.moveSourceF hp z l r).2 := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hp⟩
  let a := if l.leader = true ∨
      (r.leader = true ∧ r.label ≠ nextLabel) then clearCmp l else l
  let b := if r.leader = true then clearCmp r else r
  have hab : StateMono l r a b := by
    exact stateMono_of_pairMono ⟨(by dsimp [a]; split <;> simp [CellMono, clearCmp]),
      (by dsimp [b]; split <;> simp [CellMono, clearCmp])⟩
  let s := if a.state = .done then (a, b)
    else PPLLFableZDiv.sigMoveStep1F z a b
  have hs : StateMono a b s.1 s.2 := by
    dsimp [s]
    split
    · exact stateMono_refl a b
    · exact step1F_stateMono z a b
  let t := moveTokens s.1 s.2
  have ht : StateMono s.1 s.2 t.1 t.2 :=
    stateMono_of_pairMono
      ⟨cellMono_of_view (moveTokens_view s.1 s.2).1,
       cellMono_of_view (moveTokens_view s.1 s.2).2⟩
  let w := leaderWall t.1 t.2
  have hw : StateMono t.1 t.2 w.1 w.2 :=
    stateMono_of_pairMono (leaderWall_mono t.1 t.2)
  let x := sigMoveApplyControlConsume hp w.1
  let y := sigMoveApplyControlConsume hp w.2
  have hxy : StateMono w.1 w.2 x y :=
    stateMono_of_pairMono ⟨control_mono hp w.1, control_mono hp w.2⟩
  let x' :=
    if y.state = .depart ∧ x.label.val < ψ - 1 ∧
        x.state = .CHECK_ready then
      { x with state := .depart }
    else x
  have hx : StateMono x y x' y := by
    exact stateMono_of_pairMono
      ⟨(by dsimp [x']; split <;> simp [CellMono]), cellMono_refl y⟩
  have hfin : StateMono l r x' y :=
    stateMono_trans hab
      (stateMono_trans hs
        (stateMono_trans ht
          (stateMono_trans hw (stateMono_trans hxy hx))))
  simpa [PPLLFableZDiv.moveSourceF, nextLabel, a, b, s, t, w, x, y, x']
    using hfin

private theorem genTail_labels {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    (Prefix.genTail hp l r).1.label = l.label ∧
    (Prefix.genTail hp l r).2.label = r.label := by
  simp only [Prefix.genTail, genSigSaturatedEmit,
    genSigSaturatedPropagate, genSigSaturatedFinish,
    fst_ite, snd_ite, label_ite, ite_self, and_self]

private theorem genOverwrite_labels {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1.label = l.label ∧
    (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2.label = r.label := by
  let w := waitSaturated hp κ l r
  have hw := Prefix.wait_views hp κ l r
  simp only [Prefix.view, Prod.mk.injEq] at hw
  let a := if w.1.leader = false ∧ w.1.label = ⟨0, hp⟩ ∧
      w.1.wait = false ∧ w.1.path = .bot then
      PPLLFableZDiv.wipeProduce w.1 else w.1
  let b := if w.2.label ≠ ⟨0, hp⟩ ∧ a.state = .produce ∧
      (w.2.path = .bot ∨ (w.2.state ≠ .produce ∧ w.2.state ≠ .done)) then
      PPLLFableZDiv.wipeProduce w.2 else w.2
  have hal : a.label = l.label := by
    dsimp [a]; split
    · simpa only [PPLLFableZDiv.wipeProduce] using hw.1.1
    · exact hw.1.1
  have hbl : b.label = r.label := by
    dsimp [b]; split
    · simpa only [PPLLFableZDiv.wipeProduce] using hw.2.1
    · exact hw.2.1
  have ht := genTail_labels hp a b
  have hgen : PPLLFableZDiv.genSigOverwrite hp κ true 0 l r =
      Prefix.genTail hp a b := by
    simp [PPLLFableZDiv.genSigOverwrite, Prefix.genTail, a, b, w]
  rw [hgen]
  exact ⟨ht.1.trans hal, ht.2.trans hbl⟩

private theorem releaseSource_stateMono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    StateMono l r (releaseSource hp l r).1 (releaseSource hp l r).2 := by
  unfold releaseSource StateMono
  split <;> simp

private def throughRelease {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hp l r
  let q := PPLLFableZDiv.genSigOverwrite hp κ true 0 q.1 q.2
  let q := cleanSource hp q.1 q.2
  releaseSource hp q.1 q.2

private def afterRelease {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (inputL inputR l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := eliminateSig hp l r
  let q := PPLLFableZDiv.moveSourceF hp sourceCfg q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  let q := checkSource hp c q.1 q.2
  let q := disappear hp q.1 q.2
  let q := repair .readyAck q.1 q.2
  let q := compareLifecycle κ q.1 q.2
  let q := suppressSigResetKill hp q.1 q.2
  let q := k4Kernel hp q.1 q.2
  let q := writeWithBundle hp q.1 q.2
  conserve .head inputL inputR q

private theorem afterRelease_stateMono {ψ : Nat} (hp : ψ > 0)
    (κ : Nat) (c : Cfg) (inputL inputR l r : AgentState ψ) :
    StateMono l r
      (afterRelease hp κ c inputL inputR l r).1
      (afterRelease hp κ c inputL inputR l r).2 := by
  let d := eliminateSig hp l r
  have hd : StateMono l r d.1 d.2 :=
    stateMono_of_pairMono (eliminate_mono hp l r)
  let e := PPLLFableZDiv.moveSourceF hp sourceCfg d.1 d.2
  have he : StateMono l r e.1 e.2 :=
    stateMono_trans hd (moveSourceF_stateMono hp sourceCfg d.1 d.2)
  let f := (dropStale e.1, dropStale e.2)
  have hf : StateMono l r f.1 f.2 :=
    stateMono_trans he (stateMono_of_pairMono
      ⟨drop_mono e.1, drop_mono e.2⟩)
  let j := preCheckReset f.1 f.2
  have hj : StateMono l r j.1 j.2 :=
    stateMono_trans hf (stateMono_of_pairMono (precheck_mono f.1 f.2))
  let n := (normalizeReady j.1, normalizeReady j.2)
  have hn : StateMono l r n.1 n.2 :=
    stateMono_trans hj (stateMono_of_pairMono
      ⟨normalizeReady_mono j.1, normalizeReady_mono j.2⟩)
  let ch := checkSource hp c n.1 n.2
  have hch : StateMono l r ch.1 ch.2 :=
    stateMono_trans hn (stateMono_of_pairMono (checkSource_mono hp c n.1 n.2))
  let ds := disappear hp ch.1 ch.2
  have hds : StateMono l r ds.1 ds.2 :=
    stateMono_trans hch (stateMono_of_pairMono (disappear_mono hp ch.1 ch.2))
  let rr := repair .readyAck ds.1 ds.2
  have hrr : StateMono l r rr.1 rr.2 :=
    stateMono_trans hds (stateMono_of_pairMono (repairReady_mono ds.1 ds.2))
  let cp := compareLifecycle κ rr.1 rr.2
  have hcp : StateMono l r cp.1 cp.2 :=
    stateMono_trans hrr (stateMono_of_pairMono (compareLifecycle_mono κ rr.1 rr.2))
  let s := suppressSigResetKill hp cp.1 cp.2
  have hs : StateMono l r s.1 s.2 :=
    stateMono_trans hcp (stateMono_of_pairMono (suppress_mono hp cp.1 cp.2))
  let k := k4Kernel hp s.1 s.2
  have hk : StateMono l r k.1 k.2 :=
    stateMono_trans hs (stateMono_of_pairMono
      ⟨cellMono_of_view (kernel_view hp s.1 s.2).1,
       cellMono_of_view (kernel_view hp s.1 s.2).2⟩)
  let w := writeWithBundle hp k.1 k.2
  have hw : StateMono l r w.1 w.2 :=
    stateMono_trans hk (stateMono_of_pairMono
      ⟨cellMono_of_view (Writer.writeWithBundle_view hp k.1 k.2).1,
       cellMono_of_view (Writer.writeWithBundle_view hp k.1 k.2).2⟩)
  have ho : StateMono l r
      (conserve .head inputL inputR w).1
      (conserve .head inputL inputR w).2 :=
    stateMono_trans hw (stateMono_of_pairMono (conserve_mono inputL inputR w))
  simpa only [afterRelease, d, e, f, j, n, ch, ds, rr, cp, s, k, w] using ho

private theorem pipeline_reverse_factor {ψ : Nat} (hp : ψ > 0)
    (κ : Nat) (c : Cfg) (l r : AgentState ψ) :
    pipeline hp κ c l r =
      let q := throughRelease hp κ l r
      afterRelease hp κ c l r q.1 q.2 := by
  rfl

def ForwardEdge {ψ : Nat} (l r : AgentState ψ) : Prop :=
  0 < l.label.val ∧ l.label.val + 1 = r.label.val

private theorem propagate_forward {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hl : l.label ≠ ⟨ψ - 1, by omega⟩) :
    let q := genSigSaturatedPropagate hp l r
    q.2.state = .done →
      q.1.state ≠ .produce ∧ (l.state ≠ .done → q.1.state ≠ .done) := by
  by_cases h : l.state = .produce ∧ r.state = .done
  · have hc : l.label ≠ ⟨ψ - 1, by omega⟩ ∧
        l.state = .produce ∧ r.state = .done := ⟨hl, h⟩
    simp [genSigSaturatedPropagate, hc]
  · have hc : ¬(l.label ≠ ⟨ψ - 1, by omega⟩ ∧
        l.state = .produce ∧ r.state = .done) := by
      intro hx
      exact h hx.2
    simp only [genSigSaturatedPropagate, if_neg hc]
    intro hr
    constructor
    · intro hp'; exact h ⟨hp', hr⟩
    · exact id

private theorem genTail_forward {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ)
    (hl : l.label ≠ ⟨ψ - 1, by omega⟩)
    (h0 : l.label ≠ ⟨0, hp⟩) :
    let q := Prefix.genTail hp l r
    q.2.state = .done →
      q.1.state ≠ .produce ∧ (l.state ≠ .done → q.1.state ≠ .done) := by
  let e := genSigSaturatedEmit hp l r
  have hel : e.1 = l := by simp [e, genSigSaturatedEmit]
  let p := genSigSaturatedPropagate hp e.1 e.2
  have hpl : p.1.label = l.label := by
    simp only [p, genSigSaturatedPropagate, fst_ite, label_ite,
      ite_self, hel]
  have hprop := propagate_forward hp e.1 e.2 (by simpa [hel] using hl)
  have hfin : genSigSaturatedFinish hp p.1 p.2 = p := by
    simp [genSigSaturatedFinish, hpl, h0]
  change (genSigSaturatedFinish hp p.1 p.2).2.state = .done →
    (genSigSaturatedFinish hp p.1 p.2).1.state ≠ .produce ∧
      (l.state ≠ .done →
        (genSigSaturatedFinish hp p.1 p.2).1.state ≠ .done)
  rw [hfin]
  simpa only [p, hel] using hprop

private theorem gen_forward {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ)
    (hl : l.label ≠ ⟨ψ - 1, by omega⟩)
    (h0 : l.label ≠ ⟨0, hp⟩) :
    let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 l r
    g.2.state = .done →
      g.1.state ≠ .produce ∧ (l.state ≠ .done → g.1.state ≠ .done) := by
  let w := waitSaturated hp κ l r
  have hw := Prefix.wait_views hp κ l r
  simp only [Prefix.view, Prod.mk.injEq] at hw
  let a := if w.1.leader = false ∧ w.1.label = ⟨0, hp⟩ ∧
      w.1.wait = false ∧ w.1.path = .bot then
      PPLLFableZDiv.wipeProduce w.1 else w.1
  let b := if w.2.label ≠ ⟨0, hp⟩ ∧ a.state = .produce ∧
      (w.2.path = .bot ∨ (w.2.state ≠ .produce ∧ w.2.state ≠ .done)) then
      PPLLFableZDiv.wipeProduce w.2 else w.2
  have hwll : w.1.label = l.label := hw.1.1
  have hwls : w.1.state = l.state := hw.1.2
  have ha : a = w.1 := by
    simp [a, hwll, h0]
  have hal : a.label = l.label := by simpa [ha] using hwll
  have has : a.state = l.state := by simpa [ha] using hwls
  have ht := genTail_forward hp a b (by simpa [hal] using hl)
    (by simpa [hal] using h0)
  have hgen : PPLLFableZDiv.genSigOverwrite hp κ true 0 l r =
      Prefix.genTail hp a b := by
    simp [PPLLFableZDiv.genSigOverwrite, Prefix.genTail, a, b, w]
  change (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2.state = .done →
    (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1.state ≠ .produce ∧
      (l.state ≠ .done →
        (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1.state ≠ .done)
  rw [hgen]
  intro hrd
  have h := ht hrd
  exact ⟨h.1, fun hld => h.2 (by simpa [has] using hld)⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem throughRelease_forward {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hedge : ForwardEdge l r)
    (hld : l.state ≠ .done) :
    (throughRelease hp κ l r).2.state ≠ .done := by
  obtain ⟨hpos, hsucc⟩ := hedge
  have hn : r.label = ⟨(l.label.val + 1)%ψ, Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    change r.label.val = (l.label.val + 1)%ψ
    have hlt : l.label.val + 1 < ψ := by
      rw [hsucc]
      exact r.label.isLt
    rw [Nat.mod_eq_of_lt hlt]
    exact hsucc.symm
  have hl : l.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h
    have hv : l.label.val = ψ - 1 := by simpa using congrArg Fin.val h
    have bound := r.label.isLt
    omega
  have h0 : l.label ≠ ⟨0, hp⟩ := by
    intro h
    have hv : l.label.val = 0 := by simpa using congrArg Fin.val h
    omega
  have hr0 : r.label ≠ ⟨0, hp⟩ := by
    intro h
    have hv : r.label.val = 0 := by simpa using congrArg Fin.val h
    omega
  let p := pPsiProbeWall hp l r
  have hpview := Prefix.pPsi_views hp l r hn
  simp only [Prefix.view, Prod.mk.injEq] at hpview
  have hpl : p.1.label = l.label := hpview.1.1
  have hpr : p.2.label = r.label := hpview.2.1
  have hpsl : p.1.state = l.state := hpview.1.2
  let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
  have hg := gen_forward hp κ p.1 p.2
    (by simpa [hpl] using hl) (by simpa [hpl] using h0)
  have hglabel := genOverwrite_labels hp κ p.1 p.2
  have hgl : g.1.label = l.label := hglabel.1.trans hpl
  have hgr : g.2.label = r.label := hglabel.2.trans hpr
  let a := cleanSource hp g.1 g.2
  have hac := Prefix.cleanSource_views hp g.1 g.2
  simp only [Prefix.view, Prod.mk.injEq] at hac
  have hasl : a.1.state = g.1.state := hac.1.2
  have hasr : a.2.state = g.2.state := hac.2.2
  have hal : a.1.label = l.label := hac.1.1.trans hgl
  have har : a.2.label = r.label := hac.2.1.trans hgr
  have ar0 : a.2.label ≠ ⟨0, hp⟩ := by simpa [har] using hr0
  have acon : a.1.label.val + 1 = a.2.label.val := by
    simpa [hal, har] using hsucc
  let b := releaseSource hp a.1 a.2
  intro hbd
  change b.2.state = .done at hbd
  have hrel := releaseSource_stateMono hp a.1 a.2
  have had : a.2.state = .done := hrel.2 hbd
  have hgd : g.2.state = .done := hasr ▸ had
  have hgn := hg hgd
  have hanp : a.1.state ≠ .produce := by simpa [hasl] using hgn.1
  have hand : a.1.state ≠ .done := by
    have hpd : p.1.state ≠ .done := by simpa [hpsl] using hld
    simpa [hasl] using hgn.2 hpd
  change (releaseSource hp a.1 a.2).2.state = .done at hbd
  simp [releaseSource, had, ar0, acon, hanp, hand] at hbd

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem forward_right_done_origin {ψ : Nat} (hp : ψ > 0)
    (κ : Nat) (c : Cfg) (l r : AgentState ψ)
    (hedge : ForwardEdge l r) :
    let q := pipeline hp κ c l r
    q.2.state = .done → l.state = .done := by
  let b := throughRelease hp κ l r
  let q := afterRelease hp κ c l r b.1 b.2
  have hs := afterRelease_stateMono hp κ c l r b.1 b.2
  rw [pipeline_reverse_factor]
  change (afterRelease hp κ c l r b.1 b.2).2.state = .done →
    l.state = .done
  intro hqdone
  by_cases hld : l.state = .done
  · exact hld
  · have hb := throughRelease_forward hp κ l r hedge hld
    exact False.elim (hb (hs.2 hqdone))

#check @forward_right_done_origin
#print axioms forward_right_done_origin

end PPLLAstraR5Repair.ForwardDone
