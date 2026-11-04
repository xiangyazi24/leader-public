import Leader.Wu.ZeroDivisible.CheckRepair

/-!
# Boundary service entry and pair-hole persistence

The boundary prefix frames states and token slots while allowing CLEAN to
erase paths. After that cut, an existing pair-hole cannot disappear.
Generic stage proofs are copied from the frozen PrepRows module.
-/
namespace PPLLAstraR5Repair


namespace ServiceEntry
namespace NoAlloc


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


/-- A cell may keep or delete its path. Any output produce must already
have been present on that same input cell. -/
private def CellMono {ψ : Nat} (before after : AgentState ψ) : Prop :=
  (after.path = before.path ∨ after.path = .bot) ∧
  (after.state = .produce → before.state = .produce)


private def PairMono {ψ : Nat}
    (l r l' r' : AgentState ψ) : Prop :=
  CellMono l l' ∧ CellMono r r'


/-- Once an endpoint hole appears, only existence of a local hole is tracked.
Otherwise both original paths stay on their original holders, without produce. -/
private def FrameOrHole {ψ : Nat}
    (l0 r0 l r : AgentState ψ) : Prop :=
  l.path = .bot ∨ r.path = .bot ∨
    (l.path = l0.path ∧ r.path = r0.path ∧
      l.state ≠ .produce ∧ r.state ≠ .produce)


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


private theorem frameOrHole_mono {ψ : Nat}
    {l0 r0 l r l' r' : AgentState ψ}
    (h : FrameOrHole l0 r0 l r)
    (hm : PairMono l r l' r') :
    FrameOrHole l0 r0 l' r' := by
  rcases h with hl | hr | hf
  · rcases hm.1.1 with hp | hp
    · exact Or.inl (hp.trans hl)
    · exact Or.inl hp
  · rcases hm.2.1 with hp | hp
    · exact Or.inr (Or.inl (hp.trans hr))
    · exact Or.inr (Or.inl hp)
  · rcases hm.1.1 with hlp | hlbot
    · rcases hm.2.1 with hrp | hrbot
      · exact Or.inr (Or.inr
          ⟨hlp.trans hf.1, hrp.trans hf.2.1,
            fun hp => hf.2.2.1 (hm.1.2 hp),
            fun hp => hf.2.2.2 (hm.2.2 hp)⟩)
      · exact Or.inr (Or.inl hrbot)
    · exact Or.inl hlbot


private theorem cleanConnect_view {ψ : Nat} (u : AgentState ψ) :
    CoreView (cleanSigGenConnect u) = CoreView u := by
  cases h : u.path <;>
    simp [cleanSigGenConnect, h, CoreView]


private theorem clean3_view {ψ : Nat} (l r : AgentState ψ) :
    CoreView (cleanSigStep3 l r).1 = CoreView l ∧
    CoreView (cleanSigStep3 l r).2 = CoreView r := by
  cases h : r.path4 <;> cases hp : l.path <;>
    simp [cleanSigStep3, h, hp, CoreView, fst_ite, snd_ite, view_ite]


private theorem clean4_view {ψ : Nat} (l r : AgentState ψ) :
    CoreView (cleanSigStep4 l r).1 = CoreView l ∧
    CoreView (cleanSigStep4 l r).2 = CoreView r := by
  cases h : l.path5 <;> cases hp : r.path <;>
    simp [cleanSigStep4, h, hp, CoreView, fst_ite, snd_ite, view_ite]


private theorem clean5_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (cleanSigStep5 hp l r).1 = CoreView l ∧
    CoreView (cleanSigStep5 hp l r).2 = CoreView r := by
  cases h : r.path4 <;>
    simp [cleanSigStep5, h, CoreView, fst_ite, snd_ite, view_ite]


private theorem clean6_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (cleanSigStep6 hp l r).1 = CoreView l ∧
    CoreView (cleanSigStep6 hp l r).2 = CoreView r := by
  cases h : l.path5 <;>
    simp [cleanSigStep6, h, CoreView, fst_ite, snd_ite, view_ite]


private theorem cleanApply_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (cleanSigCleanApply u) := by
  cases hp : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp [CellMono, cleanSigCleanApply, hp, h4, h5] <;>
    (repeat split) <;> try simp_all [CellMono]
  all_goals grind


private def cleanCore {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let isCmd (t : Option (Int × Nat)) : Bool :=
    match t with
    | some (lbl, _) => decide (lbl = (-1 : Int))
    | none => false
  let l := cleanSigGenConnect l
  let r := cleanSigGenConnect r
  let q := cleanSigStep3 l r
  let q := cleanSigStep4 q.1 q.2
  let q := if isCmd q.1.path4 then (q.1, { q.2 with path4 := none })
    else cleanSigStep5 hp q.1 q.2
  if isCmd q.2.path5 then ({ q.1 with path5 := none }, q.2)
  else cleanSigStep6 hp q.1 q.2


private theorem cleanCore_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (cleanCore hp l r).1 = CoreView l ∧
    CoreView (cleanCore hp l r).2 = CoreView r := by
  simp only [cleanCore, fst_ite, snd_ite, view_ite,
    (view_state (cleanConnect_view _)), (view_path (cleanConnect_view _)),
    (view_state (clean3_view _ _).1), (view_path (clean3_view _ _).1), (view_state (clean3_view _ _).2), (view_path (clean3_view _ _).2),
    (view_state (clean4_view _ _).1), (view_path (clean4_view _ _).1), (view_state (clean4_view _ _).2), (view_path (clean4_view _ _).2),
    (view_state (clean5_view hp _ _).1), (view_path (clean5_view hp _ _).1), (view_state (clean5_view hp _ _).2), (view_path (clean5_view hp _ _).2),
    (view_state (clean6_view hp _ _).1), (view_path (clean6_view hp _ _).1), (view_state (clean6_view hp _ _).2), (view_path (clean6_view hp _ _).2),
    CoreView, state_ite, path_ite, ite_self, and_self]


private theorem cleanSource_factor {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    cleanSource hp l r =
      (cleanSigCleanApply (cleanCore hp l r).1,
       cleanSigCleanApply (cleanCore hp l r).2) := by
  rfl


private theorem cleanSource_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    PairMono l r (cleanSource hp l r).1 (cleanSource hp l r).2 := by
  rw [cleanSource_factor]
  have hc := cleanCore_view hp l r
  exact ⟨
    cellMono_trans (cellMono_of_view hc.1) (cleanApply_mono _),
    cellMono_trans (cellMono_of_view hc.2) (cleanApply_mono _)⟩


private theorem releaseSource_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    PairMono l r (releaseSource hp l r).1 (releaseSource hp l r).2 := by
  unfold PairMono CellMono releaseSource
  split <;> simp


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


private theorem step1F_frameOrHole {ψ : Nat}
    (z : PPLLFableZDiv.Cfg)
    (l0 r0 l r : AgentState ψ)
    (h : FrameOrHole l0 r0 l r) :
    FrameOrHole l0 r0
      (PPLLFableZDiv.sigMoveStep1F z l r).1
      (PPLLFableZDiv.sigMoveStep1F z l r).2 := by
  cases hl : l.path with
  | bot =>
      simp [PPLLFableZDiv.sigMoveStep1F, hl, FrameOrHole]
  | some ll lb =>
      cases hr : r.path with
      | some rl rb =>
          simpa [PPLLFableZDiv.sigMoveStep1F, hl, hr] using h
      | bot =>
          simp only [PPLLFableZDiv.sigMoveStep1F, hl, hr]
          repeat (split <;> simp_all [FrameOrHole, hl, hr])
          all_goals grind [FrameOrHole]


private theorem moveSourceF_frameOrHole {ψ : Nat}
    (hp : ψ > 0) (z : PPLLFableZDiv.Cfg)
    (l0 r0 l r : AgentState ψ)
    (h : FrameOrHole l0 r0 l r) :
    FrameOrHole l0 r0
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
  have h0 : FrameOrHole l0 r0 a b :=
    frameOrHole_mono h ⟨ha, hb⟩


  let s := if a.state = .done then (a, b)
    else PPLLFableZDiv.sigMoveStep1F z a b
  have hs : FrameOrHole l0 r0 s.1 s.2 := by
    dsimp [s]
    split
    · exact h0
    · exact step1F_frameOrHole z l0 r0 a b h0


  let t := moveTokens s.1 s.2
  have ht : FrameOrHole l0 r0 t.1 t.2 := by
    exact frameOrHole_mono hs
      ⟨cellMono_of_view (moveTokens_view s.1 s.2).1,
       cellMono_of_view (moveTokens_view s.1 s.2).2⟩


  let w := leaderWall t.1 t.2
  have hw : FrameOrHole l0 r0 w.1 w.2 :=
    frameOrHole_mono ht (leaderWall_mono t.1 t.2)


  let x := sigMoveApplyControlConsume hp w.1
  let y := sigMoveApplyControlConsume hp w.2
  have hxy : FrameOrHole l0 r0 x y := by
    exact frameOrHole_mono hw
      ⟨control_mono hp w.1, control_mono hp w.2⟩


  let x' :=
    if y.state = .depart ∧ x.label.val < ψ - 1 ∧
        x.state = .CHECK_ready then
      { x with state := .depart }
    else x
  have hx : CellMono x x' := by
    dsimp [x']
    split <;> simp [CellMono]
  have hfin : FrameOrHole l0 r0 x' y :=
    frameOrHole_mono hxy ⟨hx, cellMono_refl y⟩


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


end NoAlloc

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
set_option autoImplicit false
set_option linter.unusedSimpArgs false

private def Hole {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.path = .bot ∨ q.2.path = .bot

/-- Full own paths, token absence, physical labels and exact main states.
Payloads are arbitrary naturals; this does not identify them with resident bits. -/
private def Shape {ψ : Nat} (i j bL bR : Nat) (sL sR : MainState)
    (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.label.val = i ∧ q.2.label.val = j ∧
  q.1.path = .some i bL ∧ q.2.path = .some j bR ∧
  q.1.path2 = none ∧ q.2.path2 = none ∧
  q.1.state = sL ∧ q.2.state = sR ∧
  q.1.leader = false ∧ q.2.leader = false

private def snap {ψ : Nat} (u : AgentState ψ) :=
  (u.label,u.leader,u.state,u.path,u.path2)
private theorem snap_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    snap (if p then a else b) = if p then snap a else snap b := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
private theorem path2_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
attribute [local simp] NoAlloc.fst_ite NoAlloc.snd_ite NoAlloc.state_ite NoAlloc.path_ite
  snap_ite label_ite leader_ite path2_ite

private theorem shape_snap {ψ : Nat} {i j bL bR : Nat} {sL sR : MainState}
    {l r a b : AgentState ψ} (h : Shape i j bL bR sL sR (l,r))
    (ha : snap a = snap l) (hb : snap b = snap r) :
    Shape i j bL bR sL sR (a,b) := by
  simp only [snap,Prod.mk.injEq] at ha hb
  simp_all [Shape]

private theorem pprime_snap {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩) :
    snap (pPsiProbeWall hp l r).1 = snap l ∧
    snap (pPsiProbeWall hp l r).2 = snap r := by
  simp [pPsiProbeWall,pPsi,NoAlloc.fst_ite,NoAlloc.snd_ite,snap_ite,snap,
    label_ite,leader_ite,NoAlloc.state_ite,NoAlloc.path_ite,path2_ite,hn]

private theorem wait_snap {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    snap (waitSaturated hp κ l r).1 = snap l ∧
    snap (waitSaturated hp κ l r).2 = snap r := by
  simp only [waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,waitSaturatedReset,waitSaturatedFinish]
  simp only [NoAlloc.fst_ite,NoAlloc.snd_ite,snap_ite,snap,label_ite,leader_ite,
    NoAlloc.state_ite,NoAlloc.path_ite,path2_ite,ite_self,and_self]

private theorem gen_snap {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hl : l.label ≠ ⟨0,hp⟩) (hls : l.state ≠ .produce) (hrs : r.state ≠ .produce) :
    snap (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1 = snap l ∧
    snap (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2 = snap r := by
  have hw := wait_snap hp κ l r
  simp only [snap,Prod.mk.injEq] at hw
  simp only [PPLLFableZDiv.genSigOverwrite]
  generalize he : waitSaturated hp κ l r = q at *
  have hl' : q.1.label ≠ ⟨0,hp⟩ := by rw [hw.1.1]; exact hl
  have hls' : q.1.state ≠ .produce := by rw [hw.1.2.2.1]; exact hls
  have hrs' : q.2.state ≠ .produce := by rw [hw.2.2.2.1]; exact hrs
  simp [hl',hls',hrs',genSigSaturatedEmit,genSigSaturatedPropagate,genSigSaturatedFinish,
    snap,hw.1.1,hw.1.2.1,hw.1.2.2.1,hw.1.2.2.2.1,hw.1.2.2.2.2,
    hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2.1,hw.2.2.2.2.2,hl,hls,hrs]

private theorem gen_full_snap {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done) (hrs : r.state ≠ .produce) :
    snap (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1 = snap l ∧
    snap (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2 = snap r := by
  have hw := wait_snap hp κ l r
  simp only [snap,Prod.mk.injEq] at hw
  simp only [PPLLFableZDiv.genSigOverwrite]
  generalize he : waitSaturated hp κ l r = q at *
  have hlp' : q.1.path ≠ .bot := by rw [hw.1.2.2.2.1]; exact hlp
  have hrp' : q.2.path ≠ .bot := by rw [hw.2.2.2.2.1]; exact hrp
  have hls' : q.1.state ≠ .produce := by rw [hw.1.2.2.1]; exact hls
  have hld' : q.1.state ≠ .done := by rw [hw.1.2.2.1]; exact hld
  have hrs' : q.2.state ≠ .produce := by rw [hw.2.2.2.1]; exact hrs
  simp [hlp',hrp',hls',hld',hrs',genSigSaturatedEmit,genSigSaturatedPropagate,genSigSaturatedFinish,
    snap,hw.1.1,hw.1.2.1,hw.1.2.2.1,hw.1.2.2.2.1,hw.1.2.2.2.2,
    hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2.1,hw.2.2.2.2.2,hlp,hrp,hls,hld,hrs]

namespace Clean
private def keep {ψ : Nat} (u : AgentState ψ) := (u.label,u.leader,u.state,u.path2)
private theorem keep_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    keep (if p then a else b) = if p then keep a else keep b := by split <;> rfl
private theorem path4_keep {ψ : Nat} (u : AgentState ψ) : keep {u with path4 := none} = keep u := rfl
private theorem path5_keep {ψ : Nat} (u : AgentState ψ) : keep {u with path5 := none} = keep u := rfl
private theorem cleanSigGenConnect_keep {ψ : Nat} (u : AgentState ψ) :
    (keep (cleanSigGenConnect u)) = (keep u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [NoAlloc.fst_ite, NoAlloc.snd_ite, keep_ite, keep, label_ite, NoAlloc.state_ite]

private theorem cleanSigCleanApply_keep {ψ : Nat} (u : AgentState ψ) :
    (keep (cleanSigCleanApply u)) = (keep u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [keep_ite, keep, label_ite, NoAlloc.state_ite]

private theorem clean3_keeps {ψ : Nat} (l r : AgentState ψ) :
    (keep (cleanSigStep3 l r).1) = (keep l) ∧
    (keep (cleanSigStep3 l r).2) = (keep r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [NoAlloc.fst_ite, NoAlloc.snd_ite, keep_ite, keep, label_ite, NoAlloc.state_ite]

private theorem clean4_keeps {ψ : Nat} (l r : AgentState ψ) :
    (keep (cleanSigStep4 l r).1) = (keep l) ∧
    (keep (cleanSigStep4 l r).2) = (keep r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [NoAlloc.fst_ite, NoAlloc.snd_ite, keep_ite, keep, label_ite, NoAlloc.state_ite]

private theorem clean5_keeps {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (keep (cleanSigStep5 hψ l r).1) = (keep l) ∧
    (keep (cleanSigStep5 hψ l r).2) = (keep r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [NoAlloc.fst_ite, NoAlloc.snd_ite, keep_ite, keep, label_ite, NoAlloc.state_ite]

private theorem clean6_keeps {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (keep (cleanSigStep6 hψ l r).1) = (keep l) ∧
    (keep (cleanSigStep6 hψ l r).2) = (keep r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [NoAlloc.fst_ite, NoAlloc.snd_ite, keep_ite, keep, label_ite, NoAlloc.state_ite]

private theorem clean_keeps {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (keep (cleanSig hψ l r).1) = (keep l) ∧
    (keep (cleanSig hψ l r).2) = (keep r) := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_keep, cleanSigCleanApply_keep,
    (clean3_keeps _ _).1, (clean3_keeps _ _).2,
    (clean4_keeps _ _).1, (clean4_keeps _ _).2,
    (clean5_keeps _ _ _).1, (clean5_keeps _ _ _).2,
    (clean6_keeps _ _ _).1, (clean6_keeps _ _ _).2, and_self]

private theorem cleanSource_keeps {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    keep (cleanSource hp l r).1 = keep l ∧ keep (cleanSource hp l r).2 = keep r := by
  simp only [cleanSource]
  simp only [NoAlloc.fst_ite,NoAlloc.snd_ite,keep_ite,path4_keep,path5_keep,cleanSigGenConnect_keep,cleanSigCleanApply_keep,
    (clean3_keeps _ _).1,(clean3_keeps _ _).2,(clean4_keeps _ _).1,(clean4_keeps _ _).2,
    (clean5_keeps _ _ _).1,(clean5_keeps _ _ _).2,(clean6_keeps _ _ _).1,(clean6_keeps _ _ _).2,ite_self,and_self]

private theorem clean_snap {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (h : ¬ Hole (cleanSource hp l r)) :
    snap (cleanSource hp l r).1 = snap l ∧ snap (cleanSource hp l r).2 = snap r := by
  have hk := cleanSource_keeps hp l r
  have hm := NoAlloc.cleanSource_mono hp l r
  simp only [keep,Prod.mk.injEq] at hk
  have hpl : (cleanSource hp l r).1.path = l.path := hm.1.1.resolve_right (fun he => h (Or.inl he))
  have hpr : (cleanSource hp l r).2.path = r.path := hm.2.1.resolve_right (fun he => h (Or.inr he))
  simp only [snap,Prod.mk.injEq]
  exact ⟨⟨hk.1.1,hk.1.2.1,hk.1.2.2.1,hpl,hk.1.2.2.2⟩,
    ⟨hk.2.1,hk.2.2.1,hk.2.2.2.1,hpr,hk.2.2.2.2⟩⟩
end Clean

namespace Tail
private def core {ψ : Nat} (u : AgentState ψ) := (u.label,u.state,u.path,u.path2)
private theorem view_label {ψ : Nat} {a b : AgentState ψ} (h : core a = core b) : a.label = b.label := congrArg Prod.fst h
private theorem view_state {ψ : Nat} {a b : AgentState ψ} (h : core a = core b) : a.state = b.state := congrArg (fun x => x.2.1) h
private theorem view_path {ψ : Nat} {a b : AgentState ψ} (h : core a = core b) : a.path = b.path := congrArg (fun x => x.2.2.1) h
private theorem view_path2 {ψ : Nat} {a b : AgentState ψ} (h : core a = core b) : a.path2 = b.path2 := congrArg (fun x => x.2.2.2) h
private theorem core_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    core (if p then a else b) = if p then core a else core b := by split <;> rfl
attribute [local simp] core_ite
private def Mono {ψ : Nat} (a b : AgentState ψ) := b.path = .bot ∨ core b = core a
private def PairMono {ψ : Nat} (a b : AgentState ψ × AgentState ψ) :=
  Mono a.1 b.1 ∧ Mono a.2 b.2
private theorem mono_trans {ψ : Nat} {a b c : AgentState ψ} (h : Mono a b) (k : Mono b c) :
    Mono a c := by
  rcases k with kc | kc
  · exact Or.inl kc
  · rcases h with hb | hb
    · left
      have he := congrArg (fun x => x.2.2.1) kc
      exact he.trans hb
    · exact Or.inr (kc.trans hb)
private theorem pair_trans {ψ : Nat} {a b c : AgentState ψ × AgentState ψ}
    (h : PairMono a b) (k : PairMono b c) : PairMono a c :=
  ⟨mono_trans h.1 k.1,mono_trans h.2 k.2⟩
private theorem suppress_mono {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    PairMono (l,r) (suppressSigResetKill hp l r) := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [PairMono,Mono,core,suppressSigResetKill,suppressSigStart,
      suppressSigMoveReset,suppressSigTerminal,suppressSigEcho,suppressSigFinish,
      clearCmp,h1,h2,h3,h4] <;>
    repeat (first | split) <;> simp_all [PairMono,Mono,core,clearCmp]

private theorem kernel_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (k4Kernel hp l r).1 = core l ∧
    core (k4Kernel hp l r).2 = core r := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [core, NoAlloc.fst_ite, NoAlloc.snd_ite, NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite,
    ite_self, and_self]


namespace Writer


private theorem writeActionApplyOverwrite_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeActionApplyOverwrite u) = core u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl


private theorem writeActionApplyMoveFlip_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeActionApplyMoveFlip u) = core u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl


private theorem moveWsigCheckLast_view {ψ : Nat}
    (u : AgentState ψ) :
    core (moveWsigCheckLast u) = core u := by
  cases hp : u.path3 <;>
    simp [moveWsigCheckLast, hp, core]


private theorem writeSeqSetWriteReady_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqSetWriteReady u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqSetWriteReady, hp, core]


private theorem writeSeqCheckBit_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqCheckBit u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqCheckBit, hp, core]


private theorem writeSeqSetWriteAct_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqSetWriteAct u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqSetWriteAct, hp, core]


private theorem writeSeqFinalR_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqFinalR u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqFinalR, hp, core]


private theorem moveWsigCheckGenWs_view {ψ : Nat}
    (l r : AgentState ψ) :
    core (moveWsigCheckGenWs l r) = core r := by
  cases hp : l.path3 <;>
    simp [moveWsigCheckGenWs, hp, core]


private theorem moveWsigTransfer_view {ψ : Nat}
    (l r : AgentState ψ) :
    core (moveWsigTransfer l r).1 = core l ∧
    core (moveWsigTransfer l r).2 = core r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp [moveWsigTransfer, hl, hr, core, NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite]


private theorem groupInfo_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (groupInfo hp l r).1 = core l ∧
    core (groupInfo hp l r).2 = core r := by
  simp only [groupInfo, NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite, core,
    NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite, ite_self, and_self]


private theorem gensigWriteseq_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (gensigWriteseq hp l r).1 = core l ∧
    core (gensigWriteseq hp l r).2 = core r := by
  simp only [gensigWriteseq, NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite, core,
    NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite, ite_self, and_self]


private theorem writeAction_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (writeAction hp l r).1 = core l ∧
    core (writeAction hp l r).2 = core r := by
  simp only [writeAction, NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite, core,
    NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite, ite_self, and_self,
    (view_label (writeActionApplyOverwrite_view _)), (view_state (writeActionApplyOverwrite_view _)), (view_path2 (writeActionApplyOverwrite_view _)), (view_path (writeActionApplyOverwrite_view _)), (view_label (writeActionApplyMoveFlip_view _)), (view_state (writeActionApplyMoveFlip_view _)), (view_path2 (writeActionApplyMoveFlip_view _)), (view_path (writeActionApplyMoveFlip_view _))]


private theorem moveWsig_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (moveWsig hp l r).1 = core l ∧
    core (moveWsig hp l r).2 = core r := by
  simp only [moveWsig, NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite, core,
    NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite, ite_self, and_self,
    (view_label (moveWsigCheckGenWs_view _ _)), (view_state (moveWsigCheckGenWs_view _ _)), (view_path2 (moveWsigCheckGenWs_view _ _)), (view_path (moveWsigCheckGenWs_view _ _)), (view_label (moveWsigCheckLast_view _)), (view_state (moveWsigCheckLast_view _)), (view_path2 (moveWsigCheckLast_view _)), (view_path (moveWsigCheckLast_view _)),
    (view_label (moveWsigTransfer_view _ _).1), (view_state (moveWsigTransfer_view _ _).1), (view_path2 (moveWsigTransfer_view _ _).1), (view_path (moveWsigTransfer_view _ _).1), (view_label (moveWsigTransfer_view _ _).2), (view_state (moveWsigTransfer_view _ _).2), (view_path2 (moveWsigTransfer_view _ _).2), (view_path (moveWsigTransfer_view _ _).2)]


private theorem writeSeq_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (writeSeq hp l r).1 = core l ∧
    core (writeSeq hp l r).2 = core r := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare,
    writeSeqReady, writeSeqCompare, writeSeqCommands,
    NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite, core, NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite,
    ite_self, and_self,
    (view_label (groupInfo_view _ _ _).1), (view_state (groupInfo_view _ _ _).1), (view_path2 (groupInfo_view _ _ _).1), (view_path (groupInfo_view _ _ _).1), (view_label (groupInfo_view _ _ _).2), (view_state (groupInfo_view _ _ _).2), (view_path2 (groupInfo_view _ _ _).2), (view_path (groupInfo_view _ _ _).2),
    (view_label (gensigWriteseq_view _ _ _).1), (view_state (gensigWriteseq_view _ _ _).1), (view_path2 (gensigWriteseq_view _ _ _).1), (view_path (gensigWriteseq_view _ _ _).1), (view_label (gensigWriteseq_view _ _ _).2), (view_state (gensigWriteseq_view _ _ _).2), (view_path2 (gensigWriteseq_view _ _ _).2), (view_path (gensigWriteseq_view _ _ _).2),
    (view_label (writeAction_view _ _ _).1), (view_state (writeAction_view _ _ _).1), (view_path2 (writeAction_view _ _ _).1), (view_path (writeAction_view _ _ _).1), (view_label (writeAction_view _ _ _).2), (view_state (writeAction_view _ _ _).2), (view_path2 (writeAction_view _ _ _).2), (view_path (writeAction_view _ _ _).2),
    (view_label (moveWsig_view _ _ _).1), (view_state (moveWsig_view _ _ _).1), (view_path2 (moveWsig_view _ _ _).1), (view_path (moveWsig_view _ _ _).1), (view_label (moveWsig_view _ _ _).2), (view_state (moveWsig_view _ _ _).2), (view_path2 (moveWsig_view _ _ _).2), (view_path (moveWsig_view _ _ _).2),
    (view_label (writeSeqSetWriteReady_view _)), (view_state (writeSeqSetWriteReady_view _)), (view_path2 (writeSeqSetWriteReady_view _)), (view_path (writeSeqSetWriteReady_view _)), (view_label (writeSeqCheckBit_view _)), (view_state (writeSeqCheckBit_view _)), (view_path2 (writeSeqCheckBit_view _)), (view_path (writeSeqCheckBit_view _)),
    (view_label (writeSeqSetWriteAct_view _)), (view_state (writeSeqSetWriteAct_view _)), (view_path2 (writeSeqSetWriteAct_view _)), (view_path (writeSeqSetWriteAct_view _)), (view_label (writeSeqFinalR_view _)), (view_state (writeSeqFinalR_view _)), (view_path2 (writeSeqFinalR_view _)), (view_path (writeSeqFinalR_view _))]


theorem writeWithBundle_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (writeWithBundle hp l r).1 = core l ∧
    core (writeWithBundle hp l r).2 = core r := by
  have h := writeSeq_view hp l r
  simp only [writeWithBundle, NoAlloc.fst_ite, NoAlloc.snd_ite, core_ite, core,
    NoAlloc.state_ite, NoAlloc.path_ite,label_ite,path2_ite, view_label h.1, view_state h.1, view_path2 h.1, view_path h.1, view_label h.2, view_state h.2, view_path2 h.2, view_path h.2, ite_self, and_self]


end Writer


private theorem conserve_mono {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : PairMono q (conserve .head l r q) := by
  unfold conserve
  split <;> simp [PairMono,Mono,core,replacement,clearCmp]

private def finish {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := suppressSigResetKill hp q.1 q.2
  let q := k4Kernel hp q.1 q.2
  let q := writeWithBundle hp q.1 q.2
  conserve .head l r q

private theorem finish_mono {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : PairMono q (finish hp l r q) := by
  let a := suppressSigResetKill hp q.1 q.2
  let b := k4Kernel hp a.1 a.2
  let w := writeWithBundle hp b.1 b.2
  have ha : PairMono q a := suppress_mono hp q.1 q.2
  have hb : PairMono a b := ⟨Or.inr (kernel_view hp a.1 a.2).1,Or.inr (kernel_view hp a.1 a.2).2⟩
  have hw : PairMono b w := ⟨Or.inr (Writer.writeWithBundle_view hp b.1 b.2).1,
    Or.inr (Writer.writeWithBundle_view hp b.1 b.2).2⟩
  exact pair_trans (pair_trans (pair_trans ha hb) hw) (conserve_mono l r w)
end Tail

/-- Actual post-COMPARE suffix, retaining the original inputs for conservation. -/
def finishCompare {ψ : Nat} (hp : ψ > 0) (originalL originalR : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  let a := suppressSigResetKill hp q.1 q.2
  let b := k4Kernel hp a.1 a.2
  let w := writeWithBundle hp b.1 b.2
  conserve .head originalL originalR w

/-- Every suffix endpoint either loses its main path or preserves its complete
comparison projection. Leader flags are deliberately outside this projection. -/
theorem finishCompare_frame_or_hole {ψ : Nat} (hp : ψ > 0)
    (originalL originalR : AgentState ψ) (q : AgentState ψ × AgentState ψ) :
    let z := finishCompare hp originalL originalR q
    (z.1.path = .bot ∨
      (z.1.label,z.1.state,z.1.path,z.1.path2) =
        (q.1.label,q.1.state,q.1.path,q.1.path2)) ∧
    (z.2.path = .bot ∨
      (z.2.label,z.2.state,z.2.path,z.2.path2) =
        (q.2.label,q.2.state,q.2.path,q.2.path2)) :=
  Tail.finish_mono hp originalL originalR q

private theorem hole_mono {ψ : Nat} {l r a b : AgentState ψ}
    (h : Hole (l,r)) (hm : NoAlloc.PairMono l r a b) : Hole (a,b) := by
  rcases h with hl | hr
  · left
    rcases hm.1.1 with he | he
    · exact he.trans hl
    · exact he
  · right
    rcases hm.2.1 with he | he
    · exact he.trans hr
    · exact he

private theorem hole_move {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (h : Hole (l,r)) : Hole (PPLLFableZDiv.moveSourceF hp sourceCfg l r) := by
  have hf : NoAlloc.FrameOrHole l r l r := by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have ho := NoAlloc.moveSourceF_frameOrHole hp sourceCfg l r l r hf
  rcases ho with hl | hr | hg
  · exact Or.inl hl
  · exact Or.inr hr
  · rcases h with hl | hr
    · exact Or.inl (hg.1.trans hl)
    · exact Or.inr (hg.2.1.trans hr)


/-- Exact actual prefix ending immediately before moveSourceF. -/
def moveEntry {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let p := pPsiProbeWall hp l r
  let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
  let a := cleanSource hp g.1 g.2
  let b := releaseSource hp a.1 a.2
  eliminateSig hp b.1 b.2

/-! The stages of `moveEntry` as functions of the pair; `moveEntry_split` is checked by `rfl` at
variables. The frame theorems below generalize one stage output at a time (with tactic `let`s
for the stage outputs, the final `change` against `moveEntry` took 90-96 s). -/

private def meG {ψ : Nat} (hp : ψ > 0) (κ : Nat) (q : AgentState ψ × AgentState ψ) :=
  PPLLFableZDiv.genSigOverwrite hp κ true 0 q.1 q.2
private def meC {ψ : Nat} (hp : ψ > 0) (q : AgentState ψ × AgentState ψ) :=
  cleanSource hp q.1 q.2
private def meR {ψ : Nat} (hp : ψ > 0) (q : AgentState ψ × AgentState ψ) :=
  releaseSource hp q.1 q.2
private def meE {ψ : Nat} (hp : ψ > 0) (q : AgentState ψ × AgentState ψ) :=
  eliminateSig hp q.1 q.2

private theorem moveEntry_split {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    moveEntry hp κ l r = meE hp (meR hp (meC hp (meG hp κ (pPsiProbeWall hp l r)))) := rfl

/-- The prefix preserves comparison controls and may only delete main paths. -/
def EntryFrame {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.label = l.label ∧ q.2.label = r.label ∧
  q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
  q.1.state = l.state ∧ q.2.state = r.state ∧
  q.1.path2 = l.path2 ∧ q.2.path2 = r.path2 ∧
  (q.1.path = l.path ∨ q.1.path = .bot) ∧
  (q.2.path = r.path ∨ q.2.path = .bot)

/-- Boundary C2/locked inputs reach the actual MOVE cut with unchanged controls.
No token, path, leader or ancillary premise is needed for this prefix theorem. -/
theorem boundary_moveEntry_frame {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (l r : AgentState ψ)
    (hl : l.label.val = ψ-1) (hr : r.label.val = 0)
    (sl : l.state = .compare2) (sr : r.state = .lock ∨ r.state = .compare1) :
    EntryFrame l r (moveEntry hp κ l r) := by
  rw [moveEntry_split]
  have hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    simp only [Fin.val_mk,hl,hr]
    have he : ψ-1+1 = ψ := by omega
    simp [he]
  have hps := pprime_snap hp l r hn
  simp only [snap,Prod.mk.injEq] at hps
  revert hps; generalize pPsiProbeWall hp l r = p; intro hps
  have hp0 : p.1.label ≠ ⟨0,hp⟩ := by
    intro h
    have hval := congrArg Fin.val h
    have hlabel : p.1.label.val = ψ-1 := by rw [hps.1.1,hl]
    simp only [Fin.val_zero] at hval
    omega
  have hpn : p.1.state ≠ .produce := by rw [hps.1.2.2.1,sl]; decide
  have hrn : p.2.state ≠ .produce := by
    rw [hps.2.2.2.1]
    rcases sr with hs | hs <;> simp [hs]
  have hgs := gen_snap hp κ p.1 p.2 hp0 hpn hrn
  simp only [snap,Prod.mk.injEq] at hgs
  show EntryFrame l r (meE hp (meR hp (meC hp
    (PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2))))
  revert hgs; generalize PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2 = g; intro hgs
  have hak := Clean.cleanSource_keeps hp g.1 g.2
  simp only [Clean.keep,Prod.mk.injEq] at hak
  have ham := NoAlloc.cleanSource_mono hp g.1 g.2
  show EntryFrame l r (meE hp (meR hp (cleanSource hp g.1 g.2)))
  revert hak ham; generalize cleanSource hp g.1 g.2 = a; intro hak ham
  have al : a.1.label = l.label := hak.1.1.trans (hgs.1.1.trans hps.1.1)
  have ar : a.2.label = r.label := hak.2.1.trans (hgs.2.1.trans hps.2.1)
  have all : a.1.leader = l.leader := hak.1.2.1.trans (hgs.1.2.1.trans hps.1.2.1)
  have alr : a.2.leader = r.leader := hak.2.2.1.trans (hgs.2.2.1.trans hps.2.2.1)
  have asl : a.1.state = l.state := hak.1.2.2.1.trans (hgs.1.2.2.1.trans hps.1.2.2.1)
  have asr : a.2.state = r.state := hak.2.2.2.1.trans (hgs.2.2.2.1.trans hps.2.2.2.1)
  have atl : a.1.path2 = l.path2 := hak.1.2.2.2.trans (hgs.1.2.2.2.2.trans hps.1.2.2.2.2)
  have atr : a.2.path2 = r.path2 := hak.2.2.2.2.trans (hgs.2.2.2.2.2.trans hps.2.2.2.2.2)
  have apl : a.1.path = l.path ∨ a.1.path = .bot := by
    rcases ham.1.1 with h | h
    · exact Or.inl (h.trans (hgs.1.2.2.2.1.trans hps.1.2.2.2.1))
    · exact Or.inr h
  have apr : a.2.path = r.path ∨ a.2.path = .bot := by
    rcases ham.2.1 with h | h
    · exact Or.inl (h.trans (hgs.2.2.2.2.1.trans hps.2.2.2.2.1))
    · exact Or.inr h
  have ar0 : a.2.label = ⟨0,hp⟩ := Fin.ext (by rw [ar,hr])
  have he : eliminateSig hp (releaseSource hp a.1 a.2).1
      (releaseSource hp a.1 a.2).2 = a := by
    rcases sr with hs | hs <;>
      simp [releaseSource,eliminateSig,ar0,asr,hs]
  change EntryFrame l r (eliminateSig hp (releaseSource hp a.1 a.2).1
    (releaseSource hp a.1 a.2).2)
  rw [he]
  exact ⟨al,ar,all,alr,asl,asr,atl,atr,apl,apr⟩

/-- General full-path successor prefix for B-state consumers. No token action,
follower, payload-bit, or ancillary condition is imposed. -/
theorem full_moveEntry_frame {ψ : Nat} (hp : ψ > 0)
    (κ : Nat) (l r : AgentState ψ)
    (hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done)
    (hrs : r.state ≠ .produce) (hrd : r.state ≠ .done)
    (hre : r.state ≠ .eliminate_signal) :
    EntryFrame l r (moveEntry hp κ l r) := by
  rw [moveEntry_split]
  have hps := pprime_snap hp l r hn
  simp only [snap,Prod.mk.injEq] at hps
  revert hps; generalize pPsiProbeWall hp l r = p; intro hps
  have hpl : p.1.path ≠ .bot := by rw [hps.1.2.2.2.1]; exact hlp
  have hpr : p.2.path ≠ .bot := by rw [hps.2.2.2.2.1]; exact hrp
  have hpn : p.1.state ≠ .produce := by rw [hps.1.2.2.1]; exact hls
  have hpd : p.1.state ≠ .done := by rw [hps.1.2.2.1]; exact hld
  have hrn : p.2.state ≠ .produce := by rw [hps.2.2.2.1]; exact hrs
  have hgs := gen_full_snap hp κ p.1 p.2 hpl hpr hpn hpd hrn
  simp only [snap,Prod.mk.injEq] at hgs
  show EntryFrame l r (meE hp (meR hp (meC hp
    (PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2))))
  revert hgs; generalize PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2 = g; intro hgs
  have hak := Clean.cleanSource_keeps hp g.1 g.2
  simp only [Clean.keep,Prod.mk.injEq] at hak
  have ham := NoAlloc.cleanSource_mono hp g.1 g.2
  show EntryFrame l r (meE hp (meR hp (cleanSource hp g.1 g.2)))
  revert hak ham; generalize cleanSource hp g.1 g.2 = a; intro hak ham
  have al : a.1.label = l.label := hak.1.1.trans (hgs.1.1.trans hps.1.1)
  have ar : a.2.label = r.label := hak.2.1.trans (hgs.2.1.trans hps.2.1)
  have all : a.1.leader = l.leader := hak.1.2.1.trans (hgs.1.2.1.trans hps.1.2.1)
  have alr : a.2.leader = r.leader := hak.2.2.1.trans (hgs.2.2.1.trans hps.2.2.1)
  have asl : a.1.state = l.state := hak.1.2.2.1.trans (hgs.1.2.2.1.trans hps.1.2.2.1)
  have asr : a.2.state = r.state := hak.2.2.2.1.trans (hgs.2.2.2.1.trans hps.2.2.2.1)
  have atl : a.1.path2 = l.path2 := hak.1.2.2.2.trans (hgs.1.2.2.2.2.trans hps.1.2.2.2.2)
  have atr : a.2.path2 = r.path2 := hak.2.2.2.2.trans (hgs.2.2.2.2.2.trans hps.2.2.2.2.2)
  have apl : a.1.path = l.path ∨ a.1.path = .bot := by
    rcases ham.1.1 with h | h
    · exact Or.inl (h.trans (hgs.1.2.2.2.1.trans hps.1.2.2.2.1))
    · exact Or.inr h
  have apr : a.2.path = r.path ∨ a.2.path = .bot := by
    rcases ham.2.1 with h | h
    · exact Or.inl (h.trans (hgs.2.2.2.2.1.trans hps.2.2.2.2.1))
    · exact Or.inr h
  have ard : a.2.state ≠ .done := by rw [asr]; exact hrd
  have are : a.2.state ≠ .eliminate_signal := by rw [asr]; exact hre
  have he : eliminateSig hp (releaseSource hp a.1 a.2).1
      (releaseSource hp a.1 a.2).2 = a := by
    simp [releaseSource,eliminateSig,ard,are]
  change EntryFrame l r (eliminateSig hp (releaseSource hp a.1 a.2).1
    (releaseSource hp a.1 a.2).2)
  rw [he]
  exact ⟨al,ar,all,alr,asl,asr,atl,atr,apl,apr⟩

/-- The exact remaining R5 pipeline, retaining original inputs for conserve. -/
def afterEntry {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let m := PPLLFableZDiv.moveSourceF hp sourceCfg l r
  let d := (dropStale m.1,dropStale m.2)
  let p := preCheckReset d.1 d.2
  let n := (normalizeReady p.1,normalizeReady p.2)
  let ch := checkSource hp c n.1 n.2
  let ds := disappear hp ch.1 ch.2
  let rr := repair .readyAck ds.1 ds.2
  let cp := compareLifecycle κ rr.1 rr.2
  Tail.finish hp originalL originalR cp

/-! The stages of `afterEntry` as functions of the pair (`afterEntry_split`, `rfl` at
variables); `afterEntry_pairHole` generalizes one stage output at a time. -/

private def aeD {ψ : Nat} (q : AgentState ψ × AgentState ψ) := (dropStale q.1, dropStale q.2)
private def aeP {ψ : Nat} (q : AgentState ψ × AgentState ψ) := preCheckReset q.1 q.2
private def aeN {ψ : Nat} (q : AgentState ψ × AgentState ψ) :=
  (normalizeReady q.1, normalizeReady q.2)
private def aeC {ψ : Nat} (hp : ψ > 0) (c : Cfg) (q : AgentState ψ × AgentState ψ) :=
  checkSource hp c q.1 q.2
private def aeX {ψ : Nat} (hp : ψ > 0) (q : AgentState ψ × AgentState ψ) := disappear hp q.1 q.2
private def aeR {ψ : Nat} (q : AgentState ψ × AgentState ψ) := repair .readyAck q.1 q.2
private def aeL {ψ : Nat} (κ : Nat) (q : AgentState ψ × AgentState ψ) :=
  compareLifecycle κ q.1 q.2

private theorem afterEntry_split {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ) :
    afterEntry hp κ c originalL originalR l r =
      Tail.finish hp originalL originalR (aeL κ (aeR (aeX hp (aeC hp c (aeN (aeP (aeD
        (PPLLFableZDiv.moveSourceF hp sourceCfg l r)))))))) := rfl

/-- A pair-hole can move between endpoints, but cannot disappear after GEN. -/
theorem afterEntry_pairHole {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ)
    (h : l.path = .bot ∨ r.path = .bot) :
    (afterEntry hp κ c originalL originalR l r).1.path = .bot ∨
    (afterEntry hp κ c originalL originalR l r).2.path = .bot := by
  rw [afterEntry_split]
  have hm : Hole (PPLLFableZDiv.moveSourceF hp sourceCfg l r) := hole_move hp l r h
  revert hm; generalize PPLLFableZDiv.moveSourceF hp sourceCfg l r = m; intro hm
  have hd : Hole (aeD m) := hole_mono hm ⟨NoAlloc.drop_mono m.1,NoAlloc.drop_mono m.2⟩
  revert hd; generalize aeD m = d; intro hd
  have hp' : Hole (aeP d) := hole_mono hd (NoAlloc.precheck_mono d.1 d.2)
  revert hp'; generalize aeP d = p; intro hp'
  have hn : Hole (aeN p) :=
    hole_mono hp' ⟨NoAlloc.normalizeReady_mono p.1,NoAlloc.normalizeReady_mono p.2⟩
  revert hn; generalize aeN p = n; intro hn
  have hch : Hole (aeC hp c n) := hole_mono hn (NoAlloc.checkSource_mono hp c n.1 n.2)
  revert hch; generalize aeC hp c n = ch; intro hch
  have hds : Hole (aeX hp ch) := hole_mono hch (NoAlloc.disappear_mono hp ch.1 ch.2)
  revert hds; generalize aeX hp ch = ds; intro hds
  have hrr : Hole (aeR ds) := hole_mono hds (NoAlloc.repairReady_mono ds.1 ds.2)
  revert hrr; generalize aeR ds = rr; intro hrr
  have hcp : Hole (aeL κ rr) := hole_mono hrr (NoAlloc.compareLifecycle_mono κ rr.1 rr.2)
  revert hcp; generalize aeL κ rr = cp; intro hcp
  have hf := Tail.finish_mono hp originalL originalR cp
  rcases hcp with hL | hR
  · left
    rcases hf.1 with hb | he
    · exact hb
    · exact (Tail.view_path he).trans hL
  · right
    rcases hf.2 with hb | he
    · exact hb
    · exact (Tail.view_path he).trans hR

/-- Literal continuation after preCheckReset; original inputs are retained. -/
def afterPrecheck {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let n := (normalizeReady l, normalizeReady r)
  let ch := checkSource hp c n.1 n.2
  let ds := disappear hp ch.1 ch.2
  let rr := repair .readyAck ds.1 ds.2
  let cp := compareLifecycle κ rr.1 rr.2
  finishCompare hp originalL originalR cp

/-- Reset deletion cannot be undone by the remaining comparison/writer stages. -/
theorem afterPrecheck_pairHole {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ)
    (h : l.path = .bot ∨ r.path = .bot) :
    (afterPrecheck hp κ c originalL originalR l r).1.path = .bot ∨
    (afterPrecheck hp κ c originalL originalR l r).2.path = .bot := by
  let n := (normalizeReady l, normalizeReady r)
  have hn : Hole n := hole_mono h ⟨NoAlloc.normalizeReady_mono l,NoAlloc.normalizeReady_mono r⟩
  let ch := checkSource hp c n.1 n.2
  have hch : Hole ch := hole_mono hn (NoAlloc.checkSource_mono hp c n.1 n.2)
  let ds := disappear hp ch.1 ch.2
  have hds : Hole ds := hole_mono hch (NoAlloc.disappear_mono hp ch.1 ch.2)
  let rr := repair .readyAck ds.1 ds.2
  have hrr : Hole rr := hole_mono hds (NoAlloc.repairReady_mono ds.1 ds.2)
  let cp := compareLifecycle κ rr.1 rr.2
  have hcp : Hole cp := hole_mono hrr (NoAlloc.compareLifecycle_mono κ rr.1 rr.2)
  let z := finishCompare hp originalL originalR cp
  have hf := finishCompare_frame_or_hole hp originalL originalR cp
  change z.1.path = .bot ∨ z.2.path = .bot
  rcases hcp with hL | hR
  · left
    rcases hf.1 with hb | he
    · exact hb
    · exact (Tail.view_path he).trans hL
  · right
    rcases hf.2 with hb | he
    · exact hb
    · exact (Tail.view_path he).trans hR

/-- Literal continuation after the completed MOVE call. -/
def postMove {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let d := (dropStale l, dropStale r)
  let p := preCheckReset d.1 d.2
  afterPrecheck hp κ c originalL originalR p.1 p.2

/-- A completed-MOVE pair hole persists to the actual row endpoint. -/
theorem postMove_pairHole {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ)
    (h : l.path = .bot ∨ r.path = .bot) :
    (postMove hp κ c originalL originalR l r).1.path = .bot ∨
    (postMove hp κ c originalL originalR l r).2.path = .bot := by
  let d := (dropStale l, dropStale r)
  have hd : Hole d := hole_mono h ⟨NoAlloc.drop_mono l,NoAlloc.drop_mono r⟩
  let p := preCheckReset d.1 d.2
  have hp' : Hole p := hole_mono hd (NoAlloc.precheck_mono d.1 d.2)
  exact afterPrecheck_pairHole hp κ c originalL originalR p.1 p.2 hp'

section PostMoveFactor
attribute [local irreducible] PPLLFableZDiv.moveSourceF dropStale preCheckReset
  normalizeReady checkSource disappear repair compareLifecycle suppressSigResetKill
  k4Kernel writeWithBundle conserve

/-- Public cut identity for downstream proofs; no protocol stage is replaced. -/
theorem afterEntry_eq_postMove {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (originalL originalR l r : AgentState ψ) :
    afterEntry hp κ c originalL originalR l r =
      let m := PPLLFableZDiv.moveSourceF hp sourceCfg l r
      postMove hp κ c originalL originalR m.1 m.2 := by
  rfl
end PostMoveFactor

/-- The cut and suffix use exactly the production pipeline definition. -/
theorem pipeline_factor {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) :
    pipeline hp κ c l r =
      let q := moveEntry hp κ l r
      afterEntry hp κ c l r q.1 q.2 := rfl

/-- A frame on an arbitrary cut pair yields exact paths when neither is missing. -/
private theorem entryFrame_full {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) (hf : EntryFrame l r q)
    (hh : ¬ (q.1.path = .bot ∨ q.2.path = .bot)) :
    EntryFrame l r q ∧ q.1.path = l.path ∧ q.2.path = r.path := by
  have hp := hf.2.2.2.2.2.2.2.2
  exact ⟨hf, hp.1.resolve_right (fun h => hh (Or.inl h)),
    hp.2.resolve_right (fun h => hh (Or.inr h))⟩

-- Keep the already proved cut identities abstract during composition.
attribute [local irreducible] moveEntry afterEntry EntryFrame PPLLAstraR5Repair.pipeline

/-- The prefix alternative is connected to the final actual pipeline hole.
Selected-token and action-alphabet facts can be transported through EntryFrame. -/
theorem boundary_entry_or_final_hole {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : Cfg) (l r : AgentState ψ)
    (hl : l.label.val = ψ-1) (hr : r.label.val = 0)
    (sl : l.state = .compare2) (sr : r.state = .lock ∨ r.state = .compare1) :
    (pipeline hp κ c l r).1.path = .bot ∨
    (pipeline hp κ c l r).2.path = .bot ∨
      (let q := moveEntry hp κ l r
       EntryFrame l r q ∧ q.1.path = l.path ∧ q.2.path = r.path) := by
  let q := moveEntry hp κ l r
  have hf : EntryFrame l r q := boundary_moveEntry_frame hp h4 κ l r hl hr sl sr
  by_cases hh : q.1.path = .bot ∨ q.2.path = .bot
  · have ho := afterEntry_pairHole hp κ c l r q.1 q.2 hh
    have he : pipeline hp κ c l r = afterEntry hp κ c l r q.1 q.2 :=
      pipeline_factor hp κ c l r
    have hf : (pipeline hp κ c l r).1.path = .bot ∨
        (pipeline hp κ c l r).2.path = .bot :=
      Eq.mpr (congrArg (fun z : AgentState ψ × AgentState ψ =>
        z.1.path = .bot ∨ z.2.path = .bot) he) ho
    exact hf.elim Or.inl (fun h => Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (entryFrame_full l r q hf hh))

/-- Full-path successor analogue for B-state stage consumers. -/
theorem full_entry_or_final_hole {ψ : Nat} (hp : ψ > 0)
    (κ : Nat) (c : Cfg) (l r : AgentState ψ)
    (hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done)
    (hrs : r.state ≠ .produce) (hrd : r.state ≠ .done)
    (hre : r.state ≠ .eliminate_signal) :
    (pipeline hp κ c l r).1.path = .bot ∨
    (pipeline hp κ c l r).2.path = .bot ∨
      (let q := moveEntry hp κ l r
       EntryFrame l r q ∧ q.1.path = l.path ∧ q.2.path = r.path) := by
  let q := moveEntry hp κ l r
  have hf : EntryFrame l r q := full_moveEntry_frame hp κ l r hn hlp hrp hls hld hrs hrd hre
  by_cases hh : q.1.path = .bot ∨ q.2.path = .bot
  · have ho := afterEntry_pairHole hp κ c l r q.1 q.2 hh
    have he : pipeline hp κ c l r = afterEntry hp κ c l r q.1 q.2 :=
      pipeline_factor hp κ c l r
    have hf : (pipeline hp κ c l r).1.path = .bot ∨
        (pipeline hp κ c l r).2.path = .bot :=
      Eq.mpr (congrArg (fun z : AgentState ψ × AgentState ψ =>
        z.1.path = .bot ∨ z.2.path = .bot) he) ho
    exact hf.elim Or.inl (fun h => Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (entryFrame_full l r q hf hh))

#print axioms afterEntry_eq_postMove
#print axioms afterPrecheck_pairHole
#print axioms postMove_pairHole
#print axioms finishCompare_frame_or_hole
#print axioms full_entry_or_final_hole
#print axioms full_moveEntry_frame
#print axioms boundary_moveEntry_frame
#print axioms afterEntry_pairHole
#print axioms boundary_entry_or_final_hole
end ServiceEntry
end PPLLAstraR5Repair
