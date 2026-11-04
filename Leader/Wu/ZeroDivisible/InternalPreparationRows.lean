import Leader.Wu.ZeroDivisible.CheckRepair

/-!
# Token-free internal preparation rows

This module follows actual R5 stages with an explicit hole-or-shape invariant.
Internal nonterminal carries preserve the main-state projection. Path payloads are the original raw
payloads, independently of resident bits changed by WRITE.
-/
namespace PPLLAstraR5Repair


namespace PrepInternal
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

/-- Locked left endpoints admit either handshake phase. -/
def Locked (s : MainState) : Prop := s = .lock ∨ s = .compare1
/-- A forward preparation row accepts a departed or already locked successor. -/
def Mid (s : MainState) : Prop := s = .depart ∨ s = .lock ∨ s = .compare1
/-- An existing acknowledgement propagates left in the internal row. -/
def leftResult (s t : MainState) : MainState :=
  if s = .lock ∧ t = .compare1 then .compare1 else s
/-- A departed nonterminal successor becomes locked. -/
def rightResult (t : MainState) : MainState := if t = .depart then .lock else t

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

private theorem precheck_snap {ψ : Nat} (l r : AgentState ψ)
    (h : ¬ Hole (preCheckReset l r)) :
    snap (preCheckReset l r).1 = snap l ∧ snap (preCheckReset l r).2 = snap r := by
  cases hl : l.leader <;> cases hc : l.reset_cmd <;> cases hr : r.reset_cmd <;>
    simp_all [Hole,preCheckReset,clearCmp,snap]


private theorem internal_release {ψ : Nat} (hp : ψ > 0) {i bL bR : Nat} {s t : MainState}
    (l r : AgentState ψ) (ht : Mid t) (h : Shape i (i+1) bL bR s t (l,r)) :
    releaseSource hp l r = (l,r) := by
  have sr : r.state = t := h.2.2.2.2.2.2.2.1
  rcases ht with rfl | rfl | rfl <;> simp [releaseSource,sr]

private theorem internal_eliminate {ψ : Nat} (hp : ψ > 0) {i bL bR : Nat} {s t : MainState}
    (l r : AgentState ψ) (ht : Mid t) (h : Shape i (i+1) bL bR s t (l,r)) :
    eliminateSig hp l r = (l,r) := by
  have sr : r.state = t := h.2.2.2.2.2.2.2.1
  rcases ht with rfl | rfl | rfl <;> simp [eliminateSig,sr]

private theorem internal_move {ψ : Nat} (hp : ψ > 0) {i bL bR : Nat} {s t : MainState}
    (l r : AgentState ψ) (hs : Locked s) (ht : Mid t)
    (h : Shape i (i+1) bL bR s t (l,r)) :
    PPLLFableZDiv.moveSourceF hp sourceCfg l r = (l,r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    simp [PPLLFableZDiv.moveSourceF,PPLLFableZDiv.sigMoveStep1F,
      moveTokens,leaderWall,sigMoveApplyControlConsume,pl,pr,tl,tr,sl,sr,ll,lr]

private theorem internal_drop {ψ : Nat} {i bL bR : Nat} {s t : MainState}
    (l r : AgentState ψ) (h : Shape i (i+1) bL bR s t (l,r)) :
    (dropStale l,dropStale r) = (l,r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  simp [dropStale,aligned,pl,pr,hl,hr]

private theorem internal_normalize {ψ : Nat} {i bL bR : Nat} {s t : MainState}
    (l r : AgentState ψ) (hs : Locked s) (ht : Mid t)
    (h : Shape i (i+1) bL bR s t (l,r)) :
    (normalizeReady l,normalizeReady r) = (l,r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    simp [normalizeReady,normalizeOrphan,normalizeCarrier,releaseCongest,
      aligned,pl,pr,tl,tr,sl,sr,ll,lr,hl,hr]

private theorem internal_check {ψ : Nat} (hp : ψ > 0) (c : Cfg)
    {i bL bR : Nat} {s t : MainState} (l r : AgentState ψ) (hs : Locked s) (ht : Mid t)
    (h : Shape i (i+1) bL bR s t (l,r)) :
    checkSource hp c l r = (l,r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    cases i <;>
    simp [checkSource,checkSigSetReadyGuarded,checkSigSetReady,waveState,controlPending,
      releaseEqual,aligned,checkSigCheckL,checkSigCheckR,setResult,preserveToken,checkSigSetResult,
      pl,pr,tl,tr,sl,sr,ll,lr,hl,hr]

private theorem internal_disappear {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    {i bL bR : Nat} (hi : i ≤ ψ-3) {s t : MainState}
    (l r : AgentState ψ) (hs : Locked s) (ht : Mid t)
    (h : Shape i (i+1) bL bR s t (l,r)) :
    Shape i (i+1) bL bR s t (disappear hp l r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  have hrl : r.label ≠ ⟨ψ-1,by omega⟩ := by
    intro he; have he' := congrArg Fin.val he
    simp only [hr] at he'; omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    simp [disappear,Shape,pl,pr,tl,tr,sl,sr,ll,lr,hl,hr,hrl] <;>
    repeat (split <;> simp_all [Shape])

private theorem internal_repair {ψ : Nat} (h4 : 4 ≤ ψ)
    {i bL bR : Nat} (hi : i ≤ ψ-3) {s t : MainState}
    (l r : AgentState ψ) (hs : Locked s) (ht : Mid t)
    (h : Shape i (i+1) bL bR s t (l,r)) :
    repair .readyAck l r = (l,r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  have hnt : i+1 ≠ ψ-1 := by omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    simp [repair,normalizeCarrier,normalizeOrphan,releaseCongest,releaseReadySuffix,ackTail,
      pl,pr,tl,tr,sl,sr,ll,lr,hl,hr,hnt]

private theorem internal_compare {ψ : Nat} (h4 : 4 ≤ ψ) (κ : Nat)
    {i bL bR : Nat} (hi : i ≤ ψ-3) {s t : MainState} (l r : AgentState ψ)
    (hs : Locked s) (ht : Mid t) (h : Shape i (i+1) bL bR s t (l,r)) :
    Shape i (i+1) bL bR (leftResult s t) (rightResult t) (compareLifecycle κ l r) := by
  rcases h with ⟨hl,hr,pl,pr,tl,tr,sl,sr,ll,lr⟩
  dsimp only at hl hr pl pr tl tr sl sr ll lr
  have hnt : i+1 ≠ ψ-1 := by omega
  have hlt : i ≠ ψ-1 := by omega
  have himod : i % ψ = i := Nat.mod_eq_of_lt (by omega)
  have hprev : (i+1+ψ-1)%ψ = i := by
    have he : i+1+ψ-1 = i+ψ := by omega
    rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    simp [compareLifecycle,maintain,completeWave,wave,dropStray,landBackward,landForward,
      lockedState,lockerState,waveState,Shape,leftResult,rightResult,
      pl,pr,tl,tr,sl,sr,ll,lr,hl,hr,hnt,hlt,hprev,himod]
/-! The suffix either retains the observable comparison fields or deletes
that holder's main path. This carries terminal outcomes through reset/WRITE. -/
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

private theorem step {ψ : Nat} {P Q : (AgentState ψ × AgentState ψ) → Prop}
    (f : (AgentState ψ × AgentState ψ) → (AgentState ψ × AgentState ψ))
    (hm : ∀ q, Hole q → Hole (f q)) {q : AgentState ψ × AgentState ψ}
    (h : Hole q ∨ P q) (hg : P q → Hole (f q) ∨ Q (f q)) :
    Hole (f q) ∨ Q (f q) := by
  rcases h with hh | hq
  · exact Or.inl (hm q hh)
  · exact hg hq

private def throughCompare {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hp l r
  let q := PPLLFableZDiv.genSigOverwrite hp κ true 0 q.1 q.2
  let q := cleanSource hp q.1 q.2
  let q := releaseSource hp q.1 q.2
  let q := eliminateSig hp q.1 q.2
  let q := PPLLFableZDiv.moveSourceF hp sourceCfg q.1 q.2
  let q := (dropStale q.1,dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1,normalizeReady q.2)
  let q := checkSource hp c q.1 q.2
  let q := disappear hp q.1 q.2
  let q := repair .readyAck q.1 q.2
  compareLifecycle κ q.1 q.2

attribute [local irreducible] pPsiProbeWall PPLLFableZDiv.genSigOverwrite
  cleanSource releaseSource eliminateSig PPLLFableZDiv.moveSourceF dropStale preCheckReset
  normalizeReady checkSource disappear repair compareLifecycle
  suppressSigResetKill k4Kernel writeWithBundle conserve


private theorem throughCompare_spec {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : Cfg) {i bL bR : Nat} (hi : i ≤ ψ-3) {s t : MainState}
    (l r : AgentState ψ) (hs : Locked s) (ht : Mid t)
    (h : Shape i (i+1) bL bR s t (l,r)) :
    let q := throughCompare hp κ c l r
    Hole q ∨ Shape i (i+1) bL bR (leftResult s t) (rightResult t) q := by
  have hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    change r.label.val = (l.label.val+1)%ψ
    rw [show l.label.val = i from h.1,show r.label.val = i+1 from h.2.1]
    rw [Nat.mod_eq_of_lt (by omega)]
  let p := pPsiProbeWall hp l r
  have hpv := pprime_snap hp l r hn
  have hps : Shape i (i+1) bL bR s t p := shape_snap h hpv.1 hpv.2
  have hpl : p.1.path ≠ .bot := by rw [hps.2.2.1]; simp
  have hpr : p.2.path ≠ .bot := by rw [hps.2.2.2.1]; simp
  have hpn : p.1.state ≠ .produce := by
    have hx := hps.2.2.2.2.2.2.1
    rcases hs with hs | hs <;> simp_all
  have hpd : p.1.state ≠ .done := by
    have hx := hps.2.2.2.2.2.2.1
    rcases hs with hs | hs <;> simp_all
  have hrn : p.2.state ≠ .produce := by
    have hx := hps.2.2.2.2.2.2.2.1
    rcases ht with ht | ht | ht <;> simp_all
  let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
  have hgv := gen_snap hp κ p.1 p.2 hpl hpr hpn hpd hrn
  have hg : Shape i (i+1) bL bR s t g := shape_snap hps hgv.1 hgv.2
  let a := cleanSource hp g.1 g.2
  have ha : Hole a ∨ Shape i (i+1) bL bR s t a := by
    by_cases hh : Hole a
    · exact Or.inl hh
    · exact Or.inr (shape_snap hg (Clean.clean_snap hp g.1 g.2 hh).1 (Clean.clean_snap hp g.1 g.2 hh).2)
  let b := releaseSource hp a.1 a.2
  have hb : Hole b ∨ Shape i (i+1) bL bR s t b :=
    step (fun q => releaseSource hp q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.releaseSource_mono hp q.1 q.2)) ha
      (fun hh => Or.inr (by simpa only [b,internal_release hp a.1 a.2 ht hh] using hh))
  let d := eliminateSig hp b.1 b.2
  have hd : Hole d ∨ Shape i (i+1) bL bR s t d :=
    step (fun q => eliminateSig hp q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.eliminate_mono hp q.1 q.2)) hb
      (fun hh => Or.inr (by simpa only [d,internal_eliminate hp b.1 b.2 ht hh] using hh))
  let e := PPLLFableZDiv.moveSourceF hp sourceCfg d.1 d.2
  have he : Hole e ∨ Shape i (i+1) bL bR s t e :=
    step (fun q => PPLLFableZDiv.moveSourceF hp sourceCfg q.1 q.2)
      (fun q hh => hole_move hp q.1 q.2 hh) hd
      (fun hh => Or.inr (by simpa only [e,internal_move hp d.1 d.2 hs ht hh] using hh))
  let f := (dropStale e.1,dropStale e.2)
  have hf : Hole f ∨ Shape i (i+1) bL bR s t f :=
    step (fun q => (dropStale q.1,dropStale q.2))
      (fun q hh => hole_mono hh ⟨NoAlloc.drop_mono q.1,NoAlloc.drop_mono q.2⟩) he
      (fun hh => Or.inr (by simpa only [f,internal_drop e.1 e.2 hh] using hh))
  let j := preCheckReset f.1 f.2
  have hj : Hole j ∨ Shape i (i+1) bL bR s t j :=
    step (fun q => preCheckReset q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.precheck_mono q.1 q.2)) hf
      (fun hh => by
        by_cases hjj : Hole j
        · exact Or.inl hjj
        · exact Or.inr (shape_snap hh (precheck_snap f.1 f.2 hjj).1 (precheck_snap f.1 f.2 hjj).2))
  let n := (normalizeReady j.1,normalizeReady j.2)
  have hn : Hole n ∨ Shape i (i+1) bL bR s t n :=
    step (fun q => (normalizeReady q.1,normalizeReady q.2))
      (fun q hh => hole_mono hh ⟨NoAlloc.normalizeReady_mono q.1,NoAlloc.normalizeReady_mono q.2⟩) hj
      (fun hh => Or.inr (by simpa only [n,internal_normalize j.1 j.2 hs ht hh] using hh))
  let ch := checkSource hp c n.1 n.2
  have hch : Hole ch ∨ Shape i (i+1) bL bR s t ch :=
    step (fun q => checkSource hp c q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.checkSource_mono hp c q.1 q.2)) hn
      (fun hh => Or.inr (by simpa only [ch,internal_check hp c n.1 n.2 hs ht hh] using hh))
  let ds := disappear hp ch.1 ch.2
  have hds : Hole ds ∨ Shape i (i+1) bL bR s t ds :=
    step (fun q => disappear hp q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.disappear_mono hp q.1 q.2)) hch
      (fun hh => Or.inr (internal_disappear hp h4 hi ch.1 ch.2 hs ht hh))
  let rr := repair .readyAck ds.1 ds.2
  have hrr : Hole rr ∨ Shape i (i+1) bL bR s t rr :=
    step (fun q => repair .readyAck q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.repairReady_mono q.1 q.2)) hds
      (fun hh => Or.inr (by simpa only [rr,internal_repair h4 hi ds.1 ds.2 hs ht hh] using hh))
  let cp := compareLifecycle κ rr.1 rr.2
  have hcp : Hole cp ∨ Shape i (i+1) bL bR (leftResult s t) (rightResult t) cp :=
    step (fun q => compareLifecycle κ q.1 q.2)
      (fun q hh => hole_mono hh (NoAlloc.compareLifecycle_mono κ q.1 q.2)) hrr
      (fun hh => Or.inr (internal_compare h4 κ hi rr.1 rr.2 hs ht hh))
  simpa only [throughCompare,p,g,a,b,d,e,f,j,n,ch,ds,rr,cp] using hcp

/-- Labels and both original main-path payloads survive on their own holders,
and the two comparison-token slots remain empty. -/
def ExactFrame {ψ : Nat} (l r : AgentState ψ) (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.label = l.label ∧ q.2.label = r.label ∧
  q.1.path = l.path ∧ q.2.path = r.path ∧ q.1.path2 = none ∧ q.2.path2 = none

private theorem pipeline_factor {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) :
    pipeline hp κ c l r = Tail.finish hp l r (throughCompare hp κ c l r) := rfl

/-- Exact internal forward preparation table for the actual R5 row.
All ancillary fields and main-path payloads are arbitrary. A departed successor
locks; an existing compare1 acknowledgement propagates left. Every surviving
branch keeps both physical labels, holder paths and empty token slots. -/
theorem internal_row {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : Cfg) (i : Nat) (hi : i ≤ ψ-3)
    (l r : AgentState ψ) (bL bR : Nat)
    (hl : l.label.val = i) (hr : r.label.val = i+1)
    (pl : l.path = .some i bL) (pr : r.path = .some (i+1) bR)
    (tl : l.path2 = none) (tr : r.path2 = none)
    (ll : l.leader = false) (lr : r.leader = false)
    (sl : Locked l.state) (sr : Mid r.state) :
    let q := pipeline hp κ c l r
    q.1.path = .bot ∨ q.2.path = .bot ∨
      (ExactFrame l r q ∧ q.1.state = leftResult l.state r.state ∧
        q.2.state = rightResult r.state) := by
  have hin : Shape i (i+1) bL bR l.state r.state (l,r) :=
    ⟨hl,hr,pl,pr,tl,tr,rfl,rfl,ll,lr⟩
  let x := throughCompare hp κ c l r
  have hx := throughCompare_spec hp h4 κ c hi l r sl sr hin
  change Hole x ∨ Shape i (i+1) bL bR (leftResult l.state r.state) (rightResult r.state) x at hx
  let q := Tail.finish hp l r x
  have hm := Tail.finish_mono hp l r x
  change Tail.Mono x.1 q.1 ∧ Tail.Mono x.2 q.2 at hm
  dsimp only
  rw [pipeline_factor]
  change q.1.path = .bot ∨ q.2.path = .bot ∨ _
  rcases hm.1 with hbot | hleft
  · exact Or.inl hbot
  rcases hm.2 with hbot | hright
  · exact Or.inr (Or.inl hbot)
  have hpl := Tail.view_path hleft
  have hpr := Tail.view_path hright
  rcases hx with hh | hn
  · rcases hh with hh | hh
    · exact Or.inl (hpl.trans hh)
    · exact Or.inr (Or.inl (hpr.trans hh))
  · right; right
    rcases hn with ⟨xl,xr,xpl,xpr,xtl,xtr,xsl,xsr,_,_⟩
    have eql : q.1.label = l.label := (Tail.view_label hleft).trans (Fin.ext (xl.trans hl.symm))
    have eqr : q.2.label = r.label := (Tail.view_label hright).trans (Fin.ext (xr.trans hr.symm))
    exact ⟨⟨eql,eqr,hpl.trans (xpl.trans pl.symm),hpr.trans (xpr.trans pr.symm),
      (Tail.view_path2 hleft).trans xtl,(Tail.view_path2 hright).trans xtr⟩,
      (Tail.view_state hleft).trans xsl,(Tail.view_state hright).trans xsr⟩

/-- The reverse preparation row propagates compare1 to both endpoints,
unless the completed actual row leaves a main-path hole. -/
theorem reverse_row {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : Cfg) (i : Nat) (hi : i ≤ ψ-3)
    (l r : AgentState ψ) (bL bR : Nat)
    (hl : l.label.val = i) (hr : r.label.val = i+1)
    (pl : l.path = .some i bL) (pr : r.path = .some (i+1) bR)
    (tl : l.path2 = none) (tr : r.path2 = none)
    (ll : l.leader = false) (lr : r.leader = false)
    (sl : Locked l.state) (sr : r.state = .compare1) :
    let q := pipeline hp κ c l r
    q.1.path = .bot ∨ q.2.path = .bot ∨
      (ExactFrame l r q ∧ q.1.state = .compare1 ∧ q.2.state = .compare1) := by
  have h := internal_row hp h4 κ c i hi l r bL bR hl hr pl pr tl tr ll lr sl (Or.inr (Or.inr sr))
  rcases sl with hs | hs <;> simpa [leftResult,rightResult,hs,sr] using h

#print axioms internal_row
#print axioms reverse_row
end PrepInternal
end PPLLAstraR5Repair
