import Leader.Wu.ZeroDivisible.CheckRepair

/-!
# Occupied non-producer path frames for the actual R5 row

Two occupied, non-produce inputs cross GEN without new main-path allocation.
After GEN, cellwise stages only retain or delete paths and never create
produce. MOVE may relocate a path, but then leaves an endpoint empty.
`FrameOrHole` composes these facts through the exact R5 CHECK, K4, WRITE,
and conservation stages. The exported statements cover arbitrary raw fields,
leaders, labels, positive psi, kappa, and either R5 guard.

This proves the D0/F0 row contracts only; it does not prove a comparison
schedule, token provenance, terminal drainage, or global convergence.
-/

namespace PPLLAstraR5Repair


namespace D0F0


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


private theorem pprime_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CoreView (pPsiProbeWall hp l r).1 = CoreView l ∧
    CoreView (pPsiProbeWall hp l r).2 = CoreView r := by
  simp only [pPsiProbeWall, pPsi, fst_ite, snd_ite, view_ite,
    CoreView, state_ite, path_ite, ite_self, and_self]


private theorem wait_view {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    CoreView (waitSaturated hp κ l r).1 = CoreView l ∧
    CoreView (waitSaturated hp κ l r).2 = CoreView r := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish,
    fst_ite, snd_ite, view_ite, CoreView, state_ite, path_ite,
    ite_self, and_self]


private theorem gen_full_frame {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hrs : r.state ≠ .produce) :
    let q := PPLLFableZDiv.genSigOverwrite hp κ true 0 l r
    q.1.path = l.path ∧ q.2.path = r.path ∧
      q.1.state ≠ .produce ∧ q.2.state ≠ .produce := by
  have hw := wait_view hp κ l r
  generalize he : waitSaturated hp κ l r = q at hw
  have qlp : q.1.path ≠ .bot := by
    rw [view_path hw.1]
    exact hlp
  have qrp : q.2.path ≠ .bot := by
    rw [view_path hw.2]
    exact hrp
  have qls : q.1.state ≠ .produce := by
    intro h
    apply hls
    rw [← view_state hw.1]
    exact h
  have qrs : q.2.state ≠ .produce := by
    intro h
    apply hrs
    rw [← view_state hw.2]
    exact h
  by_cases hf : q.1.label = ⟨0, hp⟩ ∧ q.1.state = .done
  · simp [PPLLFableZDiv.genSigOverwrite, he, hlp, hrp, hls, hrs, qlp, qrp, qls, qrs, hf,
      genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
      view_path hw.1, view_path hw.2]
  · simp [PPLLFableZDiv.genSigOverwrite, he, hlp, hrp, hls, hrs, qlp, qrp, qls, qrs, hf,
      genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
      view_path hw.1, view_path hw.2]


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


attribute [local irreducible] pPsiProbeWall PPLLFableZDiv.genSigOverwrite
  cleanSource releaseSource eliminateSig PPLLFableZDiv.moveSourceF dropStale preCheckReset
  normalizeReady checkSource disappear repair compareLifecycle
  suppressSigResetKill k4Kernel writeWithBundle conserve

/-- Complete actual R5 row: two occupied non-producers yield a hole or
preserve both original PathInfo records and both non-producer states.
All other raw fields, including input leaders, are unrestricted. -/
theorem pipeline_D0F0_raw {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : Cfg) (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hrs : r.state ≠ .produce) :
    let o := pipeline hp κ c l r
    o.1.path = .bot ∨ o.2.path = .bot ∨
      (o.1.path = l.path ∧ o.2.path = r.path ∧
        o.1.state ≠ .produce ∧ o.2.state ≠ .produce) := by
  let p := pPsiProbeWall hp l r
  have hpv := pprime_view hp l r


  let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
  have hg0 := gen_full_frame hp κ p.1 p.2
    (by rw [view_path hpv.1]; exact hlp)
    (by rw [view_path hpv.2]; exact hrp)
    (by
      intro h
      apply hls
      rw [← view_state hpv.1]
      exact h)
    (by
      intro h
      apply hrs
      rw [← view_state hpv.2]
      exact h)
  have hg : FrameOrHole l r g.1 g.2 := by
    right
    right
    exact ⟨
      hg0.1.trans (view_path hpv.1),
      hg0.2.1.trans (view_path hpv.2),
      hg0.2.2.1,
      hg0.2.2.2⟩


  let a := cleanSource hp g.1 g.2
  have ha : FrameOrHole l r a.1 a.2 :=
    frameOrHole_mono hg (cleanSource_mono hp g.1 g.2)


  let b := releaseSource hp a.1 a.2
  have hb : FrameOrHole l r b.1 b.2 :=
    frameOrHole_mono ha (releaseSource_mono hp a.1 a.2)


  let d := eliminateSig hp b.1 b.2
  have hd : FrameOrHole l r d.1 d.2 :=
    frameOrHole_mono hb (eliminate_mono hp b.1 b.2)


  let e := PPLLFableZDiv.moveSourceF hp sourceCfg d.1 d.2
  have he : FrameOrHole l r e.1 e.2 :=
    moveSourceF_frameOrHole hp sourceCfg l r d.1 d.2 hd


  let f := (dropStale e.1, dropStale e.2)
  have hf : FrameOrHole l r f.1 f.2 :=
    frameOrHole_mono he ⟨drop_mono e.1, drop_mono e.2⟩


  let j := preCheckReset f.1 f.2
  have hj : FrameOrHole l r j.1 j.2 :=
    frameOrHole_mono hf (precheck_mono f.1 f.2)


  let n := (normalizeReady j.1, normalizeReady j.2)
  have hn : FrameOrHole l r n.1 n.2 :=
    frameOrHole_mono hj
      ⟨normalizeReady_mono j.1, normalizeReady_mono j.2⟩


  let ch := checkSource hp c n.1 n.2
  have hch : FrameOrHole l r ch.1 ch.2 :=
    frameOrHole_mono hn (checkSource_mono hp c n.1 n.2)


  let ds := disappear hp ch.1 ch.2
  have hds : FrameOrHole l r ds.1 ds.2 :=
    frameOrHole_mono hch (disappear_mono hp ch.1 ch.2)


  let rr := repair .readyAck ds.1 ds.2
  have hrr : FrameOrHole l r rr.1 rr.2 :=
    frameOrHole_mono hds (repairReady_mono ds.1 ds.2)


  let cp := compareLifecycle κ rr.1 rr.2
  have hcp : FrameOrHole l r cp.1 cp.2 :=
    frameOrHole_mono hrr (compareLifecycle_mono κ rr.1 rr.2)


  let s := suppressSigResetKill hp cp.1 cp.2
  have hs : FrameOrHole l r s.1 s.2 :=
    frameOrHole_mono hcp (suppress_mono hp cp.1 cp.2)


  have hbefore :
      FrameOrHole l r
        (beforeElimination hp κ c l r).1
        (beforeElimination hp κ c l r).2 := by
    simpa only [beforeElimination, p, g, a, b, d, e, f, j, n, ch, ds, rr, cp, s]
      using hs


  let k := k4Kernel hp
    (beforeElimination hp κ c l r).1
    (beforeElimination hp κ c l r).2
  have hk : FrameOrHole l r k.1 k.2 := by
    exact frameOrHole_mono hbefore
      ⟨cellMono_of_view
          (kernel_view hp
            (beforeElimination hp κ c l r).1
            (beforeElimination hp κ c l r).2).1,
       cellMono_of_view
          (kernel_view hp
            (beforeElimination hp κ c l r).1
            (beforeElimination hp κ c l r).2).2⟩


  let w := writeWithBundle hp k.1 k.2
  have hw : FrameOrHole l r w.1 w.2 := by
    exact frameOrHole_mono hk
      ⟨cellMono_of_view (Writer.writeWithBundle_view hp k.1 k.2).1,
       cellMono_of_view (Writer.writeWithBundle_view hp k.1 k.2).2⟩


  have ho : FrameOrHole l r
      (conserve .head l r w).1
      (conserve .head l r w).2 :=
    frameOrHole_mono hw (conserve_mono l r w)


  simpa only [pipeline, k, w, FrameOrHole] using ho


/-- D0: a complete row either creates a hole or keeps both cells non-produce. -/
theorem pipeline_D0_raw {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : Cfg) (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hrs : r.state ≠ .produce) :
    let o := pipeline hp κ c l r
    o.1.path = .bot ∨ o.2.path = .bot ∨
      (o.1.state ≠ .produce ∧ o.2.state ≠ .produce) := by
  have h := pipeline_D0F0_raw hp κ c l r hlp hrp hls hrs
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h.2.2.1, h.2.2.2⟩)


/-- F0: a complete row either creates a hole or keeps each original path on its holder. -/
theorem pipeline_F0_raw {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : Cfg) (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hrs : r.state ≠ .produce) :
    let o := pipeline hp κ c l r
    o.1.path = .bot ∨ o.2.path = .bot ∨
      (o.1.path = l.path ∧ o.2.path = r.path) := by
  have h := pipeline_D0F0_raw hp κ c l r hlp hrp hls hrs
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)


#print axioms pipeline_D0F0_raw
#print axioms pipeline_D0_raw
#print axioms pipeline_F0_raw

end D0F0
end PPLLAstraR5Repair
