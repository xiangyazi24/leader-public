import Leader.Wu.ZeroDivisible.LotterySuffix

/-!
# Lottery-field frame before DISAPPEAR

The actual R5 prefix through guarded CHECK has no lottery increment. A
comparison clear may reset `p` and `p_carry`, but also removes that holder's
main path. The exported disjunction records the pair hole at this exact cut.
-/

namespace PPLLAstraR5LotteryPrefix

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
open PPLLAstraR5Repair

set_option autoImplicit false
set_option linter.unusedSimpArgs false

private def lottery {ψ : Nat} (u : AgentState ψ) := (u.p, u.p_carry)

private theorem lottery_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    lottery (if p then a else b) = if p then lottery a else lottery b := by
  split <;> rfl

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem pprime_lottery {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    lottery (pPsiProbeWall hp l r).1 = lottery l ∧
    lottery (pPsiProbeWall hp l r).2 = lottery r := by
  simp [pPsiProbeWall, pPsi, fst_ite, snd_ite,
    lottery_ite, lottery] <;> grind

private theorem wait_lottery {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    lottery (waitSaturated hp κ l r).1 = lottery l ∧
    lottery (waitSaturated hp κ l r).2 = lottery r := by
  simp [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish,
    fst_ite, snd_ite, lottery_ite, lottery] <;> grind

private theorem emit_lottery {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    lottery (genSigSaturatedEmit hp l r).1 = lottery l ∧
    lottery (genSigSaturatedEmit hp l r).2 = lottery r := by
  simp [genSigSaturatedEmit, lottery]

private theorem propagate_lottery {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    lottery (genSigSaturatedPropagate hp l r).1 = lottery l ∧
    lottery (genSigSaturatedPropagate hp l r).2 = lottery r := by
  simp [genSigSaturatedPropagate, lottery] <;> grind

private theorem finish_lottery {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    lottery (genSigSaturatedFinish hp l r).1 = lottery l ∧
    lottery (genSigSaturatedFinish hp l r).2 = lottery r := by
  simp [genSigSaturatedFinish, lottery]

private theorem gen_lottery {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    lottery (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1 = lottery l ∧
    lottery (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2 = lottery r := by
  let w := waitSaturated hp κ l r
  let a :=
    if w.1.leader = false ∧ w.1.label = ⟨0, hp⟩ ∧ w.1.wait = false ∧
        w.1.path = .bot then PPLLFableZDiv.wipeProduce w.1 else w.1
  let b :=
    if w.2.label ≠ ⟨0, hp⟩ ∧ a.state = .produce ∧
        (w.2.path = .bot ∨ (w.2.state ≠ .produce ∧ w.2.state ≠ .done)) then
      PPLLFableZDiv.wipeProduce w.2 else w.2
  let e := genSigSaturatedEmit hp a b
  let p := genSigSaturatedPropagate hp e.1 e.2
  let f := genSigSaturatedFinish hp p.1 p.2
  have hdef : PPLLFableZDiv.genSigOverwrite hp κ true 0 l r = f := by
    simp [PPLLFableZDiv.genSigOverwrite, w, a, b, e, p, f]
  have hw := wait_lottery hp κ l r
  have ha : lottery a = lottery w.1 := by
    simp [a, PPLLFableZDiv.wipeProduce, lottery]
  have hb : lottery b = lottery w.2 := by
    simp [b, PPLLFableZDiv.wipeProduce, lottery]
  have he := emit_lottery hp a b
  have hprop := propagate_lottery hp e.1 e.2
  have hfin := finish_lottery hp p.1 p.2
  rw [hdef]
  exact ⟨hfin.1.trans (hprop.1.trans (he.1.trans (ha.trans hw.1))),
    hfin.2.trans (hprop.2.trans (he.2.trans (hb.trans hw.2)))⟩

private theorem cleanConnect_lottery {ψ : Nat} (u : AgentState ψ) :
    lottery (cleanSigGenConnect u) = lottery u := by
  cases h : u.path <;> simp [cleanSigGenConnect, h, lottery]

private theorem cleanApply_lottery {ψ : Nat} (u : AgentState ψ) :
    lottery (cleanSigCleanApply u) = lottery u := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    repeat (split <;> simp_all [lottery_ite, lottery])

private theorem clean3_lottery {ψ : Nat} (l r : AgentState ψ) :
    lottery (cleanSigStep3 l r).1 = lottery l ∧
    lottery (cleanSigStep3 l r).2 = lottery r := by
  cases h : r.path4 <;> cases hp : l.path <;>
    simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, lottery_ite, lottery]

private theorem clean4_lottery {ψ : Nat} (l r : AgentState ψ) :
    lottery (cleanSigStep4 l r).1 = lottery l ∧
    lottery (cleanSigStep4 l r).2 = lottery r := by
  cases h : l.path5 <;> cases hp : r.path <;>
    simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, lottery_ite, lottery]

private theorem clean5_lottery {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    lottery (cleanSigStep5 hp l r).1 = lottery l ∧
    lottery (cleanSigStep5 hp l r).2 = lottery r := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, lottery_ite, lottery]

private theorem clean6_lottery {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    lottery (cleanSigStep6 hp l r).1 = lottery l ∧
    lottery (cleanSigStep6 hp l r).2 = lottery r := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, lottery_ite, lottery]

private theorem clean_lottery {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    lottery (cleanSource hp l r).1 = lottery l ∧
    lottery (cleanSource hp l r).2 = lottery r := by
  have h4 (u : AgentState ψ) : lottery {u with path4 := none} = lottery u := rfl
  have h5 (u : AgentState ψ) : lottery {u with path5 := none} = lottery u := rfl
  simp only [cleanSource, fst_ite, snd_ite, lottery_ite,
    h4, h5, cleanConnect_lottery, cleanApply_lottery,
    (clean3_lottery _ _).1, (clean3_lottery _ _).2,
    (clean4_lottery _ _).1, (clean4_lottery _ _).2,
    (clean5_lottery _ _ _).1, (clean5_lottery _ _ _).2,
    (clean6_lottery _ _ _).1, (clean6_lottery _ _ _).2,
    ite_self, and_self]

private theorem release_lottery {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    lottery (releaseSource hp l r).1 = lottery l ∧
    lottery (releaseSource hp l r).2 = lottery r := by
  simp [releaseSource, lottery, fst_ite, snd_ite, lottery_ite]

private theorem eliminate_lottery {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    lottery (eliminateSig hp l r).1 = lottery l ∧
    lottery (eliminateSig hp l r).2 = lottery r := by
  simp [eliminateSig, lottery, fst_ite, snd_ite, lottery_ite]

private def CellMono {ψ : Nat} (u v : AgentState ψ) : Prop :=
  v.path = .bot ∨ (v.path = u.path ∧ lottery v = lottery u)

private def PairFrame {ψ : Nat} (l0 r0 l r : AgentState ψ) : Prop :=
  l.path = .bot ∨ r.path = .bot ∨
    (lottery l = lottery l0 ∧ lottery r = lottery r0)

private theorem cell_refl {ψ : Nat} (u : AgentState ψ) : CellMono u u :=
  Or.inr ⟨rfl, rfl⟩

private theorem cell_clear {ψ : Nat} (u : AgentState ψ) :
    CellMono u (clearCmp u) := Or.inl rfl

private theorem cell_state {ψ : Nat} (u : AgentState ψ) (s : MainState) :
    CellMono u {u with state := s} := Or.inr ⟨rfl, rfl⟩

private theorem cell_trans {ψ : Nat} {a b c : AgentState ψ}
    (h1 : CellMono a b) (h2 : CellMono b c) : CellMono a c := by
  rcases h2 with h | ⟨hp,hl⟩
  · exact Or.inl h
  rcases h1 with h | ⟨hp',hl'⟩
  · exact Or.inl (hp.trans h)
  · exact Or.inr ⟨hp.trans hp', hl.trans hl'⟩

private theorem pair_mono {ψ : Nat} {l0 r0 l r a b : AgentState ψ}
    (h : PairFrame l0 r0 l r)
    (ha : CellMono l a) (hb : CellMono r b) :
    PairFrame l0 r0 a b := by
  rcases h with hL | hR | hF
  · rcases ha with h | ⟨h,_⟩
    · exact Or.inl h
    · exact Or.inl (h.trans hL)
  · rcases hb with h | ⟨h,_⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inl (h.trans hR))
  · rcases ha with h | ⟨_,ha⟩
    · exact Or.inl h
    rcases hb with h | ⟨_,hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨ha.trans hF.1, hb.trans hF.2⟩)

private theorem moveTokens_mono {ψ : Nat} (l r : AgentState ψ) :
    CellMono l (moveTokens l r).1 ∧ CellMono r (moveTokens l r).2 := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [moveTokens, hl, hr, CellMono, lottery] <;>
    grind

private theorem consume_mono {ψ : Nat} (hp : ψ > 0)
    (u : AgentState ψ) :
    CellMono u (sigMoveApplyControlConsume hp u) := by
  cases h : u.path2 <;>
    simp [sigMoveApplyControlConsume, h, CellMono, lottery] <;> grind

private theorem leaderWall_mono {ψ : Nat} (l r : AgentState ψ) :
    CellMono l (leaderWall l r).1 ∧
    CellMono r (leaderWall l r).2 := by
  simp [leaderWall, CellMono, clearCmp, lottery] <;> grind

private theorem step1_frame {ψ : Nat} (z : PPLLFableZDiv.Cfg)
    (l0 r0 l r : AgentState ψ) (h : PairFrame l0 r0 l r) :
    PairFrame l0 r0
      (PPLLFableZDiv.sigMoveStep1F z l r).1
      (PPLLFableZDiv.sigMoveStep1F z l r).2 := by
  cases hl : l.path with
  | bot =>
      simp [PPLLFableZDiv.sigMoveStep1F, hl, PairFrame]
  | some _ _ =>
      cases hr : r.path with
      | some _ _ =>
          simpa [PPLLFableZDiv.sigMoveStep1F, hl, hr] using h
      | bot =>
          simp only [PPLLFableZDiv.sigMoveStep1F, hl, hr]
          repeat (split <;> simp_all [PairFrame, hl, hr, lottery])
          all_goals grind [PairFrame]

private theorem move_frame {ψ : Nat} (hp : ψ > 0)
    (l0 r0 l r : AgentState ψ) (h : PairFrame l0 r0 l r) :
    PairFrame l0 r0
      (PPLLFableZDiv.moveSourceF hp sourceCfg l r).1
      (PPLLFableZDiv.moveSourceF hp sourceCfg l r).2 := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hp⟩
  let a := if l.leader = true ∨
      (r.leader = true ∧ r.label ≠ nextLabel) then clearCmp l else l
  let b := if r.leader = true then clearCmp r else r
  have ha : CellMono l a := by
    dsimp [a]
    split <;> first | exact cell_refl l | exact cell_clear l
  have hb : CellMono r b := by
    dsimp [b]
    split <;> first | exact cell_refl r | exact cell_clear r
  have h0 : PairFrame l0 r0 a b := pair_mono h ha hb
  let s := if a.state = .done then (a,b)
    else PPLLFableZDiv.sigMoveStep1F sourceCfg a b
  have hs : PairFrame l0 r0 s.1 s.2 := by
    dsimp [s]
    split
    · exact h0
    · exact step1_frame sourceCfg l0 r0 a b h0
  let t := moveTokens s.1 s.2
  have ht : PairFrame l0 r0 t.1 t.2 :=
    pair_mono hs (moveTokens_mono s.1 s.2).1
      (moveTokens_mono s.1 s.2).2
  let w := leaderWall t.1 t.2
  have hw : PairFrame l0 r0 w.1 w.2 :=
    pair_mono ht (leaderWall_mono t.1 t.2).1
      (leaderWall_mono t.1 t.2).2
  let x := sigMoveApplyControlConsume hp w.1
  let y := sigMoveApplyControlConsume hp w.2
  have hxy : PairFrame l0 r0 x y :=
    pair_mono hw (consume_mono hp w.1) (consume_mono hp w.2)
  let x' :=
    if y.state = .depart ∧ x.label.val < ψ - 1 ∧
        x.state = .CHECK_ready then {x with state := .depart} else x
  have hx : CellMono x x' := by
    dsimp [x']
    split
    · exact cell_state x .depart
    · exact cell_refl x
  have hfin : PairFrame l0 r0 x' y := pair_mono hxy hx (cell_refl y)
  simpa [PPLLFableZDiv.moveSourceF, nextLabel, a, b, s, t, w, x, y, x']
    using hfin

private theorem drop_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (dropStale u) := by
  simp [dropStale, CellMono, lottery] <;> grind

private theorem precheck_mono {ψ : Nat} (l r : AgentState ψ) :
    CellMono l (preCheckReset l r).1 ∧
    CellMono r (preCheckReset l r).2 := by
  simp [preCheckReset, CellMono, clearCmp, lottery] <;> grind

private theorem orphan_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (normalizeOrphan u) := by
  cases hp : u.path <;>
    simp [CellMono, normalizeOrphan, hp, lottery] <;>
    repeat (first | split) <;> simp_all [CellMono, lottery]

private theorem carrier_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (normalizeCarrier u) := by
  cases hp : u.path <;>
    simp [CellMono, normalizeCarrier, releaseCongest, hp, lottery] <;>
    repeat (first | split) <;> simp_all [CellMono, lottery]

private theorem ready_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (normalizeReady u) := by
  generalize ho : normalizeOrphan u = o
  have hO := orphan_mono u
  rw [ho] at hO
  let c := if o.state = .none ∧ aligned o then o else normalizeCarrier o
  have hC : CellMono o c := by
    dsimp [c]
    split
    · exact cell_refl o
    · exact carrier_mono o
  have hOC := cell_trans hO hC
  have hF : CellMono c (normalizeReady u) := by
    simp only [normalizeReady, ho]
    change CellMono c
      (if c.leader then c else
       match c.path with
       | .bot => c
       | .some pl _ =>
         if c.state = .produce then
           {c with state := if pl = c.label.val then .none else .depart}
         else if (c.state = .equal ∨ c.state = .larger ∨
             c.state = .less) ∧ pl ≠ c.label.val then
           {c with state := .depart}
         else c)
    cases hp : c.path <;>
      simp [CellMono, hp, lottery] <;>
      repeat (first | split) <;> simp_all [CellMono, lottery]
  exact cell_trans hOC hF

private theorem readyGuarded_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (checkSigSetReadyGuarded u) := by
  cases hp : u.path <;>
    simp [CellMono, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, hp, lottery] <;>
    repeat (first | split) <;> simp_all [CellMono, lottery]

private def r5Ready {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if waveState u.state ∨ u.state = .congest ∨ u.state = .done then u
  else checkSigSetReadyGuarded u

private theorem r5Ready_mono {ψ : Nat} (u : AgentState ψ) :
    CellMono u (r5Ready u) := by
  unfold r5Ready
  split
  · exact cell_refl u
  · exact readyGuarded_mono u

private theorem releaseEqual_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CellMono l (releaseEqual hp l r) := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [CellMono, releaseEqual, hl, hr, lottery] <;>
    repeat (first | split) <;> simp_all [CellMono, lottery]

private theorem checkL_mono {ψ : Nat} (hp : ψ > 0)
    (u : AgentState ψ) :
    CellMono u (checkSigCheckL hp u) := by
  unfold checkSigCheckL
  repeat (first | split) <;> simp_all [CellMono, lottery, checkBit]
  all_goals grind

private theorem checkR_mono {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    CellMono r (checkSigCheckR hp l r) := by
  unfold checkSigCheckR
  repeat (first | split) <;> simp_all [CellMono, lottery, checkBit]
  all_goals grind

private theorem setResult_mono {ψ : Nat} (c : PPLLAstraR5Repair.Cfg)
    (u : AgentState ψ) :
    CellMono u (setResult c u) := by
  cases h : u.path2 <;>
    simp [CellMono, setResult, preserveToken, h,
      checkSigSetResult, lottery] <;> grind

private theorem checkSource_mono {ψ : Nat} (hp : ψ > 0)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    CellMono l (PPLLAstraR5Repair.checkSource hp c l r).1 ∧
    CellMono r (PPLLAstraR5Repair.checkSource hp c l r).2 := by
  let l0 := r5Ready l
  let r0 := r5Ready r
  let l1 := releaseEqual hp l0 r0
  let l2 := checkSigCheckL hp l1
  let r1 := checkSigCheckR hp l2 r0
  let l3 := setResult c l2
  let r2 := setResult c r1
  have hL : CellMono l l3 :=
    cell_trans (r5Ready_mono l)
      (cell_trans (releaseEqual_mono hp l0 r0)
        (cell_trans (checkL_mono hp l1) (setResult_mono c l2)))
  have hR : CellMono r r2 :=
    cell_trans (r5Ready_mono r)
      (cell_trans (checkR_mono hp l2 r0) (setResult_mono c r1))
  have hLast : CellMono r
      (if r2.label = ⟨ψ-1, by omega⟩ ∧ r2.state = .equal then
        {r2 with leader := true} else r2) := by
    -- The comparison birth changes only the responder's leader flag.
    have h : CellMono r2
        (if r2.label = ⟨ψ-1, by omega⟩ ∧ r2.state = .equal then
          {r2 with leader := true} else r2) := by
      split <;> exact Or.inr ⟨rfl,rfl⟩
    exact cell_trans hR h
  have hPair : CellMono l l3 ∧ CellMono r
      (if r2.label = ⟨ψ-1, by omega⟩ ∧ r2.state = .equal then
        {r2 with leader := true} else r2) := ⟨hL,hLast⟩
  have hdef : PPLLAstraR5Repair.checkSource hp c l r =
      (if r2.label = ⟨ψ-1, by omega⟩ ∧ r2.state = .equal then
        (l3, {r2 with leader := true}) else (l3, r2)) := rfl
  rw [hdef]
  simpa only [fst_ite, snd_ite, ite_self] using hPair

-- Keep stage bodies behind their proved interfaces during composition.
-- This is the same elaboration boundary used by FullOwnFrame and PathFrame.
attribute [local irreducible] pPsiProbeWall PPLLFableZDiv.genSigOverwrite
  cleanSource releaseSource eliminateSig PPLLFableZDiv.moveSourceF dropStale
  preCheckReset normalizeReady PPLLAstraR5Repair.checkSource

/-- The actual pre-DISAPPEAR cut has a pair hole, or both lottery registers
still equal their original input values. No state or path premise is carried. -/
theorem throughCheck_lottery_or_hole {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    let ch := PPLLAstraR5Repair.SuffixInterfaces.throughCheck hp κ c l r
    ch.1.path = .bot ∨ ch.2.path = .bot ∨
      ((ch.1.p,ch.1.p_carry) = (l.p,l.p_carry) ∧
       (ch.2.p,ch.2.p_carry) = (r.p,r.p_carry)) := by
  change PairFrame l r
    (PPLLAstraR5Repair.SuffixInterfaces.throughCheck hp κ c l r).1
    (PPLLAstraR5Repair.SuffixInterfaces.throughCheck hp κ c l r).2
  unfold PPLLAstraR5Repair.SuffixInterfaces.throughCheck
  generalize hpCut : pPsiProbeWall hp l r = p
  have hp0 := pprime_lottery hp l r
  rw [hpCut] at hp0
  generalize hgCut : PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2 = g
  have hg0 := gen_lottery hp κ p.1 p.2
  rw [hgCut] at hg0
  generalize haCut : cleanSource hp g.1 g.2 = a
  have ha0 := clean_lottery hp g.1 g.2
  rw [haCut] at ha0
  generalize hbCut : releaseSource hp a.1 a.2 = b
  have hb0 := release_lottery hp a.1 a.2
  rw [hbCut] at hb0
  generalize hdCut : eliminateSig hp b.1 b.2 = d
  have hd0 := eliminate_lottery hp b.1 b.2
  rw [hdCut] at hd0
  have hd : PairFrame l r d.1 d.2 := Or.inr (Or.inr
    ⟨hd0.1.trans (hb0.1.trans (ha0.1.trans (hg0.1.trans hp0.1))),
     hd0.2.trans (hb0.2.trans (ha0.2.trans (hg0.2.trans hp0.2)))⟩)
  generalize hmCut : PPLLFableZDiv.moveSourceF hp sourceCfg d.1 d.2 = m
  have hm := move_frame hp l r d.1 d.2 hd
  rw [hmCut] at hm
  generalize hdsCut : (dropStale m.1, dropStale m.2) = ds
  have hds := pair_mono hm (drop_mono m.1) (drop_mono m.2)
  change PairFrame l r (dropStale m.1, dropStale m.2).1
    (dropStale m.1, dropStale m.2).2 at hds
  rw [hdsCut] at hds
  generalize hprCut : preCheckReset ds.1 ds.2 = pr
  have hpr := pair_mono hds (precheck_mono ds.1 ds.2).1
    (precheck_mono ds.1 ds.2).2
  rw [hprCut] at hpr
  generalize hnrCut : (normalizeReady pr.1, normalizeReady pr.2) = nr
  have hnr := pair_mono hpr (ready_mono pr.1) (ready_mono pr.2)
  change PairFrame l r (normalizeReady pr.1, normalizeReady pr.2).1
    (normalizeReady pr.1, normalizeReady pr.2).2 at hnr
  rw [hnrCut] at hnr
  generalize hchCut : PPLLAstraR5Repair.checkSource hp c nr.1 nr.2 = ch
  have hch := pair_mono hnr (checkSource_mono hp c nr.1 nr.2).1
    (checkSource_mono hp c nr.1 nr.2).2
  rw [hchCut] at hch
  have hdsL : dropStale m.1=ds.1 := congrArg Prod.fst hdsCut
  have hdsR : dropStale m.2=ds.2 := congrArg Prod.snd hdsCut
  have hnrL : normalizeReady pr.1=nr.1 := congrArg Prod.fst hnrCut
  have hnrR : normalizeReady pr.2=nr.2 := congrArg Prod.snd hnrCut
  simpa only [hgCut,haCut,hbCut,hdCut,hmCut,hdsL,hdsR,hprCut,hnrL,hnrR,hchCut]
    using hch

/-- A cut hole is a final pair hole by the verified actual suffix; otherwise
the pre-DISAPPEAR lottery registers equal the original inputs. -/
theorem pipeline_cut_lottery_or_final_hole {ψ : Nat}
    (hp : ψ > 0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) :
    let ch := PPLLAstraR5Repair.SuffixInterfaces.throughCheck hp κ c l r
    let z := PPLLAstraR5Repair.pipeline hp κ c l r
    z.1.path = .bot ∨ z.2.path = .bot ∨
      ((ch.1.p,ch.1.p_carry) = (l.p,l.p_carry) ∧
       (ch.2.p,ch.2.p_carry) = (r.p,r.p_carry)) := by
  rw [PPLLAstraR5Repair.SuffixInterfaces.pipeline_eq_from_check]
  generalize hcut : PPLLAstraR5Repair.SuffixInterfaces.throughCheck hp κ c l r = ch
  have h := throughCheck_lottery_or_hole hp κ c l r
  rw [hcut] at h
  rcases h with hL | hR | hF
  · have hz := PPLLAstraR5LotterySuffix.finishAfterCheck_pairHole
      hp κ l r ch.1 ch.2 (Or.inl hL)
    exact hz.elim Or.inl (fun h => Or.inr (Or.inl h))
  · have hz := PPLLAstraR5LotterySuffix.finishAfterCheck_pairHole
      hp κ l r ch.1 ch.2 (Or.inr hR)
    exact hz.elim Or.inl (fun h => Or.inr (Or.inl h))
  · exact Or.inr (Or.inr hF)

#print axioms throughCheck_lottery_or_hole
#print axioms pipeline_cut_lottery_or_final_hole

end PPLLAstraR5LotteryPrefix
