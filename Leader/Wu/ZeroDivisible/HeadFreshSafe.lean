import Leader.Wu.ZeroDivisible.K4BoundaryEquality
import Leader.Wu.ZeroDivisible.HeadReset
import Leader.Wu.Safety.ConcreteProtocolProperties
/-! Fresh comparison safety for Head on successor-aligned ψ≥3 edges.
GENSIG can temporarily create nonterminal DONE; its path provenance is kept
until CHECK/COMPARE discharge that temporary state. -/
namespace PPLLAstraFreshSafe
open PPLLElimVariants PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2
/-- The six comparison states generated without a comparison head carrier. -/
def StateOK : MainState → Prop
  | .none | .produce | .done | .depart | .CHECK_ready | .eliminate_signal => True
  | _ => False
/-- No main comparison carrier with sub-signal index zero. -/
def NoZero : PathInfo → Prop
  | .bot => True
  | .some a _ => a≠0
/-- Comparison traffic has no head or control token and stays in six states. -/
def Core {ψ : Nat} (u : AgentState ψ) : Prop :=
  StateOK u.state ∧ NoZero u.path ∧ u.path2=none
/-- Fresh comparison safety. DONE is permitted only at a terminal physical
label; all cleanup, writer, WAIT, suppression and elimination fields are free. -/
def Safe {ψ : Nat} (u : AgentState ψ) : Prop :=
  Core u ∧ (u.state=.done → u.label.val=ψ-1)
/-- Temporary initiator provenance after GENSIG: a nonterminal DONE still has
its own generated carrier, unless a later cleanup stage deleted that carrier. -/
def GenerationCut {ψ : Nat} (u : AgentState ψ) : Prop :=
  Core u ∧ (u.state=.done → u.label.val=ψ-1 ∨ u.path=.bot ∨
    ∃b, u.path=.some u.label.val b)
private theorem safe_left {ψ : Nat} (u : AgentState ψ) (h : Safe u) : GenerationCut u :=
  ⟨h.1,fun hd => Or.inl (h.2 hd)⟩
/-- Actual comparison clearing produces Safe with no ancillary assumptions. -/
theorem clear_safe {ψ : Nat} (u : AgentState ψ) : Safe (clearCmp u) := by
  simp [Safe,Core,StateOK,NoZero,clearCmp]
private def View {ψ : Nat} (u : AgentState ψ) := (u.label,u.state,u.path,u.path2,u.leader)
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    View (if p then a else b) = if p then View a else View b := by split <;> rfl
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem path2_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
private theorem safe_of_view {ψ : Nat} (a b : AgentState ψ) (h : View a=View b)
    (hb : Safe b) : Safe a := by
  simp only [View,Prod.mk.injEq] at h
  simpa only [Safe,Core,h.1,h.2.1,h.2.2.1,h.2.2.2.1] using hb
private theorem wait_view {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    View (waitSaturated hp κ l r).1=View l ∧ View (waitSaturated hp κ l r).2=View r := by
  simp only [waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,waitSaturatedReset,
    waitSaturatedFinish,fst_ite,snd_ite,view_ite,View,label_ite,state_ite,path_ite,path2_ite,leader_ite,ite_self,and_self]
private theorem start_safe {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : Safe l) (hr : Safe r) :
    Safe (genSigSaturatedStart hp l r).1 ∧ Safe (genSigSaturatedStart hp l r).2 := by
  unfold genSigSaturatedStart
  try dsimp only
  split <;> (try dsimp only) <;> (repeat split) <;> simp_all [Safe,Core,StateOK]
private theorem emit_safe {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (l r : AgentState ψ)
    (hl : Safe l) (hr : Safe r) :
    Safe (genSigSaturatedEmit hp l r).1 ∧ Safe (genSigSaturatedEmit hp l r).2 := by
  unfold genSigSaturatedEmit
  split
  · rename_i h
    have hv : r.label.val=ψ-1 := congrArg Fin.val h.1
    have hn : r.label.val≠0 := by omega
    simp_all [Safe,Core,StateOK,NoZero]
  · exact ⟨hl,hr⟩
private theorem propagate_cut {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hl : Safe l) (hr : Safe r) :
    GenerationCut (genSigSaturatedPropagate hp l r).1 ∧ Safe (genSigSaturatedPropagate hp l r).2 := by
  unfold genSigSaturatedPropagate
  split
  · rename_i h
    have hd := hr.2 h.2.2
    have hn : l.label.val≠0 := by
      intro hz
      have hv := congrArg Fin.val ha
      change r.label.val=(l.label.val+1)%ψ at hv
      rw [hz] at hv
      have hm : (0+1)%ψ=1 := Nat.mod_eq_of_lt (by omega)
      rw [hm] at hv
      omega
    constructor
    · simp [GenerationCut,Core,StateOK,NoZero,hn,hl.1.2.2]
    · exact ⟨⟨True.intro,hr.1.2.1,hr.1.2.2⟩,by intro h; cases h⟩
  · exact ⟨safe_left l hl,hr⟩
private theorem finish_cut {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    GenerationCut (genSigSaturatedFinish hp l r).1 ∧ Safe (genSigSaturatedFinish hp l r).2 := by
  unfold genSigSaturatedFinish
  split
  · constructor
    · exact ⟨⟨True.intro,hl.1.2.1,hl.1.2.2⟩,by intro h; cases h⟩
    · exact hr
  · exact ⟨hl,hr⟩
private theorem start_labels {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (genSigSaturatedStart hp l r).1.label=l.label ∧ (genSigSaturatedStart hp l r).2.label=r.label := by
  simp only [genSigSaturatedStart,fst_ite,snd_ite,label_ite,ite_self,and_self]
private theorem emit_labels {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (genSigSaturatedEmit hp l r).1.label=l.label ∧ (genSigSaturatedEmit hp l r).2.label=r.label := by
  simp only [genSigSaturatedEmit,fst_ite,snd_ite,label_ite,ite_self,and_self]
/-- Exact GENSIG cut: a head carrier cannot be created on a successor-aligned
ψ≥3 edge from Safe endpoints, even with arbitrary WAIT and counter fields. -/
theorem genSigSaturated_cut {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ) (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hl : Safe l) (hr : Safe r) :
    GenerationCut (genSigSaturated hp κ l r).1 ∧ Safe (genSigSaturated hp κ l r).2 := by
  have hw := wait_view hp κ l r
  let w := waitSaturated hp κ l r
  have hwL := safe_of_view w.1 l hw.1 hl
  have hwR := safe_of_view w.2 r hw.2 hr
  have hwlabL := congrArg Prod.fst hw.1
  have hwlabR := congrArg Prod.fst hw.2
  have hs := start_safe hp w.1 w.2 hwL hwR
  let s := genSigSaturatedStart hp w.1 w.2
  have hsLab := start_labels hp w.1 w.2
  have he := emit_safe hp h3 s.1 s.2 hs.1 hs.2
  let e := genSigSaturatedEmit hp s.1 s.2
  have heLab := emit_labels hp s.1 s.2
  have hal : e.2.label=⟨(e.1.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by
    change w.1.label=l.label at hwlabL
    change w.2.label=r.label at hwlabR
    rw [heLab.1,heLab.2,hsLab.1,hsLab.2,hwlabL,hwlabR]
    exact ha
  have ht := propagate_cut hp h3 e.1 e.2 hal he.1 he.2
  exact finish_cut hp _ _ ht.1 ht.2

/-! CLEAN only deletes main carriers and changes its private connection fields. -/
private def CleanFrame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.label=b.label ∧ a.state=b.state ∧ a.path2=b.path2 ∧ a.leader=b.leader ∧
    (a.path=b.path ∨ a.path=.bot)
private theorem cleanFrame_refl {ψ : Nat} (u : AgentState ψ) : CleanFrame u u :=
  ⟨rfl,rfl,rfl,rfl,Or.inl rfl⟩
private theorem cleanFrame_trans {ψ : Nat} {a b c : AgentState ψ}
    (hab : CleanFrame a b) (hbc : CleanFrame b c) : CleanFrame a c := by
  rcases hab with ⟨hl,hs,ht,hv,hp⟩
  rcases hbc with ⟨hl',hs',ht',hv',hp'⟩
  refine ⟨hl.trans hl',hs.trans hs',ht.trans ht',hv.trans hv',?_⟩
  rcases hp with hp | hp
  · rw [hp]; exact hp'
  · exact Or.inr hp
private theorem cleanFrame_core {ψ : Nat} {a b : AgentState ψ}
    (hf : CleanFrame a b) (hb : Core b) : Core a := by
  refine ⟨?_,?_,?_⟩
  · simpa only [hf.2.1] using hb.1
  · rcases hf.2.2.2.2 with h | h
    · simpa only [h] using hb.2.1
    · simp [h,NoZero]
  · exact hf.2.2.1.trans hb.2.2
private theorem cleanFrame_safe {ψ : Nat} {a b : AgentState ψ}
    (hf : CleanFrame a b) (hb : Safe b) : Safe a := by
  refine ⟨cleanFrame_core hf hb.1,?_⟩
  intro hd
  rw [hf.1]
  exact hb.2 (hf.2.1.symm.trans hd)
private theorem cleanFrame_cut {ψ : Nat} {a b : AgentState ψ}
    (hf : CleanFrame a b) (hb : GenerationCut b) : GenerationCut a := by
  refine ⟨cleanFrame_core hf hb.1,?_⟩
  intro hd
  rcases hb.2 (hf.2.1.symm.trans hd) with ht | ht | ⟨bit,ht⟩
  · exact Or.inl ((congrArg Fin.val hf.1).trans ht)
  · rcases hf.2.2.2.2 with hp | hp
    · exact Or.inr (Or.inl (hp.trans ht))
    · exact Or.inr (Or.inl hp)
  · rcases hf.2.2.2.2 with hp | hp
    · exact Or.inr (Or.inr ⟨bit,by rw [hp,hf.1]; exact ht⟩)
    · exact Or.inr (Or.inl hp)
private theorem clean_connect_frame {ψ : Nat} (u : AgentState ψ) :
    CleanFrame (cleanSigGenConnect u) u := by
  unfold cleanSigGenConnect
  split <;> (repeat first | dsimp only | split) <;> simp [CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
private theorem clean_apply_frame {ψ : Nat} (u : AgentState ψ) :
    CleanFrame (cleanSigCleanApply u) u := by
  cases hp : u.path with
  | bot => simp_all [cleanSigCleanApply,hp,CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
  | some pl pb =>
    by_cases hz : pl=0 <;> by_cases ht : pl=ψ-1
    all_goals
      cases h4 : u.path4 with
      | none =>
        cases h5 : u.path5 with
        | none => simp_all [cleanSigCleanApply,hp,h4,h5,CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
        | some p5 =>
          rcases p5 with ⟨z5,b5⟩
          by_cases hn5 : z5=(-1:Int) <;>
            simp_all [cleanSigCleanApply,hp,h4,h5,hz,ht,hn5,CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
      | some p4 =>
        rcases p4 with ⟨z4,b4⟩
        by_cases hn4 : z4=(-1:Int)
        all_goals
          cases h5 : u.path5 with
          | none => simp_all [cleanSigCleanApply,hp,h4,h5,hz,ht,hn4,CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
          | some p5 =>
            rcases p5 with ⟨z5,b5⟩
            by_cases hn5 : z5=(-1:Int) <;>
              simp_all [cleanSigCleanApply,hp,h4,h5,hz,ht,hn4,hn5,CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
private theorem clean_step3_frame {ψ : Nat} (l r : AgentState ψ) :
    CleanFrame (cleanSigStep3 l r).1 l ∧ CleanFrame (cleanSigStep3 l r).2 r := by
  unfold cleanSigStep3
  split <;> (repeat first | dsimp only | split) <;> simp [CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
private theorem clean_step4_frame {ψ : Nat} (l r : AgentState ψ) :
    CleanFrame (cleanSigStep4 l r).1 l ∧ CleanFrame (cleanSigStep4 l r).2 r := by
  unfold cleanSigStep4
  split <;> (repeat first | dsimp only | split) <;> simp [CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
private theorem clean_step5_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CleanFrame (cleanSigStep5 hp l r).1 l ∧ CleanFrame (cleanSigStep5 hp l r).2 r := by
  unfold cleanSigStep5
  split <;> (repeat first | dsimp only | split) <;> simp [CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
private theorem clean_step6_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CleanFrame (cleanSigStep6 hp l r).1 l ∧ CleanFrame (cleanSigStep6 hp l r).2 r := by
  unfold cleanSigStep6
  split <;> (repeat first | dsimp only | split) <;> simp [CleanFrame,label_ite,state_ite,path_ite,path2_ite,leader_ite]
private theorem clean_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CleanFrame (cleanSig hp l r).1 l ∧ CleanFrame (cleanSig hp l r).2 r := by
  let a := (cleanSigGenConnect l,cleanSigGenConnect r)
  let b := cleanSigStep3 a.1 a.2
  let c := cleanSigStep4 b.1 b.2
  let d := cleanSigStep5 hp c.1 c.2
  let e := cleanSigStep6 hp d.1 d.2
  have ha := And.intro (clean_connect_frame l) (clean_connect_frame r)
  have hb := clean_step3_frame a.1 a.2
  have hc := clean_step4_frame b.1 b.2
  have hd := clean_step5_frame hp c.1 c.2
  have he := clean_step6_frame hp d.1 d.2
  have hf := And.intro (clean_apply_frame e.1) (clean_apply_frame e.2)
  exact ⟨cleanFrame_trans hf.1 (cleanFrame_trans he.1 (cleanFrame_trans hd.1
    (cleanFrame_trans hc.1 (cleanFrame_trans hb.1 ha.1)))),
    cleanFrame_trans hf.2 (cleanFrame_trans he.2 (cleanFrame_trans hd.2
    (cleanFrame_trans hc.2 (cleanFrame_trans hb.2 ha.2))))⟩

private theorem stateOK_flags {s : MainState} (h : StateOK s) :
    waveState s=false ∧ lockedState s=false ∧ s≠.compare2 ∧ s≠.lock ∧ s≠.compare1 := by
  cases s <;> simp_all [StateOK,waveState,lockedState]
private theorem maintain_core {ψ : Nat} (l r : AgentState ψ)
    (hl : Core l) (hr : Core r) : maintain l r=(l,r) := by
  have fl := stateOK_flags hl.1
  have fr := stateOK_flags hr.1
  cases hp : l.path <;> cases hq : r.path <;>
    simp [maintain,hp,hq,fl.1,fl.2.1,fl.2.2.1,fr.2.1]
private theorem wave_core {ψ : Nat} (l r : AgentState ψ)
    (hl : Core l) (hr : Core r) : wave l r=(l,r) := by
  have fl := stateOK_flags hl.1
  have fr := stateOK_flags hr.1
  cases hp : l.path <;> cases hq : r.path <;>
    simp_all [wave,Core,NoZero]
private theorem compare_init_core {ψ : Nat} (l : AgentState ψ) (hl : Core l) :
    Core (compareSigInit l) := by
  cases hp : l.path <;> simp_all [compareSigInit,Core,NoZero,StateOK]
/-- On the fresh state family COMPARE has no lock, token or birth transition;
its only effect is the printed pathless-initiator state cleanup. -/
theorem compare_core_eq {ψ : Nat} (κ : Nat) (detect eqBirth : Bool)
    (l r : AgentState ψ) (hl : Core l) (hr : Core r) :
    compareSigF κ detect eqBirth l r=(compareSigInit l,r) := by
  have hi := compare_init_core l hl
  simp only [compareSigF,maintain_core _ _ hi hr,wave_core _ _ hi hr]
  simp [dropStray,landBackward,landForward,hi.2.2,hr.2.2]

private theorem eliminate_cut {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    GenerationCut (eliminateSig hp l r).1 ∧ Safe (eliminateSig hp l r).2 := by
  unfold eliminateSig
  split <;> (repeat first | dsimp only | split) <;>
    simp_all [GenerationCut,Safe,Core,StateOK,NoZero]
private theorem move_step1_cut {ψ : Nat} (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    GenerationCut (sigMoveStep1With .dropMisaligned l r).1 ∧
    Safe (sigMoveStep1With .dropMisaligned l r).2 := by
  cases hp : l.path <;> cases hq : r.path <;>
    simp only [sigMoveStep1With,hp,hq] <;>
    (repeat first | dsimp only | split) <;>
    simp_all [GenerationCut,Safe,Core,StateOK,NoZero]
private theorem drop_cut {ψ : Nat} (u : AgentState ψ) (h : GenerationCut u) :
    GenerationCut (dropStale u) := by
  unfold dropStale
  split <;> simp_all [GenerationCut,Core,StateOK,NoZero]
private theorem drop_safe {ψ : Nat} (u : AgentState ψ) (h : Safe u) :
    Safe (dropStale u) := by
  unfold dropStale
  split <;> simp_all [Safe,Core,StateOK,NoZero]
private theorem precheck_cut {ψ : Nat} (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    GenerationCut (preCheckReset l r).1 ∧ Safe (preCheckReset l r).2 := by
  unfold preCheckReset
  try dsimp only
  split <;> split <;> simp_all [GenerationCut,Safe,Core,StateOK,NoZero,clearCmp]

private theorem wall_cut {ψ : Nat} (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    GenerationCut (leaderWall l r).1 ∧ Safe (leaderWall l r).2 := by
  unfold leaderWall
  try dsimp only
  split <;> split <;> simp_all [GenerationCut,Safe,Core,StateOK,NoZero,clearCmp]
private theorem sigmove_cut {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    GenerationCut (sigMoveF hp true .dropMisaligned l r).1 ∧
    Safe (sigMoveF hp true .dropMisaligned l r).2 := by
  let a : AgentState ψ := if true ∧ (l.leader=true ∨
      (r.leader=true ∧ r.label≠⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)) then clearCmp l else l
  let b : AgentState ψ := if true ∧ r.leader=true then clearCmp r else r
  have ha : GenerationCut a := by
    dsimp only [a]; split
    · exact safe_left _ (clear_safe _)
    · exact hl
  have hb : Safe b := by
    dsimp only [b]; split
    · exact clear_safe _
    · exact hr
  let c := sigMoveStep1With .dropMisaligned a b
  have hc := move_step1_cut a b ha hb
  change GenerationCut c.1 ∧ Safe c.2 at hc
  have hm : moveTokens c.1 c.2=c := by
    simp [moveTokens,hc.1.1.2.2,hc.2.1.2.2]
  let d := leaderWall c.1 c.2
  have hd := wall_cut c.1 c.2 hc.1 hc.2
  change GenerationCut d.1 ∧ Safe d.2 at hd
  have hdL : sigMoveApplyControlConsume hp d.1=d.1 := by
    simp [sigMoveApplyControlConsume,hd.1.1.2.2]
  have hdR : sigMoveApplyControlConsume hp d.2=d.2 := by
    simp [sigMoveApplyControlConsume,hd.2.1.2.2]
  change GenerationCut (let q := moveTokens c.1 c.2
    let q := leaderWall q.1 q.2
    let l := sigMoveApplyControlConsume hp q.1
    let r := sigMoveApplyControlConsume hp q.2
    (if r.state=.depart then
      if l.label.val<ψ-1 ∧ l.state=.CHECK_ready then {l with state:=.depart} else l
      else l,r)).1 ∧ Safe (sigMoveApplyControlConsume hp
        (leaderWall (moveTokens c.1 c.2).1 (moveTokens c.1 c.2).2).2)
  change sigMoveApplyControlConsume hp (leaderWall c.1 c.2).1=(leaderWall c.1 c.2).1 at hdL
  change sigMoveApplyControlConsume hp (leaderWall c.1 c.2).2=(leaderWall c.1 c.2).2 at hdR
  simp only [hm,hdL,hdR]
  change GenerationCut (if d.2.state=.depart then
    if d.1.label.val<ψ-1 ∧ d.1.state=.CHECK_ready then {d.1 with state:=.depart} else d.1
    else d.1) ∧ Safe d.2
  split <;> (repeat split) <;> simp_all [GenerationCut,Core,StateOK]

/-- After CHECK, only a deleted-carrier DONE can remain nonterminal. -/
def CheckedCut {ψ : Nat} (u : AgentState ψ) : Prop :=
  Core u ∧ (u.state=.done → u.label.val=ψ-1 ∨ u.path=.bot)
private theorem ready_checked {ψ : Nat} (u : AgentState ψ) (h : GenerationCut u) :
    CheckedCut (readyF u) := by
  cases hp : u.path with
  | bot =>
    cases hs : u.state <;>
      simp_all [readyF,checkSigSetReadyGuarded,controlPending,checkSigSetReady,
        waveState,GenerationCut,CheckedCut,Core,StateOK,NoZero] <;> omega
  | some pl pb =>
    by_cases ha : u.label.val=pl
    all_goals cases hs : u.state <;>
      simp_all [readyF,checkSigSetReadyGuarded,controlPending,checkSigSetReady,
        waveState,GenerationCut,CheckedCut,Core,StateOK,NoZero] <;> omega
private theorem ready_safe {ψ : Nat} (u : AgentState ψ) (h : Safe u) : Safe (readyF u) := by
  cases hp : u.path with
  | bot =>
    cases hs : u.state <;>
      simp_all [readyF,checkSigSetReadyGuarded,controlPending,checkSigSetReady,
        waveState,Safe,Core,StateOK,NoZero] <;> omega
  | some pl pb =>
    by_cases ha : u.label.val=pl
    all_goals cases hs : u.state <;>
      simp_all [readyF,checkSigSetReadyGuarded,controlPending,checkSigSetReady,
        waveState,Safe,Core,StateOK,NoZero] <;> omega
private theorem core_not_equal {ψ : Nat} (u : AgentState ψ) (h : Core u) : u.state≠.equal := by
  intro he; simpa [he,StateOK] using h.1
private theorem checkL_core {ψ : Nat} (hp : ψ>0) (u : AgentState ψ) (h : Core u) :
    checkSigCheckL hp u=u := by
  cases hu : u.path with
  | bot => simp [checkSigCheckL,hu]
  | some pl pb =>
    have hn : pl≠0 := by simpa [NoZero,hu] using h.2.1
    cases pl <;> simp_all [checkSigCheckL,hu]
private theorem checkR_core {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) (hl : Core l) :
    checkSigCheckR hp l r=r := by
  have hn := core_not_equal l hl
  cases h : r.path <;> simp [checkSigCheckR,h,hn]
private theorem result_core {ψ : Nat} (u : AgentState ψ) (h : Core u) :
    checkSigSetResult u=u := by
  cases hs : u.state <;> simp_all [Core,StateOK,checkSigSetResult]
private theorem check_cut {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    CheckedCut (checkSigF hp κ false l r).1 ∧ Safe (checkSigF hp κ false l r).2 := by
  have ha := ready_checked l hl
  have hb := ready_safe r hr
  have hla := core_not_equal (readyF l) ha.1
  have hra := core_not_equal (readyF r) hb.1
  simp only [checkSigF,hla,and_false,false_and,ite_false,
    checkL_core hp _ ha.1,checkR_core hp _ _ ha.1,
    result_core _ ha.1,result_core _ hb.1,hra]
  exact ⟨ha,hb⟩

private theorem disappear_cut {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : CheckedCut l) (hr : Safe r) :
    CheckedCut (disappear hp l r).1 ∧ Safe (disappear hp l r).2 := by
  have hlt : l.state≠.toss := by intro h; simpa [h,StateOK] using hl.1.1
  have hrt : r.state≠.toss := by intro h; simpa [h,StateOK] using hr.1.1
  simp only [disappear,hlt,hrt,false_and,ite_false]
  (repeat first | dsimp only | split) <;>
    simp_all [CheckedCut,Safe,Core,StateOK]
private theorem compare_safe {ψ : Nat} (κ : Nat) (l r : AgentState ψ)
    (hl : CheckedCut l) (hr : Safe r) :
    Safe (compareSigF κ false true l r).1 ∧ Safe (compareSigF κ false true l r).2 := by
  rw [compare_core_eq κ false true l r hl.1 hr.1]
  refine ⟨?_,hr⟩
  cases hp : l.path <;> simp_all [compareSigInit,CheckedCut,Safe,Core,NoZero,StateOK]

private def CmpView {ψ : Nat} (u : AgentState ψ) := (u.label,u.state,u.path,u.path2)
private theorem cmpview_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    CmpView (if p then a else b)=if p then CmpView a else CmpView b := by split <;> rfl
private theorem safe_of_cmpview {ψ : Nat} (a b : AgentState ψ) (hv : CmpView a=CmpView b)
    (hb : Safe b) : Safe a := by
  simp only [CmpView,Prod.mk.injEq] at hv
  simpa only [Safe,Core,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2] using hb
private theorem suppressSigStart_cmp {ψ : Nat} (l r : AgentState ψ) :
    CmpView (suppressSigStart l r).1=CmpView l ∧ CmpView (suppressSigStart l r).2=CmpView r := by
  simp only [suppressSigStart,CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem suppressSigMoveReset_cmp {ψ : Nat} (l r : AgentState ψ) :
    CmpView (suppressSigMoveReset l r).1=CmpView l ∧ CmpView (suppressSigMoveReset l r).2=CmpView r := by
  simp only [suppressSigMoveReset,CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem suppressSigTerminal_cmp {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CmpView (suppressSigTerminal hp l r).1=CmpView l ∧ CmpView (suppressSigTerminal hp l r).2=CmpView r := by
  simp only [suppressSigTerminal,CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem suppressSigEcho_cmp {ψ : Nat} (l r : AgentState ψ) :
    CmpView (suppressSigEcho l r).1=CmpView l ∧ CmpView (suppressSigEcho l r).2=CmpView r := by
  simp only [suppressSigEcho,CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem suppressSigFinish_cmp {ψ : Nat} (l r : AgentState ψ) :
    CmpView (suppressSigFinish l r).1=CmpView l ∧ CmpView (suppressSigFinish l r).2=CmpView r := by
  simp only [suppressSigFinish,CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem kill_safe {ψ : Nat} (u : AgentState ψ) (h : Safe u) :
    Safe (if u.reset_cmd then clearCmp u else u) := by
  split
  · exact clear_safe _
  · exact h
private theorem pair_safe_view {ψ : Nat} (a b : AgentState ψ × AgentState ψ)
    (hv : CmpView a.1=CmpView b.1 ∧ CmpView a.2=CmpView b.2)
    (hb : Safe b.1 ∧ Safe b.2) : Safe a.1 ∧ Safe a.2 :=
  ⟨safe_of_cmpview _ _ hv.1 hb.1,safe_of_cmpview _ _ hv.2 hb.2⟩
private theorem suppress_safe {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : Safe l) (hr : Safe r) :
    Safe (suppressSigResetKill hp l r).1 ∧ Safe (suppressSigResetKill hp l r).2 := by
  let kill := fun u : AgentState ψ => if u.reset_cmd then clearCmp u else u
  let a := suppressSigStart l r
  have ha := pair_safe_view a (l,r) (suppressSigStart_cmp l r) ⟨hl,hr⟩
  let b := (kill a.1,kill a.2)
  have hb : Safe b.1 ∧ Safe b.2 := ⟨kill_safe a.1 ha.1,kill_safe a.2 ha.2⟩
  let c := suppressSigMoveReset b.1 b.2
  have hc := pair_safe_view c b (suppressSigMoveReset_cmp b.1 b.2) hb
  let d := (kill c.1,kill c.2)
  have hd : Safe d.1 ∧ Safe d.2 := ⟨kill_safe c.1 hc.1,kill_safe c.2 hc.2⟩
  let e := suppressSigTerminal hp d.1 d.2
  have he := pair_safe_view e d (suppressSigTerminal_cmp hp d.1 d.2) hd
  let f := suppressSigEcho e.1 e.2
  have hf := pair_safe_view f e (suppressSigEcho_cmp e.1 e.2) he
  exact pair_safe_view _ f (suppressSigFinish_cmp f.1 f.2) hf
private theorem kernel_cmpview {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CmpView (k4Kernel hp l r).1=CmpView l ∧ CmpView (k4Kernel hp l r).2=CmpView r := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp only [CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]

/-! WRITE frames are proved directly from the frozen writer definitions;
writer fields and bit mutations impose no comparison-safety premise. -/
namespace Writer
private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.label=b.label ∧ a.state=b.state ∧ a.path=b.path ∧ a.path2=b.path2
private theorem writeActionApplyOverwrite_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeActionApplyOverwrite u) u := by
  unfold Frame writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeActionApplyMoveFlip_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeActionApplyMoveFlip u) u := by
  unfold Frame writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) : Frame (moveWsigCheckLast u) u := by
  unfold Frame moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqSetWriteReady u) u := by
  unfold Frame writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeSeqCheckBit_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqCheckBit u) u := by
  unfold Frame writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [Frame,writeSeqSetWriteAct,hp] <;>
    simp [label_ite,state_ite,path_ite,path2_ite,hp]
private theorem writeSeqFinalR_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqFinalR u) u := by
  unfold Frame writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem moveWsigCheckGenWs_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigCheckGenWs l r) r := by
  unfold Frame moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigTransfer l r).1 l ∧ Frame (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [Frame,moveWsigTransfer,hl,hr] <;>
    simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem groupInfo_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (groupInfo hp l r).1 l ∧ Frame (groupInfo hp l r).2 r := by
  simp only [Frame,groupInfo,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem gensigWriteseq_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hp l r).1 l ∧ Frame (gensigWriteseq hp l r).2 r := by
  simp only [Frame,gensigWriteseq,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem writeAction_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (writeAction hp l r).1 l ∧ Frame (writeAction hp l r).2 r := by
  simp only [Frame,writeAction]
  simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self,(writeActionApplyOverwrite_frame _).1,(writeActionApplyOverwrite_frame _).2.1,(writeActionApplyOverwrite_frame _).2.2.1,(writeActionApplyOverwrite_frame _).2.2.2,(writeActionApplyMoveFlip_frame _).1,(writeActionApplyMoveFlip_frame _).2.1,(writeActionApplyMoveFlip_frame _).2.2.1,(writeActionApplyMoveFlip_frame _).2.2.2]
private theorem moveWsig_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (moveWsig hp l r).1 l ∧ Frame (moveWsig hp l r).2 r := by
  simp only [Frame,moveWsig]
  simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self,(moveWsigCheckGenWs_frame _ _).1,(moveWsigCheckGenWs_frame _ _).2.1,(moveWsigCheckGenWs_frame _ _).2.2.1,(moveWsigCheckGenWs_frame _ _).2.2.2,(moveWsigCheckLast_frame _).1,(moveWsigCheckLast_frame _).2.1,(moveWsigCheckLast_frame _).2.2.1,(moveWsigCheckLast_frame _).2.2.2,(moveWsigTransfer_frame _ _).1.1,(moveWsigTransfer_frame _ _).1.2.1,(moveWsigTransfer_frame _ _).1.2.2.1,(moveWsigTransfer_frame _ _).1.2.2.2,(moveWsigTransfer_frame _ _).2.1,(moveWsigTransfer_frame _ _).2.2.1,(moveWsigTransfer_frame _ _).2.2.2.1,(moveWsigTransfer_frame _ _).2.2.2.2]
private theorem writeSeq_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (writeSeq hp l r).1 l ∧ Frame (writeSeq hp l r).2 r := by
  simp only [Frame,writeSeq,writeSeqThroughPrepare,writeSeqAfterPrepare,writeSeqLeaderMove,writeSeqGenerate,writeSeqPrepare,writeSeqReady,writeSeqCompare,writeSeqCommands]
  simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self,(groupInfo_frame _ _ _).1.1,(groupInfo_frame _ _ _).1.2.1,(groupInfo_frame _ _ _).1.2.2.1,(groupInfo_frame _ _ _).1.2.2.2,(groupInfo_frame _ _ _).2.1,(groupInfo_frame _ _ _).2.2.1,(groupInfo_frame _ _ _).2.2.2.1,(groupInfo_frame _ _ _).2.2.2.2,(gensigWriteseq_frame _ _ _).1.1,(gensigWriteseq_frame _ _ _).1.2.1,(gensigWriteseq_frame _ _ _).1.2.2.1,(gensigWriteseq_frame _ _ _).1.2.2.2,(gensigWriteseq_frame _ _ _).2.1,(gensigWriteseq_frame _ _ _).2.2.1,(gensigWriteseq_frame _ _ _).2.2.2.1,(gensigWriteseq_frame _ _ _).2.2.2.2,(writeAction_frame _ _ _).1.1,(writeAction_frame _ _ _).1.2.1,(writeAction_frame _ _ _).1.2.2.1,(writeAction_frame _ _ _).1.2.2.2,(writeAction_frame _ _ _).2.1,(writeAction_frame _ _ _).2.2.1,(writeAction_frame _ _ _).2.2.2.1,(writeAction_frame _ _ _).2.2.2.2,(moveWsig_frame _ _ _).1.1,(moveWsig_frame _ _ _).1.2.1,(moveWsig_frame _ _ _).1.2.2.1,(moveWsig_frame _ _ _).1.2.2.2,(moveWsig_frame _ _ _).2.1,(moveWsig_frame _ _ _).2.2.1,(moveWsig_frame _ _ _).2.2.2.1,(moveWsig_frame _ _ _).2.2.2.2,(writeSeqSetWriteReady_frame _).1,(writeSeqSetWriteReady_frame _).2.1,(writeSeqSetWriteReady_frame _).2.2.1,(writeSeqSetWriteReady_frame _).2.2.2,(writeSeqCheckBit_frame _).1,(writeSeqCheckBit_frame _).2.1,(writeSeqCheckBit_frame _).2.2.1,(writeSeqCheckBit_frame _).2.2.2,(writeSeqSetWriteAct_frame _).1,(writeSeqSetWriteAct_frame _).2.1,(writeSeqSetWriteAct_frame _).2.2.1,(writeSeqSetWriteAct_frame _).2.2.2,(writeSeqFinalR_frame _).1,(writeSeqFinalR_frame _).2.1,(writeSeqFinalR_frame _).2.2.1,(writeSeqFinalR_frame _).2.2.2]
private theorem write_cmpview {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CmpView (writeWithBundle hp l r).1=CmpView l ∧
    CmpView (writeWithBundle hp l r).2=CmpView r := by
  have h := writeSeq_frame hp l r
  simp only [CmpView,writeWithBundle,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,
    h.1.1,h.1.2.1,h.1.2.2.1,h.1.2.2.2,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,ite_self,and_self]
end Writer

private theorem pprime_view {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩) :
    View (pPsiProbeWall hp l r).1=View l ∧ View (pPsiProbeWall hp l r).2=View r := by
  cases hll : l.leader <;> cases hrl : r.leader <;> cases hpr : r.probe <;>
    simp [pPsiProbeWall,pPsi,hll,hrl,hpr,ha,View]
/-- Safety through every frozen Head stage before K4. The comparison stages
cannot retain a nonterminal DONE or create a control token or head carrier. -/
theorem before_safe {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ) (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hl : Safe l) (hr : Safe r) :
    Safe (beforeElimination hp κ l r).1 ∧ Safe (beforeElimination hp κ l r).2 := by
  unfold beforeElimination
  try dsimp only
  generalize hA : pPsiProbeWall hp l r = a
  try dsimp only
  have hav := pprime_view hp l r ha
  rw [hA] at hav
  have hal := congrArg Prod.fst hav.1
  have har := congrArg Prod.fst hav.2
  change a.1.label=l.label at hal
  change a.2.label=r.label at har
  have haa : a.2.label=⟨(a.1.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by rw [hal,har]; exact ha
  generalize hB : genSigSaturated hp κ a.1 a.2 = b
  try dsimp only
  have hb : GenerationCut b.1 ∧ Safe b.2 := by
    rw [← hB]
    exact genSigSaturated_cut hp h3 κ a.1 a.2 haa
      (safe_of_view _ _ hav.1 hl) (safe_of_view _ _ hav.2 hr)
  generalize hC : cleanSig hp b.1 b.2 = c
  try dsimp only
  have hcframe := clean_frame hp b.1 b.2
  rw [hC] at hcframe
  have hc : GenerationCut c.1 ∧ Safe c.2 :=
    ⟨cleanFrame_cut hcframe.1 hb.1,cleanFrame_safe hcframe.2 hb.2⟩
  generalize hD : eliminateSig hp c.1 c.2 = d
  try dsimp only
  have hd : GenerationCut d.1 ∧ Safe d.2 := by
    rw [← hD]; exact eliminate_cut hp c.1 c.2 hc.1 hc.2
  generalize hE : sigMoveF hp true .dropMisaligned d.1 d.2 = e
  try dsimp only
  have he : GenerationCut e.1 ∧ Safe e.2 := by
    rw [← hE]; exact sigmove_cut hp d.1 d.2 hd.1 hd.2
  let f := (dropStale e.1,dropStale e.2)
  have hf : GenerationCut f.1 ∧ Safe f.2 := ⟨drop_cut e.1 he.1,drop_safe e.2 he.2⟩
  generalize hG : preCheckReset (dropStale e.1) (dropStale e.2) = g
  try dsimp only
  have hg : GenerationCut g.1 ∧ Safe g.2 := by
    rw [← hG]; exact precheck_cut f.1 f.2 hf.1 hf.2
  generalize hH : checkSigF hp κ false g.1 g.2 = h
  try dsimp only
  have hh : CheckedCut h.1 ∧ Safe h.2 := by
    rw [← hH]; exact check_cut hp κ g.1 g.2 hg.1 hg.2
  generalize hI : disappear hp h.1 h.2 = i
  try dsimp only
  have hi : CheckedCut i.1 ∧ Safe i.2 := by
    rw [← hI]; exact disappear_cut hp h.1 h.2 hh.1 hh.2
  generalize hJ : compareSigF κ false true i.1 i.2 = j
  try dsimp only
  have hj : Safe j.1 ∧ Safe j.2 := by
    rw [← hJ]; exact compare_safe κ i.1 i.2 hi.1 hi.2
  exact suppress_safe hp j.1 j.2 hj.1 hj.2
/-- Full actual Head preserves fresh comparison safety on a successor-aligned
ψ≥3 edge. Ancillary registers, including probes and writer debris, are free;
this is an edge-local statement and does not assert geometry preservation. -/
theorem pipeline_safe {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ) (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hl : Safe l) (hr : Safe r) :
    Safe (PPLLAstraDesign2.pipeline hp κ .head l r).1 ∧ Safe (PPLLAstraDesign2.pipeline hp κ .head l r).2 := by
  unfold PPLLAstraDesign2.pipeline
  try dsimp only
  generalize hA : beforeElimination hp κ l r = a
  try dsimp only
  have haS := before_safe hp h3 κ l r ha hl hr
  rw [hA] at haS
  generalize hB : k4Kernel hp a.1 a.2 = b
  try dsimp only
  have hbV := kernel_cmpview hp a.1 a.2
  rw [hB] at hbV
  have hb := pair_safe_view b a hbV haS
  generalize hC : writeWithBundle hp b.1 b.2 = c
  try dsimp only
  have hcV := Writer.write_cmpview hp b.1 b.2
  rw [hC] at hcV
  have hc := pair_safe_view c b hcV hb
  unfold conserve
  split
  · simpa [replacement,clearCmp,Safe,Core,StateOK,NoZero] using hc.1
  · exact hc

/-! Exact leader frames: the comparison prefix creates no leader in Safe. -/
private theorem gen_leaders {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    (genSigSaturated hp κ l r).1.leader=l.leader ∧
    (genSigSaturated hp κ l r).2.leader=r.leader := by
  simp only [genSigSaturated,genSigSaturatedAfterWait,genSigSaturatedStart,
    genSigSaturatedEmit,genSigSaturatedPropagate,genSigSaturatedFinish,
    waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,waitSaturatedReset,
    waitSaturatedFinish,fst_ite,snd_ite,leader_ite,ite_self,and_self]
private theorem eliminate_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (eliminateSig hp l r).1.leader=l.leader ∧ (eliminateSig hp l r).2.leader=r.leader := by
  simp only [eliminateSig,fst_ite,snd_ite,leader_ite,ite_self,and_self]
private theorem move1_leaders {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.leader=l.leader ∧
    (sigMoveStep1With .dropMisaligned l r).2.leader=r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [sigMoveStep1With,hl,hr,fst_ite,snd_ite,leader_ite]
private theorem moveToken_leaders {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.leader=l.leader ∧ (moveTokens l r).2.leader=r.leader := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [moveTokens,hl,hr,fst_ite,snd_ite,leader_ite]
private theorem control_leader {ψ : Nat} (hp : ψ>0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hp u).leader=u.leader := by
  cases h : u.path2 <;> simp [sigMoveApplyControlConsume,h,leader_ite]
private theorem sigmove_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (sigMoveF hp true .dropMisaligned l r).1.leader=l.leader ∧
    (sigMoveF hp true .dropMisaligned l r).2.leader=r.leader := by
  simp only [sigMoveF,leaderWall,fst_ite,snd_ite,leader_ite,control_leader,
    (move1_leaders _ _).1,(move1_leaders _ _).2,
    (moveToken_leaders _ _).1,(moveToken_leaders _ _).2,clearCmp,ite_self,and_self]
private theorem drop_leader {ψ : Nat} (u : AgentState ψ) : (dropStale u).leader=u.leader := by
  simp [dropStale,leader_ite]
private theorem precheck_leaders {ψ : Nat} (l r : AgentState ψ) :
    (preCheckReset l r).1.leader=l.leader ∧ (preCheckReset l r).2.leader=r.leader := by
  simp [preCheckReset,clearCmp,leader_ite]
private theorem ready_leader {ψ : Nat} (u : AgentState ψ) : (readyF u).leader=u.leader := by
  cases h : u.path <;>
    simp [readyF,checkSigSetReadyGuarded,checkSigSetReady,h,leader_ite]
private theorem check_leaders {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (hl : GenerationCut l) (hr : Safe r) :
    (checkSigF hp κ false l r).1.leader=l.leader ∧
    (checkSigF hp κ false l r).2.leader=r.leader := by
  have ha := ready_checked l hl
  have hb := ready_safe r hr
  have hla := core_not_equal (readyF l) ha.1
  have hra := core_not_equal (readyF r) hb.1
  simp only [checkSigF,hla,and_false,false_and,ite_false,
    checkL_core hp _ ha.1,checkR_core hp _ _ ha.1,
    result_core _ ha.1,result_core _ hb.1,hra,ready_leader,and_self]
private theorem disappear_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (disappear hp l r).1.leader=l.leader ∧ (disappear hp l r).2.leader=r.leader := by
  simp only [disappear,fst_ite,snd_ite,leader_ite,ite_self,and_self]
private theorem compare_leaders {ψ : Nat} (κ : Nat) (l r : AgentState ψ)
    (hl : Core l) (hr : Core r) :
    (compareSigF κ false true l r).1.leader=l.leader ∧
    (compareSigF κ false true l r).2.leader=r.leader := by
  rw [compare_core_eq κ false true l r hl hr]
  cases h : l.path <;> simp [compareSigInit,h]
private theorem suppress_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigResetKill hp l r).1.leader=l.leader ∧
    (suppressSigResetKill hp l r).2.leader=r.leader := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [suppressSigResetKill,suppressSigStart,suppressSigMoveReset,
      suppressSigTerminal,suppressSigEcho,suppressSigFinish,clearCmp,
      h1,h2,h3,h4,fst_ite,snd_ite,leader_ite]
/-- The whole comparison prefix preserves both input leader bits on Safe aligned edges. -/
theorem before_leaders {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ) (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hl : Safe l) (hr : Safe r) :
    (beforeElimination hp κ l r).1.leader=l.leader ∧
    (beforeElimination hp κ l r).2.leader=r.leader := by
  unfold beforeElimination
  try dsimp only
  generalize hA : pPsiProbeWall hp l r = a
  try dsimp only
  have hav := pprime_view hp l r ha
  rw [hA] at hav
  have hal := congrArg Prod.fst hav.1
  have har := congrArg Prod.fst hav.2
  change a.1.label=l.label at hal
  change a.2.label=r.label at har
  have haa : a.2.label=⟨(a.1.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by rw [hal,har]; exact ha
  generalize hB : genSigSaturated hp κ a.1 a.2 = b
  try dsimp only
  have hb : GenerationCut b.1 ∧ Safe b.2 := by
    rw [← hB]
    exact genSigSaturated_cut hp h3 κ a.1 a.2 haa
      (safe_of_view _ _ hav.1 hl) (safe_of_view _ _ hav.2 hr)
  generalize hC : cleanSig hp b.1 b.2 = c
  try dsimp only
  have hcframe := clean_frame hp b.1 b.2
  rw [hC] at hcframe
  have hc : GenerationCut c.1 ∧ Safe c.2 :=
    ⟨cleanFrame_cut hcframe.1 hb.1,cleanFrame_safe hcframe.2 hb.2⟩
  generalize hD : eliminateSig hp c.1 c.2 = d
  try dsimp only
  have hd : GenerationCut d.1 ∧ Safe d.2 := by
    rw [← hD]; exact eliminate_cut hp c.1 c.2 hc.1 hc.2
  generalize hE : sigMoveF hp true .dropMisaligned d.1 d.2 = e
  try dsimp only
  have he : GenerationCut e.1 ∧ Safe e.2 := by
    rw [← hE]; exact sigmove_cut hp d.1 d.2 hd.1 hd.2
  let f := (dropStale e.1,dropStale e.2)
  have hf : GenerationCut f.1 ∧ Safe f.2 := ⟨drop_cut e.1 he.1,drop_safe e.2 he.2⟩
  generalize hG : preCheckReset (dropStale e.1) (dropStale e.2) = g
  try dsimp only
  have hg : GenerationCut g.1 ∧ Safe g.2 := by
    rw [← hG]; exact precheck_cut f.1 f.2 hf.1 hf.2
  generalize hH : checkSigF hp κ false g.1 g.2 = h
  try dsimp only
  have hh : CheckedCut h.1 ∧ Safe h.2 := by
    rw [← hH]; exact check_cut hp κ g.1 g.2 hg.1 hg.2
  generalize hI : disappear hp h.1 h.2 = i
  try dsimp only
  have hi : CheckedCut i.1 ∧ Safe i.2 := by
    rw [← hI]; exact disappear_cut hp h.1 h.2 hh.1 hh.2
  generalize hJ : compareSigF κ false true i.1 i.2 = j
  try dsimp only
  have hj : Safe j.1 ∧ Safe j.2 := by
    rw [← hJ]; exact compare_safe κ i.1 i.2 hi.1 hi.2
  have hgen := gen_leaders hp κ a.1 a.2
  rw [hB] at hgen
  have hel := eliminate_leaders hp c.1 c.2
  rw [hD] at hel
  have hmov := sigmove_leaders hp d.1 d.2
  rw [hE] at hmov
  have hpre := precheck_leaders f.1 f.2
  rw [hG] at hpre
  have hcheck := check_leaders hp κ g.1 g.2 hg.1 hg.2
  rw [hH] at hcheck
  have hdis := disappear_leaders hp h.1 h.2
  rw [hI] at hdis
  have hcmp := compare_leaders κ i.1 i.2 hi.1.1 hi.2.1
  rw [hJ] at hcmp
  have hsup := suppress_leaders hp j.1 j.2
  have hpaL := congrArg (fun v => v.2.2.2.2) hav.1
  have hpaR := congrArg (fun v => v.2.2.2.2) hav.2
  constructor
  · exact hsup.1.trans (hcmp.1.trans (hdis.1.trans (hcheck.1.trans
      (hpre.1.trans ((drop_leader _).trans (hmov.1.trans (hel.1.trans
      (hcframe.1.2.2.2.1.trans (hgen.1.trans hpaL)))))))))
  · exact hsup.2.trans (hcmp.2.trans (hdis.2.trans (hcheck.2.trans
      (hpre.2.trans ((drop_leader _).trans (hmov.2.trans (hel.2.trans
      (hcframe.2.2.2.2.1.trans (hgen.2.trans hpaR)))))))))

/-- Reset comparison emptiness constructs the fresh-safe comparison sector. -/
theorem cmpEmpty_safe {ψ : Nat} (u : AgentState ψ) (h : PPLLAstraReset.CmpEmpty u) : Safe u := by
  simp [Safe,Core,StateOK,NoZero,h.1,h.2.1,h.2.2.1]
private theorem kernel_followers {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : l.leader=false) (hr : r.leader=false) :
    (k4Kernel hp l r).1.leader=false ∧ (k4Kernel hp l r).2.leader=false := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp only [fst_ite,snd_ite,leader_ite,hl,hr,ite_self,and_self]
private theorem write_followers {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : l.leader=false) (hr : r.leader=false) :
    (writeWithBundle hp l r).1.leader=false ∧ (writeWithBundle hp l r).2.leader=false := by
  have hL : (writeSeq hp l r).1.leader=false := by
    cases h : (writeSeq hp l r).1.leader
    · rfl
    · have bad := (PPLLVerify.writeSeq_new_initiator_requires_responder_leader hp l r h hl).1
      simp [hr] at bad
  have hR : (writeSeq hp l r).2.leader=false := by
    cases h : (writeSeq hp l r).2.leader
    · rfl
    · have bad := PPLLVerify.writeSeq_responder_leader_was_leader hp l r h
      simp [hr] at bad
  simpa [writeWithBundle,hr] using And.intro hL hR
/-- Full Head has no leader birth on a Safe successor-aligned follower pair.
This includes arbitrary ancillary fields and the final conservation guard. -/
theorem pipeline_followers {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ) (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩)
    (hl : Safe l) (hr : Safe r) (hlf : l.leader=false) (hrf : r.leader=false) :
    (PPLLAstraDesign2.pipeline hp κ .head l r).1.leader=false ∧ (PPLLAstraDesign2.pipeline hp κ .head l r).2.leader=false := by
  unfold PPLLAstraDesign2.pipeline
  try dsimp only
  generalize hA : beforeElimination hp κ l r = a
  try dsimp only
  have haL := before_leaders hp h3 κ l r ha hl hr
  rw [hA,hlf,hrf] at haL
  generalize hB : k4Kernel hp a.1 a.2 = b
  try dsimp only
  have hb := kernel_followers hp a.1 a.2 haL.1 haL.2
  rw [hB] at hb
  generalize hC : writeWithBundle hp b.1 b.2 = c
  try dsimp only
  have hc := write_followers hp b.1 b.2 hb.1 hb.2
  rw [hC] at hc
  simpa [conserve,hlf,hrf] using hc
end PPLLAstraFreshSafe
