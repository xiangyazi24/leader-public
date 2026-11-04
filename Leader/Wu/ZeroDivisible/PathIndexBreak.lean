import Leader.Wu.ZeroDivisible.ServiceEntry

/-! A resident-path successor break and the actual R5 CLEAN stage. -/
namespace PPLLAstraR5PathIndexBreak
open PPLL PPLLRepair PPLLPostElectionGuard PPLLAstraR5Repair
  PPLLAstraR5Repair.ServiceEntry PPLLAstraDesign3
set_option autoImplicit false

private theorem gen_path {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).path = u.path := by
  cases h : u.path <;> simp [cleanSigGenConnect,h] <;>
    repeat (first | split | simp_all)

private theorem gen_right_path4 {ψ : Nat} (r : AgentState ψ) (b bb : Nat)
    (hr : r.path = .some b bb) (hb0 : b ≠ 0) :
    (cleanSigGenConnect r).path4 = some (Int.ofNat b,1) := by
  simp [cleanSigGenConnect,hr,hb0] <;>
    repeat (first | split | simp_all)

private theorem step3_right_cmd {ψ : Nat} (l r : AgentState ψ)
    (a b ba bb : Nat) (hl : l.path = .some a ba)
    (hr : r.path = .some b bb)
    (hr4 : r.path4 = some (Int.ofNat b,1))
    (hbad : b ≠ a+1) :
    (cleanSigStep3 l r).2.path5 = some ((-1 : Int),0) ∧
    (cleanSigStep3 l r).2.path = .some b bb := by
  have hne : (b : Int) ≠ (a : Int)+1 := by omega
  simp [cleanSigStep3,hl,hr,hr4,hne]

private theorem step4_right {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).2 = r := by
  cases h : l.path5 <;> simp [cleanSigStep4,h] <;>
    repeat (first | split | simp_all)

private theorem step5_right_path5 {ψ : Nat} (hp : 0<ψ)
    (l r : AgentState ψ) :
    (cleanSigStep5 hp l r).2.path5 = r.path5 ∧
    (cleanSigStep5 hp l r).2.path = r.path := by
  cases h : r.path4 <;> simp [cleanSigStep5,h] <;>
    repeat (first | split | simp_all)

private theorem cleanApply_right_cmd {ψ : Nat} (r : AgentState ψ)
    (hcmd : r.path5 = some ((-1 : Int),0)) :
    (cleanSigCleanApply r).path = .bot := by
  cases hp : r.path <;> cases h4 : r.path4 <;>
    simp [cleanSigCleanApply,hp,h4,hcmd] <;>
    repeat (first | split | simp_all)

private theorem gen_left_path5 {ψ : Nat} (l : AgentState ψ) (a ba : Nat)
    (hl : l.path = .some a ba) (ha : a ≠ ψ - 1) :
    (cleanSigGenConnect l).path5 = some (Int.ofNat a,1) := by
  simp [cleanSigGenConnect,hl,ha] <;>
    repeat (first | split | simp_all)

private theorem step3_left {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1 = l := by
  cases h : r.path4 <;> simp [cleanSigStep3,h] <;>
    repeat (first | split | simp_all)

private theorem step3_right_path {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).2.path = r.path := by
  cases h : r.path4 <;> simp [cleanSigStep3,h] <;>
    repeat (first | split | simp_all)

private theorem step4_left_cmd {ψ : Nat} (l r : AgentState ψ)
    (a bb : Nat) (hl5 : l.path5 = some (Int.ofNat a,1))
    (hr : r.path = .some 0 bb) :
    (cleanSigStep4 l r).1.path4 = some ((-1 : Int),0) := by
  simp [cleanSigStep4,hl5,hr] <;> omega

private theorem step6_left_path4 {ψ : Nat} (hp : 0<ψ)
    (l r : AgentState ψ) :
    (cleanSigStep6 hp l r).1.path4 = l.path4 := by
  cases h : l.path5 <;> simp [cleanSigStep6,h] <;>
    repeat (first | split | simp_all)

private theorem cleanApply_left_cmd {ψ : Nat} (l : AgentState ψ)
    (hcmd : l.path4 = some ((-1 : Int),0)) :
    (cleanSigCleanApply l).path = .bot := by
  cases hp : l.path <;> cases h5 : l.path5 <;>
    simp [cleanSigCleanApply,hp,h5,hcmd] <;>
    repeat (first | split | simp_all)

/-- A nonzero responder path index different from the initiator successor
creates a protected CLEAN command on the responder. Saved CLEAN registers are
arbitrary. -/
theorem clean_right_break {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) (a b ba bb : Nat)
    (hl : l.path = .some a ba) (hr : r.path = .some b bb)
    (hb0 : b ≠ 0) (hbad : b ≠ a + 1) :
    (cleanSource hp l r).2.path = .bot := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  have h3 := step3_right_cmd l0 r0 a b ba bb
    (by change l0.path = .some a ba; rw [gen_path]; exact hl)
    (by change r0.path = .some b bb; rw [gen_path]; exact hr)
    (gen_right_path4 r b bb hr hb0) hbad
  let s3 := cleanSigStep3 l0 r0
  let s4 := cleanSigStep4 s3.1 s3.2
  have h4r : s4.2 = s3.2 := step4_right _ _
  have h4cmd : s4.2.path5 = some ((-1 : Int),0) := by rw [h4r]; exact h3.1
  have h4path : s4.2.path = .some b bb := by rw [h4r]; exact h3.2
  let s5 := if (match s4.1.path4 with
      | some (x,_) => decide (x = (-1 : Int)) | none => false)
    then (s4.1,{s4.2 with path4 := none}) else cleanSigStep5 hp s4.1 s4.2
  have h5cmd : s5.2.path5 = some ((-1 : Int),0) := by
    by_cases hc : (match s4.1.path4 with
        | some (x,_) => decide (x = (-1 : Int)) | none => false) = true
    · simp [s5,hc,h4cmd]
    · simp [s5,hc,(step5_right_path5 hp s4.1 s4.2).1,h4cmd]
  have hfinal : (cleanSigCleanApply s5.2).path = .bot :=
    cleanApply_right_cmd s5.2 h5cmd
  change (cleanSigCleanApply
    (if (match s5.2.path5 with
        | some (x,_) => decide (x = (-1 : Int)) | none => false)
      then ({s5.1 with path5 := none},s5.2)
      else cleanSigStep6 hp s5.1 s5.2).2).path = .bot
  simp [h5cmd,hfinal]

/-- A zero responder index after a nonterminal initiator creates a protected
CLEAN command on the initiator. -/
theorem clean_left_zero_break {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) (a ba bb : Nat)
    (hl : l.path = .some a ba) (hr : r.path = .some 0 bb)
    (ha : a ≠ ψ - 1) :
    (cleanSource hp l r).1.path = .bot := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  let s3 := cleanSigStep3 l0 r0
  have h3l : s3.1 = l0 := step3_left _ _
  have h3l5 : s3.1.path5 = some (Int.ofNat a,1) := by
    rw [h3l]; exact gen_left_path5 l a ba hl ha
  have h3rp : s3.2.path = .some 0 bb := by
    change (cleanSigStep3 l0 r0).2.path = .some 0 bb
    rw [step3_right_path,gen_path]
    exact hr
  let s4 := cleanSigStep4 s3.1 s3.2
  have h4cmd : s4.1.path4 = some ((-1 : Int),0) :=
    step4_left_cmd s3.1 s3.2 a bb h3l5 h3rp
  let s5 := if (match s4.1.path4 with
      | some (x,_) => decide (x = (-1 : Int)) | none => false)
    then (s4.1,{s4.2 with path4 := none}) else cleanSigStep5 hp s4.1 s4.2
  have h5cmd : s5.1.path4 = some ((-1 : Int),0) := by
    dsimp only [s5]
    simp [h4cmd]
  have hfinal : ∀ v : AgentState ψ,
      v.path4 = some ((-1 : Int),0) → (cleanSigCleanApply v).path=.bot :=
    fun v hv => cleanApply_left_cmd v hv
  change (cleanSigCleanApply
    (if (match s5.2.path5 with
        | some (x,_) => decide (x = (-1 : Int)) | none => false)
      then ({s5.1 with path5 := none},s5.2)
      else cleanSigStep6 hp s5.1 s5.2).1).path = .bot
  by_cases hc : (match s5.2.path5 with
      | some (x,_) => decide (x = (-1 : Int)) | none => false) = true
  · simp only [if_pos hc]
    apply hfinal
    simpa using h5cmd
  · simp only [if_neg hc]
    apply hfinal
    exact (step6_left_path4 hp s5.1 s5.2).trans h5cmd

/-- The source CLEAN row detects every bounded cyclic successor break. -/
theorem clean_path_index_break {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) (a b ba bb : Nat)
    (hl : l.path = .some a ba) (hr : r.path = .some b bb)
    (ha : a < ψ) (hb : b < ψ) (hbreak : b ≠ (a + 1) % ψ) :
    (cleanSource hp l r).1.path = .bot ∨
      (cleanSource hp l r).2.path = .bot := by
  by_cases hb0 : b = 0
  · left
    have hlast : a ≠ ψ - 1 := by
      intro he
      subst a
      have hs : ψ - 1 + 1 = ψ := Nat.sub_add_cancel hp
      rw [hs,Nat.mod_self] at hbreak
      exact hbreak hb0
    exact clean_left_zero_break hp l r a ba bb hl (by simpa [hb0] using hr) hlast
  · right
    have hbad : b ≠ a+1 := by
      intro he
      apply hbreak
      rw [←he]
      exact (Nat.mod_eq_of_lt hb).symm
    exact clean_right_break hp l r a b ba bb hl hr hb0 hbad

private def core {ψ : Nat} (u : AgentState ψ) := (u.state,u.path)

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl
private theorem core_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    core (if p then a else b) = if p then core a else core b := by
  split <;> rfl
private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by
  split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem probe_core {ψ : Nat} (hp : 0<ψ)
    (l r : AgentState ψ) :
    core (pPsiProbeWall hp l r).1 = core l ∧
    core (pPsiProbeWall hp l r).2 = core r := by
  simp [pPsiProbeWall,pPsi,core] <;>
    repeat (first | split | simp_all [core])

private theorem wait_core {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ) :
    core (waitSaturated hp κ l r).1 = core l ∧
    core (waitSaturated hp κ l r).2 = core r := by
  simp only [waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,
    waitSaturatedReset,waitSaturatedFinish]
  simp only [fst_ite,snd_ite,core_ite,core,state_ite,path_ite,ite_self,and_self]

private theorem gen_core {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done)
    (hrs : r.state ≠ .produce) :
    core (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1 = core l ∧
    core (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2 = core r := by
  have hw := wait_core hp κ l r
  simp only [core,Prod.mk.injEq] at hw
  simp only [PPLLFableZDiv.genSigOverwrite]
  generalize he : waitSaturated hp κ l r = q at *
  have hlp' : q.1.path ≠ .bot := by rw [hw.1.2]; exact hlp
  have hrp' : q.2.path ≠ .bot := by rw [hw.2.2]; exact hrp
  have hls' : q.1.state ≠ .produce := by rw [hw.1.1]; exact hls
  have hld' : q.1.state ≠ .done := by rw [hw.1.1]; exact hld
  have hrs' : q.2.state ≠ .produce := by rw [hw.2.1]; exact hrs
  simp [hlp',hrp',hls',hld',hrs',genSigSaturatedEmit,
    genSigSaturatedPropagate,genSigSaturatedFinish,core,
    hw.1.1,hw.1.2,hw.2.1,hw.2.2,hlp,hrp,hls,hld,hrs]

/-- On an occupied pair with no PRODUCE or DONE, the actual probe and GEN
prefix preserve both main states and main paths before CLEAN. -/
theorem preclean_core {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done)
    (hrs : r.state ≠ .produce) :
    let p := pPsiProbeWall hp l r
    let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
    core g.1 = core l ∧ core g.2 = core r := by
  let p := pPsiProbeWall hp l r
  have hpc' := probe_core hp l r
  have hpc := hpc'
  change core p.1 = core l ∧ core p.2 = core r at hpc
  simp only [core,Prod.mk.injEq] at hpc
  have hgp := gen_core hp κ p.1 p.2
    (by rw [hpc.1.2]; exact hlp)
    (by rw [hpc.2.2]; exact hrp)
    (by rw [hpc.1.1]; exact hls)
    (by rw [hpc.1.1]; exact hld)
    (by rw [hpc.2.1]; exact hrs)
  exact ⟨hgp.1.trans hpc'.1,hgp.2.trans hpc'.2⟩

private theorem release_paths {ψ : Nat} (hp : 0<ψ)
    (l r : AgentState ψ) :
    (releaseSource hp l r).1.path=l.path ∧
    (releaseSource hp l r).2.path=r.path := by
  simp [releaseSource] <;> repeat (first | split | simp_all)

private theorem eliminate_hole {ψ : Nat} (hp : 0<ψ)
    (l r : AgentState ψ) (h : l.path=.bot ∨ r.path=.bot) :
    (eliminateSig hp l r).1.path=.bot ∨
    (eliminateSig hp l r).2.path=.bot := by
  by_cases he : r.state = .eliminate_signal
  · right
    simp [eliminateSig,he]
  · simpa [eliminateSig,he] using h

private theorem moveEntry_factor {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ) :
    moveEntry hp κ l r =
      let p := pPsiProbeWall hp l r
      let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
      let c := cleanSource hp g.1 g.2
      let d := releaseSource hp c.1 c.2
      eliminateSig hp d.1 d.2 := rfl

private def HasHole {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.path=.bot ∨ q.2.path=.bot

private theorem hasHole_iff {ψ : Nat} (q : AgentState ψ × AgentState ψ) :
    HasHole q ↔ (q.1.path=.bot ∨ q.2.path=.bot) := Iff.rfl

attribute [local irreducible] HasHole

/-- A cut-local CLEAN break; the full pipeline is connected separately. -/
private theorem cut_hole {ψ : Nat} (hp : 0<ψ)
    (g c d : AgentState ψ × AgentState ψ) (a b ba bb : Nat)
    (hgl : g.1.path=.some a ba) (hgr : g.2.path=.some b bb)
    (ha : a<ψ) (hb : b<ψ) (hbreak : b ≠ (a+1)%ψ)
    (hc : c = cleanSource hp g.1 g.2)
    (hd : d = releaseSource hp c.1 c.2) :
    HasHole (eliminateSig hp d.1 d.2) := by
  have hclean : c.1.path=.bot ∨ c.2.path=.bot := by
    subst c
    exact clean_path_index_break hp g.1 g.2 a b ba bb hgl hgr ha hb hbreak
  have hreleased : d.1.path=.bot ∨ d.2.path=.bot := by
    subst d
    have hf := release_paths hp c.1 c.2
    rcases hclean with h | h
    · exact Or.inl (hf.1.trans h)
    · exact Or.inr (hf.2.trans h)
  exact (hasHole_iff _).2 (eliminate_hole hp d.1 d.2 hreleased)

attribute [local irreducible] PPLLAstraR5Repair.ServiceEntry.moveEntry

/-- The explicit cut is exactly the public pre-MOVE entry. -/
private theorem moveEntry_path_index_break {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ) (a b ba bb : Nat)
    (hl : l.path=.some a ba) (hr : r.path=.some b bb)
    (ha : a<ψ) (hb : b<ψ) (hbreak : b ≠ (a+1)%ψ)
    (hls : l.state≠.produce) (hld : l.state≠.done)
    (hrs : r.state≠.produce) :
    HasHole (moveEntry hp κ l r) := by
  let p := pPsiProbeWall hp l r
  let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
  let c := cleanSource hp g.1 g.2
  let d := releaseSource hp c.1 c.2
  have hpc := preclean_core hp κ l r
    (by simp [hl]) (by simp [hr]) hls hld hrs
  change core g.1 = core l ∧ core g.2 = core r at hpc
  simp only [core, Prod.mk.injEq] at hpc
  have hcut : HasHole (eliminateSig hp d.1 d.2) :=
    cut_hole hp g c d a b ba bb
      (by rw [hpc.1.2]; exact hl)
      (by rw [hpc.2.2]; exact hr)
      ha hb hbreak rfl rfl
  rw [moveEntry_factor]
  exact hcut

attribute [local irreducible] PPLLAstraR5Repair.ServiceEntry.afterEntry
  PPLLAstraR5Repair.pipeline

/-- One actual R5 row creates a main-path hole from a bounded occupied
resident-index break, for either CHECK guard and arbitrary auxiliary fields.
Physical-label successor alignment is unnecessary for this stronger leaf. -/
theorem pipeline_path_index_break {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (c : Cfg) (l r : AgentState ψ) (a b ba bb : Nat)
    (hl : l.path=.some a ba) (hr : r.path=.some b bb)
    (ha : a<ψ) (hb : b<ψ) (hbreak : b ≠ (a+1)%ψ)
    (hls : l.state≠.produce) (hld : l.state≠.done)
    (hrs : r.state≠.produce) :
    (pipeline hp κ c l r).1.path=.bot ∨
    (pipeline hp κ c l r).2.path=.bot := by
  rw [ServiceEntry.pipeline_factor]
  exact ServiceEntry.afterEntry_pairHole hp κ c l r
    (moveEntry hp κ l r).1 (moveEntry hp κ l r).2
    ((hasHole_iff _).1
      (moveEntry_path_index_break hp κ l r a b ba bb hl hr ha hb hbreak hls hld hrs))

#check clean_path_index_break
#print axioms clean_path_index_break
#check preclean_core
#print axioms preclean_core
#check pipeline_path_index_break
#print axioms pipeline_path_index_break
end PPLLAstraR5PathIndexBreak
