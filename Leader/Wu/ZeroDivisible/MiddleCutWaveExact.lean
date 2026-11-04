import Leader.Wu.ZeroDivisible.MiddleCut

/-!
# Exact prepared-wave states through the actual Middle cut

Full own carriers in C1 (nonterminal) or C2 (terminal) survive drop/reset,
normalization, CHECK, DISAPPEAR and ReadyAck with exact state/token/path/label
frames, unless a path is cleared or terminal carry creates E. No hypothesis
restricts leaders, token actions, writer fields, counters, or reset debris.
-/
namespace PPLLAstraR5MiddleWaveExact
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
open PPLLPostElectionGuard PPLLFableDesignR1
open PPLLAstraDesign2 PPLLAstraDesign3 PPLLAstraR5CompareB PPLLAstraR5MiddleB
set_option autoImplicit false

/-- Exact prepared role: C2 at the physical terminal and C1 elsewhere. -/
def WaveExact (ψ k : Nat) (s : MainState) : Prop :=
  s = if k+1=ψ then .compare2 else .compare1

/-- The normal branch preserves the same holder's comparison fields. -/
def ExactFrame {ψ : Nat} (l r : AgentState ψ) (z : AgentState ψ × AgentState ψ) : Prop :=
  z.1.label=l.label ∧ z.2.label=r.label ∧
  z.1.path=l.path ∧ z.2.path=r.path ∧
  z.1.path2=l.path2 ∧ z.2.path2=r.path2 ∧
  z.1.state=l.state ∧ z.2.state=r.state

private theorem wave_cases {ψ k : Nat} {s : MainState} (h : WaveExact ψ k s) :
    s=.compare1 ∨ s=.compare2 := by
  unfold WaveExact at h
  split at h <;> simp_all

private theorem wave_B {ψ k : Nat} {s : MainState} (h4 : 4≤ψ)
    (h : WaveExact ψ k s) : BState ψ k s := by
  unfold WaveExact at h
  unfold BState
  by_cases h0 : k=0
  · subst k
    simp [show 0+1≠ψ by omega] at h ⊢
    simp [HeadState,h]
  · simp only [if_neg h0]
    split <;> simp_all [MidState,PenState]

private theorem normalize_wave {ψ b : Nat} (u : AgentState ψ)
    (hp : u.path=.some u.label.val b) (hs : WaveExact ψ u.label.val u.state) :
    normalizeReady u=u := by
  rcases wave_cases hs with hs | hs <;>
    simp [normalizeReady,normalizeOrphan,normalizeCarrier,aligned,hp,hs]

private theorem check_wave {ψ bL bR : Nat} (h4 : 4≤ψ) (hp : 0<ψ)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (succ : r.label.val=(l.label.val+1)%ψ)
    (pl : l.path=.some l.label.val bL) (pr : r.path=.some r.label.val bR)
    (hL : WaveExact ψ l.label.val l.state) (hR : WaveExact ψ r.label.val r.state) :
    PPLLAstraR5Repair.checkSource hp c l r=(l,r) := by
  have h := checkSource_BOrE_table hp h4 c l r rfl rfl succ pl pr
    (Or.inl (wave_B h4 hL)) (Or.inl (wave_B h4 hR))
  change PPLLAstraR5Repair.checkSource hp c l r =
    ((if l.state=.equal ∧ r.state=.compare2 then {l with state:=.depart} else l),r) at h
  have ne : l.state≠.equal := by rcases wave_cases hL with hs | hs <;> simp [hs]
  simpa only [ne,false_and,if_false] using h

/-- DISAPPEAR preserves all three carrier fields and the left state. Its only
wave-state change is right terminal E from arbitrary carry debris. -/
private theorem disappear_wave {ψ : Nat} (hp : 0<ψ) (l r : AgentState ψ)
    (hL : WaveExact ψ l.label.val l.state) (hR : WaveExact ψ r.label.val r.state) :
    let z := disappear hp l r
    z.1.label=l.label ∧ z.2.label=r.label ∧
    z.1.path=l.path ∧ z.2.path=r.path ∧
    z.1.path2=l.path2 ∧ z.2.path2=r.path2 ∧ z.1.state=l.state ∧
    (z.2.state=r.state ∨ (z.2.label.val+1=ψ ∧ z.2.state=.eliminate_signal)) := by
  have nl : l.state≠.toss := by rcases wave_cases hL with hs | hs <;> simp [hs]
  have nr : r.state≠.toss := by rcases wave_cases hR with hs | hs <;> simp [hs]
  have hd : disappear hp l r=disappearCarry hp l r := by
    simp [disappear_eq_staged,disappearStaged,disappearStartR,disappearStartL,nl,nr]
  rw [hd]
  by_cases hc : l.p_carry=true
  · by_cases hr : r.p=true
    · by_cases ht : r.label=(⟨ψ-1,by omega⟩ : Fin ψ)
      · have hv := congrArg Fin.val ht
        have terminal : r.label.val+1=ψ := by change r.label.val=ψ-1 at hv; omega
        simp [disappearCarry,hc,hr,ht]
        omega
      · simp [disappearCarry,hc,hr,ht]
    · simp [disappearCarry,hc,hr]
  · simp [disappearCarry,hc]

/-- Actual Middle is exact on prepared wave carriers unless reset creates a
hole or carry produces physical terminal E. Both CHECK guard variants and all
raw ancillary/token fields are quantified without extra restrictions. -/
theorem middle_wave_exact {ψ bL bR : Nat} (h4 : 4≤ψ) (hp : 0<ψ)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (succ : r.label.val=(l.label.val+1)%ψ)
    (pl : l.path=.some l.label.val bL) (pr : r.path=.some r.label.val bR)
    (hL : WaveExact ψ l.label.val l.state) (hR : WaveExact ψ r.label.val r.state) :
    let z := Middle hp c l r
    PairHole z ∨ TerminalE z ∨ ExactFrame l r z := by
  by_cases hb : l.leader=true ∨ l.reset_cmd=true ∨ r.reset_cmd=true
  · exact Or.inl ((middle_hole_iff hp c l r rfl rfl pl pr).mpr hb)
  have fl : l.leader=false := by cases h : l.leader <;> simp_all
  have rl : l.reset_cmd=false := by cases h : l.reset_cmd <;> simp_all
  have rr : r.reset_cmd=false := by cases h : r.reset_cmd <;> simp_all
  have dl : dropStale l=l := by simp [dropStale,aligned,pl]
  have dr : dropStale r=r := by simp [dropStale,aligned,pr]
  have pre : preCheckReset l r=(l,r) := by simp [preCheckReset,fl,rl,rr]
  let d := disappear hp l r
  have hd := disappear_wave hp l r hL hR
  change d.1.label=l.label ∧ d.2.label=r.label ∧
    d.1.path=l.path ∧ d.2.path=r.path ∧
    d.1.path2=l.path2 ∧ d.2.path2=r.path2 ∧ d.1.state=l.state ∧
    (d.2.state=r.state ∨ (d.2.label.val+1=ψ ∧ d.2.state=.eliminate_signal)) at hd
  obtain ⟨labL,labR,pathL,pathR,tokL,tokR,stateL,stateR⟩ := hd
  have bore := disappear_BOrE hp l r rfl
    (Or.inl (wave_B h4 hL)) (Or.inl (wave_B h4 hR))
  have rep := repair_BOrE h4 d.1 d.2 (pathL.trans pl) (pathR.trans pr)
    bore.2.2.1 bore.2.2.2
  have eq : Middle hp c l r=d := by
    simp only [Middle,dl,dr,pre,normalize_wave l pl hL,normalize_wave r pr hR,
      check_wave h4 hp c l r succ pl pr hL hR]
    exact rep
  rw [eq]
  rcases stateR with stateR | he
  · exact Or.inr (Or.inr ⟨labL,labR,pathL,pathR,tokL,tokR,stateL,stateR⟩)
  · exact Or.inr (Or.inl (Or.inr he))

#print axioms middle_wave_exact
end PPLLAstraR5MiddleWaveExact
