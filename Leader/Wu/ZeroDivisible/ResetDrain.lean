import Leader.Wu.ZeroDivisible.ResetFrames
import Leader.Wu.Safety.CorrectedFormulation

/-! Reset drainage for the actual R5 Candidate-E pipeline, uniformly in its
CHECK result guard. This directly ports the ReadyAck stopped sweep/walk/kill
proof. No bounded-domain, label-alignment, token or writer assumptions are used.
No word-length theorem is asserted. -/
namespace PPLLAstraR5ResetDrain
open PPLL PPLLPostElectionGuard PPLLAstraR5ResetFrames PPLLResearchFormulation
set_option autoImplicit false

/-- The actual R5 transition, without projection or bounded reification. -/
abbrev protocol {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) : PopulationProtocol where
  Q := AgentState ψ
  Y := Bool
  transition := PPLLAstraR5Repair.pipeline hp κ c
  output := fun a => a.leader

/-- Execute a physical edge word in the actual R5 protocol. -/
def run {n ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : List (Fin n) → (Fin n → AgentState ψ)
  | [] => C
  | e :: es => run hp κ c ring ((protocol hp κ c).step ring C e) es

/-- Every executed word is a reachability witness for that same protocol. -/
theorem run_reachable {n ψ : Nat} (hp : ψ>0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (w : List (Fin n)) :
    (protocol hp κ c).Reachable ring C (run hp κ c ring C w) := by
  have he : runSchedule (protocol hp κ c) ring C w = run hp κ c ring C w := by
    induction w generalizing C with
    | nil => rfl
    | cons e es ih => exact ih _
  rw [← he]
  exact runSchedule_reachable (protocol hp κ c) ring C w

/-! ### Algorithm 14 stage by stage

Each suppression stage is described by its effect on the four fields that
matter here (leader, reset_cmd, echo, label). `clearCmp` preserves all four, so
the `kill` guard is transparent. No stage is unfolded into a structure literal
inside a larger term. -/

section Stages
variable {ψ : Nat}
private theorem fst_ite (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem reset_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).reset_cmd = if p then a.reset_cmd else b.reset_cmd := by split <;> rfl
private theorem echo_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).echo = if p then a.echo else b.echo := by split <;> rfl
private theorem leader_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
private theorem label_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
private theorem cc_reset (u : AgentState ψ) : (clearCmp u).reset_cmd=u.reset_cmd := rfl
private theorem cc_echo (u : AgentState ψ) : (clearCmp u).echo=u.echo := rfl
private theorem cc_leader (u : AgentState ψ) : (clearCmp u).leader=u.leader := rfl
private theorem cc_label (u : AgentState ψ) : (clearCmp u).label=u.label := rfl

private theorem st1 (l r : AgentState ψ) (hl : l.leader=false) : suppressSigStart l r = (l,r) := by
  simp [suppressSigStart,hl]
private theorem mv1_reset (l r : AgentState ψ) : (suppressSigMoveReset l r).1.reset_cmd=false := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv1_echo (l r : AgentState ψ) : (suppressSigMoveReset l r).1.echo=l.echo := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv1_leader (l r : AgentState ψ) : (suppressSigMoveReset l r).1.leader=l.leader := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_reset (l r : AgentState ψ) :
    (suppressSigMoveReset l r).2.reset_cmd=(l.reset_cmd || r.reset_cmd) := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_echo (l r : AgentState ψ) : (suppressSigMoveReset l r).2.echo=r.echo := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_label (l r : AgentState ψ) : (suppressSigMoveReset l r).2.label=r.label := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem tm1_reset (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).1.reset_cmd=l.reset_cmd := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm1_leader (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).1.leader=l.leader := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm1_echo (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).1.echo=
      if r.label = ⟨ψ-1,by omega⟩ ∧ r.reset_cmd=true then true else l.echo := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm2_reset (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.reset_cmd=r.reset_cmd := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm2_echo (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.echo=r.echo := by
  unfold suppressSigTerminal; split <;> rfl
private theorem ec1_reset (l r : AgentState ψ) : (suppressSigEcho l r).1.reset_cmd=l.reset_cmd := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec1_leader (l r : AgentState ψ) : (suppressSigEcho l r).1.leader=l.leader := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec1_echo (l r : AgentState ψ) :
    (suppressSigEcho l r).1.echo=(l.echo || (r.echo && !r.reset_cmd)) := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec2_reset (l r : AgentState ψ) :
    (suppressSigEcho l r).2.reset_cmd=(r.reset_cmd && !r.echo) := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem fn1_reset (l r : AgentState ψ) : (suppressSigFinish l r).1.reset_cmd=l.reset_cmd := by
  cases h : l.leader <;> simp [suppressSigFinish,h]
private theorem fn1_echo (l r : AgentState ψ) :
    (suppressSigFinish l r).1.echo=(l.echo && !l.leader) := by
  cases h : l.leader <;> simp [suppressSigFinish,h]
private theorem fn2 (l r : AgentState ψ) : (suppressSigFinish l r).2=r := rfl
private theorem tm2_label (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.label=r.label := by
  unfold suppressSigTerminal; split <;> rfl
private theorem ec2_label (l r : AgentState ψ) : (suppressSigEcho l r).2.label=r.label := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]

/-- Algorithm 14 on a follower initiator: the initiator loses its reset and the
responder holds the merged bit unless the responder echo annihilates it. -/
private theorem suppress_reset (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false) :
    (suppressSigResetKill hp l r).1.reset_cmd=false ∧
    (suppressSigResetKill hp l r).2.reset_cmd=((l.reset_cmd || r.reset_cmd) && !r.echo) := by
  constructor
  · simp only [suppressSigResetKill,st1 l r hl,fn1_reset,ec1_reset,tm1_reset,mv1_reset,
      reset_ite,cc_reset,ite_self]
  · simp only [suppressSigResetKill,st1 l r hl,fn2,ec2_reset,tm2_reset,tm2_echo,mv2_reset,mv2_echo,
      reset_ite,echo_ite,cc_reset,cc_echo,ite_self]

/-- Algorithm 14 does not relabel the responder. -/
private theorem suppress_label (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false) :
    (suppressSigResetKill hp l r).2.label=r.label := by
  simp only [suppressSigResetKill,st1 l r hl,fn2,ec2_label,tm2_label,mv2_label,label_ite,cc_label,ite_self]

/-- Echo birth inside Algorithm 14: a terminal responder carrying (merged)
reset debt gives the initiator an echo. -/
private theorem suppress_echo_terminal (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false)
    (ht : r.label=⟨ψ-1,by omega⟩) (hc : (l.reset_cmd || r.reset_cmd)=true) :
    (suppressSigResetKill hp l r).1.echo=true := by
  simp only [suppressSigResetKill,st1 l r hl,fn1_echo,ec1_echo,ec1_leader,tm1_echo,tm1_leader,
    tm2_echo,tm2_reset,mv1_echo,mv1_leader,mv2_echo,mv2_reset,mv2_label,
    reset_ite,echo_ite,leader_ite,label_ite,cc_reset,cc_echo,cc_leader,cc_label,ite_self]
  simp [ht,hc,hl]

/-- Echo transport inside Algorithm 14: with no reset on either endpoint a
responder echo moves to the initiator. -/
private theorem suppress_echo_walk (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false)
    (ha : l.reset_cmd=false) (hb : r.reset_cmd=false) (he : r.echo=true) :
    (suppressSigResetKill hp l r).1.echo=true := by
  simp only [suppressSigResetKill,st1 l r hl,fn1_echo,ec1_echo,ec1_leader,tm1_echo,tm1_leader,
    tm2_echo,tm2_reset,mv1_echo,mv1_leader,mv2_echo,mv2_reset,mv2_label,
    reset_ite,echo_ite,leader_ite,label_ite,cc_reset,cc_echo,cc_leader,cc_label,ite_self]
  simp [ha,hb,he,hl]

/-- The responder label reaching Algorithm 14 is P′'s responder label. -/
private theorem prefix_right_label (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) (hl : l.leader=false) :
    (beforeSuppress hp κ c l r).2.label=(pPsiProbeWall hp l r).2.label := by
  have hb := (PPLLAstraR5ResetFrames.before_control hp κ c l r).2
  simp only [PPLLAstraR5ResetFrames.control,Prod.mk.injEq] at hb
  have h := hb.1
  rw [prefix_identity,suppress_label hp _ _ ((prefix_leader hp κ c l r).trans hl)] at h
  exact h
end Stages

/-! ### Full-pipeline reset/echo equations for a follower initiator -/

/-- A follower initiator emits no fresh reset: the initiator leaves reset-free
and the responder holds the merged reset bit unless its echo annihilates it.
All ancillary state, κ and the responder's leader bit are unrestricted. -/
theorem pipeline_follower_reset {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.leader=false) :
    (PPLLAstraR5Repair.pipeline hp κ c l r).1.reset_cmd=false ∧
    (PPLLAstraR5Repair.pipeline hp κ c l r).2.reset_cmd=((l.reset_cmd || r.reset_cmd) && !r.echo) := by
  have hb := prefix_bits hp κ c l r
  have hs := suppress_reset hp (beforeSuppress hp κ c l r).1 (beforeSuppress hp κ c l r).2
    ((prefix_leader hp κ c l r).trans hl)
  have hq := pipeline_bits hp κ c l r
  rw [prefix_identity] at hq
  rw [hb.1,hb.2.2.1,hb.2.2.2] at hs
  exact ⟨hq.1.trans hs.1,hq.2.2.1.trans hs.2⟩

/-- Echo birth: a follower initiator carrying (or meeting) reset debt, served
against a responder that P′ labels terminal, leaves with an echo. -/
theorem pipeline_terminal_echo {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.leader=false) (ht : (pPsiProbeWall hp l r).2.label.val=ψ-1)
    (hc : (l.reset_cmd || r.reset_cmd)=true) :
    (PPLLAstraR5Repair.pipeline hp κ c l r).1.echo=true := by
  have hb := prefix_bits hp κ c l r
  have hlab : (beforeSuppress hp κ c l r).2.label = ⟨ψ-1,by omega⟩ :=
    Fin.ext ((congrArg Fin.val (prefix_right_label hp κ c l r hl)).trans ht)
  have hs := suppress_echo_terminal hp _ _ ((prefix_leader hp κ c l r).trans hl) hlab
    (by rw [hb.1,hb.2.2.1]; exact hc)
  have hq := pipeline_bits hp κ c l r
  rw [prefix_identity] at hq
  exact hq.2.1.trans hs

/-- Echo transport: when neither endpoint carries reset debt and the responder
holds an echo, a follower initiator leaves the full interaction holding an
echo. This is the counterclockwise echo move of Algorithm 14. -/
theorem pipeline_echo_walk {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.leader=false) (ha : l.reset_cmd=false) (hb : r.reset_cmd=false)
    (he : r.echo=true) :
    (PPLLAstraR5Repair.pipeline hp κ c l r).1.echo=true := by
  have hpb := prefix_bits hp κ c l r
  have hs := suppress_echo_walk hp _ _ ((prefix_leader hp κ c l r).trans hl)
    (hpb.1.trans ha) (hpb.2.2.1.trans hb) (hpb.2.2.2.trans he)
  have hq := pipeline_bits hp κ c l r
  rw [prefix_identity] at hq
  exact hq.2.1.trans hs

/-- Labels on a leaderless interaction: when both inputs are followers and the
responder output is a follower, P′ fired without a probe birth, so the initiator
keeps its label and the responder (both at P′ and at the pipeline output)
carries `label(l)+1 mod ψ`. -/
theorem pipeline_follower_labels {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.leader=false) (hr : r.leader=false)
    (hout : (PPLLAstraR5Repair.pipeline hp κ c l r).2.leader=false) :
    (pPsiProbeWall hp l r).2.label.val=(l.label.val+1)%ψ ∧
    (PPLLAstraR5Repair.pipeline hp κ c l r).2.label.val=(l.label.val+1)%ψ := by
  have hs := PPLLAstraR5ResetFrames.pipeline_zero_no_probe_barrier hp κ c l r hl hr hout
  have hc := PPLLAstraR5ResetFrames.pipeline_followers_control hp κ c l r hl hr
  have hlab : (PPLLAstraR5Repair.pipeline hp κ c l r).2.label=(pPsiProbeWall hp l r).2.label := by
    have h2 := hc.2
    simp only [PPLLAstraR5ResetFrames.control,Prod.mk.injEq] at h2
    exact h2.1
  have hp1 : (pPsiProbeWall hp l r).2.label.val=(l.label.val+1)%ψ := by
    rcases hs with hs | hs
    · by_cases hn : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩
      · simp [pPsiProbeWall,pPsi,hl,hr,hs,hn]
      · cases hx : l.phase <;> simp [pPsiProbeWall,pPsi,hl,hr,hs,hn,hx]
    · simp [pPsiProbeWall,pPsi,hl,hr,hs]
  exact ⟨hp1,by rw [hlab]; exact hp1⟩

/-! ### Configuration-level bookkeeping -/

private abbrev S {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n → AgentState ψ :=
  (protocol hp κ c).step ring C e

private theorem neighbor_ne' {n : Nat} (ring : DirectedRing n) (hn : 1<n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val+1)%n=e.val at he
  by_cases hk : e.val+1<n
  · rw [Nat.mod_eq_of_lt hk] at he; omega
  · have hlast : e.val+1=n := by omega
    rw [hlast,Nat.mod_self] at he; omega

private theorem step_left {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    S hp κ c ring C e e = (PPLLAstraR5Repair.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1 := by
  simp [S,PopulationProtocol.step,protocol]

private theorem step_right {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n) (hn : 1<n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    S hp κ c ring C e (ring.rightNeighbor e) =
      (PPLLAstraR5Repair.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2 := by
  have ne := neighbor_ne' ring hn e
  simp [S,PopulationProtocol.step,protocol,ne]

private theorem step_other {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n) (h1 : i≠e) (h2 : i≠ring.rightNeighbor e) :
    S hp κ c ring C e i = C i := by
  simp [S,PopulationProtocol.step,protocol,h1,h2]

private theorem run_append {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (w1 w2 : List (Fin n)) : ∀ C : Fin n → AgentState ψ,
    run hp κ c ring C (w1++w2) = run hp κ c ring (run hp κ c ring C w1) w2 := by
  induction w1 with
  | nil => intro C; rfl
  | cons e es ih => intro C; exact ih _

/-- Leaderless configuration. -/
private def LF {n ψ : Nat} (C : Fin n → AgentState ψ) : Prop := ∀ i, (C i).leader=false

/-- The goal: some word reaches a leader or a reset-free configuration. -/
private def G {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∃ w : List (Fin n), (∃ i, (run hp κ c ring C w i).leader=true) ∨
    ∀ i, (run hp κ c ring C w i).reset_cmd=false

private theorem G_clean {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (h : ∀ i, (C i).reset_cmd=false) : G hp κ c ring C :=
  ⟨[],Or.inr h⟩

/-- One service either produces a leader (success) or a leaderless successor. -/
private theorem G_step {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : LF (S hp κ c ring C e) → G hp κ c ring (S hp κ c ring C e)) : G hp κ c ring C := by
  classical
  by_cases hl : ∃ i, (S hp κ c ring C e i).leader=true
  · exact ⟨[e],Or.inl hl⟩
  · have hz : LF (S hp κ c ring C e) := by
      intro i
      cases hi : (S hp κ c ring C e i).leader
      · rfl
      · exact False.elim (hl ⟨i,hi⟩)
    obtain ⟨w,hw⟩ := h hz
    exact ⟨e::w,hw⟩

private theorem mod_ne_self {n y k : Nat} (hy : y<n) (hk0 : 0<k) (hk : k<n) :
    (y+k)%n ≠ y := by
  by_cases h : y+k<n
  · rw [Nat.mod_eq_of_lt h]; omega
  · have h1 : (y+k)%n = (y+k-n)%n := by
      rw [Nat.mod_eq_sub_mod (by omega)]
    rw [h1,Nat.mod_eq_of_lt (by omega)]; omega

/-! ### Kill: an echo walks counterclockwise onto the reset's right neighbour -/

/-- The echo at `z` is `d+1` cells clockwise of the single reset at `y`
(`d+2 ≤ n`). Walking the echo back through `d` reset-free edges and then serving
`y` annihilates the last reset. -/
private theorem kill {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n) (hn : 1<n)
    (d : Nat) : ∀ (C : Fin n → AgentState ψ) (y z : Fin n), d+2 ≤ n → LF C →
    (∀ i, (C i).reset_cmd=true → i=y) → (C z).echo=true →
    z.val=(y.val+1+d)%n → G hp κ c ring C := by
  induction d with
  | zero =>
    intro C y z _ hC hy hz hzv
    have hzr : z=ring.rightNeighbor y := Fin.ext (by rw [hzv]; rfl)
    rw [hzr] at hz
    apply G_step hp κ c ring C y
    intro _
    apply G_clean
    have hr := pipeline_follower_reset hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
    intro i
    by_cases h1 : i=y
    · rw [h1,step_left]; exact hr.1
    · by_cases h2 : i=ring.rightNeighbor y
      · rw [h2,step_right hp κ c ring hn]
        have h2' := hr.2
        change (PPLLAstraR5Repair.pipeline hp κ c (C y) (C (ring.rightNeighbor y))).2.reset_cmd = _ at h2'
        rw [h2',hz]; simp
      · rw [step_other hp κ c ring C y i h1 h2]
        cases hc : (C i).reset_cmd
        · rfl
        · exact False.elim (h1 (hy i hc))
  | succ d ih =>
    intro C y z hd hC hy hz hzv
    obtain ⟨p,hpv⟩ : ∃ p : Fin n, p.val=(y.val+1+d)%n := ⟨⟨_,Nat.mod_lt _ (by omega)⟩,rfl⟩
    have hpz : ring.rightNeighbor p = z := by
      apply Fin.ext
      change (p.val+1)%n = z.val
      rw [hpv,Nat.mod_add_mod,hzv,Nat.add_assoc (y.val+1) d 1]
    have hpy : p≠y := by
      intro h
      rw [h] at hpv
      exact mod_ne_self (k:=1+d) y.isLt (by omega) (by omega)
        (by rw [← Nat.add_assoc]; exact hpv.symm)
    have hzy : z≠y := by
      intro h
      rw [h] at hzv
      exact mod_ne_self (k:=1+(d+1)) y.isLt (by omega) (by omega)
        (by rw [← Nat.add_assoc]; exact hzv.symm)
    have hpr : (C p).reset_cmd=false := by
      cases hc : (C p).reset_cmd
      · rfl
      · exact False.elim (hpy (hy p hc))
    have hzr : (C z).reset_cmd=false := by
      cases hc : (C z).reset_cmd
      · rfl
      · exact False.elim (hzy (hy z hc))
    apply G_step hp κ c ring C p
    intro hD
    have hr := pipeline_follower_reset hp κ c (C p) (C (ring.rightNeighbor p)) (hC p)
    apply ih (S hp κ c ring C p) y p (by omega) hD
    · intro i hi
      by_cases h1 : i=p
      · rw [h1,step_left,hr.1] at hi; cases hi
      · by_cases h2 : i=ring.rightNeighbor p
        · rw [h2,step_right hp κ c ring hn] at hi
          have h2' := hr.2
          change (PPLLAstraR5Repair.pipeline hp κ c (C p) (C (ring.rightNeighbor p))).2.reset_cmd = _ at h2'
          rw [h2',hpz,hpr,hzr] at hi; simp at hi
        · rw [step_other hp κ c ring C p i h1 h2] at hi; exact hy i hi
    · rw [step_left]
      exact pipeline_echo_walk hp κ c _ _ (hC p) hpr (by rw [hpz]; exact hzr) (by rw [hpz]; exact hz)
    · exact hpv

/-! ### Walk: a single reset travels until its responder is terminal -/

/-- A single reset at `y` whose responder becomes terminal after `k` further
services can be driven to an echo/reset pair, and then killed. -/
private theorem walk {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n) (hn : 1<n)
    (k : Nat) : ∀ (C : Fin n → AgentState ψ) (y : Fin n), LF C →
    (∀ i, (C i).reset_cmd=true → i=y) →
    ((C y).label.val+1+k)%ψ=ψ-1 → G hp κ c ring C := by
  induction k with
  | zero =>
    intro C y hC hy hk
    apply G_step hp κ c ring C y
    intro hD
    have hr := pipeline_follower_reset hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
    have hr2 := hr.2
    change (PPLLAstraR5Repair.pipeline hp κ c (C y) (C (ring.rightNeighbor y))).2.reset_cmd = _ at hr2
    have hout : (PPLLAstraR5Repair.pipeline hp κ c (C y) (C (ring.rightNeighbor y))).2.leader=false := by
      have := hD (ring.rightNeighbor y); rwa [step_right hp κ c ring hn] at this
    have hlab := pipeline_follower_labels hp κ c (C y) (C (ring.rightNeighbor y)) (hC y) (hC _) hout
    have hframe : ∀ i, i≠y → i≠ring.rightNeighbor y → (S hp κ c ring C y i).reset_cmd=false := by
      intro i h1 h2
      rw [step_other hp κ c ring C y i h1 h2]
      cases hc : (C i).reset_cmd
      · rfl
      · exact False.elim (h1 (hy i hc))
    have hyl : (S hp κ c ring C y y).reset_cmd=false := by rw [step_left]; exact hr.1
    cases hyr : (C y).reset_cmd
    · -- no reset at all
      apply G_clean
      intro i
      by_cases h1 : i=y
      · rw [h1]; exact hyl
      · by_cases h2 : i=ring.rightNeighbor y
        · rw [h2,step_right hp κ c ring hn,hr2,hyr]
          cases hc : (C (ring.rightNeighbor y)).reset_cmd
          · rfl
          · exact False.elim (neighbor_ne' ring hn y (hy _ hc))
        · exact hframe i h1 h2
    · cases hre : (C (ring.rightNeighbor y)).echo
      · -- terminal: an echo is created at `y`, the reset now sits at `y+1`
        have hE : (S hp κ c ring C y y).echo=true := by
          rw [step_left]
          apply pipeline_terminal_echo hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
          · rw [hlab.1]; simpa using hk
          · simp [hyr]
        apply kill hp κ c ring hn (n-2) (S hp κ c ring C y) (ring.rightNeighbor y) y (by omega) hD
        · intro i hi
          by_cases h1 : i=y
          · rw [h1,hyl] at hi; cases hi
          · by_cases h2 : i=ring.rightNeighbor y
            · exact h2
            · rw [hframe i h1 h2] at hi; cases hi
        · exact hE
        · change y.val = (((y.val+1)%n)+1+(n-2))%n
          rw [Nat.add_assoc,Nat.mod_add_mod]
          have : y.val+1+(1+(n-2)) = y.val+n := by omega
          rw [this,Nat.add_mod_right,Nat.mod_eq_of_lt y.isLt]
      · -- the reset dies on the responder echo
        apply G_clean
        intro i
        by_cases h1 : i=y
        · rw [h1]; exact hyl
        · by_cases h2 : i=ring.rightNeighbor y
          · rw [h2,step_right hp κ c ring hn,hr2,hre]; simp
          · exact hframe i h1 h2
  | succ k ih =>
    intro C y hC hy hk
    apply G_step hp κ c ring C y
    intro hD
    have hr := pipeline_follower_reset hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
    have hout : (PPLLAstraR5Repair.pipeline hp κ c (C y) (C (ring.rightNeighbor y))).2.leader=false := by
      have := hD (ring.rightNeighbor y); rwa [step_right hp κ c ring hn] at this
    have hlab := pipeline_follower_labels hp κ c (C y) (C (ring.rightNeighbor y)) (hC y) (hC _) hout
    apply ih (S hp κ c ring C y) (ring.rightNeighbor y) hD
    · intro i hi
      by_cases h1 : i=y
      · rw [h1,step_left,hr.1] at hi; cases hi
      · by_cases h2 : i=ring.rightNeighbor y
        · exact h2
        · rw [step_other hp κ c ring C y i h1 h2] at hi
          exact False.elim (h1 (hy i hi))
    · rw [step_right hp κ c ring hn,hlab.2,Nat.add_assoc,Nat.mod_add_mod]
      rw [← hk]; congr 1; omega

/-! ### Sweep: serving edges `0,…,k-1` clears cells `0,…,k-1` -/

private theorem sweep {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : LF C) (k : Nat) :
    k+1 ≤ n → ∃ w : List (Fin n), (∃ i, (run hp κ c ring C w i).leader=true) ∨
      (LF (run hp κ c ring C w) ∧ ∀ i : Fin n, i.val<k → (run hp κ c ring C w i).reset_cmd=false) := by
  induction k with
  | zero => intro _; exact ⟨[],Or.inr ⟨hC,fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨w,hw⟩ := ih (by omega)
    rcases hw with hw | ⟨hD,hc⟩
    · exact ⟨w,Or.inl hw⟩
    · classical
      generalize hDw : run hp κ c ring C w = D at hD hc
      obtain ⟨e,hev⟩ : ∃ e : Fin n, e.val=k := ⟨⟨k,by omega⟩,rfl⟩
      have hrun : run hp κ c ring C (w++[e]) = S hp κ c ring D e := by
        rw [run_append,hDw]; rfl
      by_cases hl : ∃ i, (S hp κ c ring D e i).leader=true
      · exact ⟨w++[e],Or.inl (by rw [hrun]; exact hl)⟩
      · refine ⟨w++[e],Or.inr ⟨?_,?_⟩⟩
        · intro i
          rw [hrun]
          cases hi : (S hp κ c ring D e i).leader
          · rfl
          · exact False.elim (hl ⟨i,hi⟩)
        · intro i hi
          rw [hrun]
          have hr := pipeline_follower_reset hp κ c (D e) (D (ring.rightNeighbor e)) (hD e)
          by_cases h1 : i=e
          · rw [h1,step_left]; exact hr.1
          · have hik : i.val<k := by
              have : i.val≠k := fun h => h1 (Fin.ext (h.trans hev.symm))
              omega
            have h2 : i≠ring.rightNeighbor e := by
              intro h
              have := congrArg Fin.val h
              change i.val=(e.val+1)%n at this
              rw [hev,Nat.mod_eq_of_lt (by omega)] at this
              omega
            rw [step_other hp κ c ring D e i h1 h2]
            exact hc i hik

/-! ### Headline -/

/-- **Reset drain for actual R5.** From any configuration on a directed
ring with at least two cells, some physical word reaches a configuration that
has a leader or carries no `reset_cmd` anywhere. Labels, echoes, κ and all
ancillary fields are arbitrary. The leaderless part of the word is a sweep
(gathering all reset debt on the last cell), a walk of at most `ψ` services
(which relabels consecutively until the responder is terminal and an echo is
born), and an echo walk of `n-2` services followed by the annihilating
service. -/
theorem exists_reset_free_or_positive {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (ring : DirectedRing n) (hn : 1<n) (C : Fin n → AgentState ψ) :
    ∃ w : List (Fin n), (∃ i, (run hp κ c ring C w i).leader=true) ∨
      ∀ i, (run hp κ c ring C w i).reset_cmd=false := by
  classical
  by_cases hc : ∃ i, (C i).leader=true
  · exact ⟨[],Or.inl hc⟩
  have hC : LF C := by
    intro i
    cases hi : (C i).leader
    · rfl
    · exact False.elim (hc ⟨i,hi⟩)
  obtain ⟨w,hw⟩ := sweep hp κ c ring C hC (n-1) (by omega)
  rcases hw with hw | ⟨hD,hcl⟩
  · exact ⟨w,Or.inl hw⟩
  generalize hDw : run hp κ c ring C w = D at hD hcl
  let last : Fin n := ⟨n-1,by omega⟩
  have hy : ∀ i, (D i).reset_cmd=true → i=last := by
    intro i hi
    apply Fin.ext
    change i.val=n-1
    by_cases h : i.val<n-1
    · rw [hcl i h] at hi; cases hi
    · have := i.isLt; omega
  have hG : G hp κ c ring D := by
    have hlt := (D last).label.isLt
    by_cases hL : (D last).label.val+1 ≤ ψ-1
    · apply walk hp κ c ring hn (ψ-1-((D last).label.val+1)) D last hD hy
      have : (D last).label.val+1+(ψ-1-((D last).label.val+1)) = ψ-1 := by omega
      rw [this,Nat.mod_eq_of_lt (by omega)]
    · apply walk hp κ c ring hn (ψ-1) D last hD hy
      have : (D last).label.val+1+(ψ-1) = (ψ-1)+ψ := by omega
      rw [this,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨w2,hw2⟩ := hG
  exact ⟨w++w2,by rw [run_append,hDw]; exact hw2⟩

/-- Reachability form of `exists_reset_free_or_positive`. -/
theorem exists_reset_free_or_positive_reachable {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (ring : DirectedRing n) (hn : 1<n) (C : Fin n → AgentState ψ) :
    ∃ D : Fin n → AgentState ψ, (protocol hp κ c).Reachable ring C D ∧
      ((∃ i, (D i).leader=true) ∨ ∀ i, (D i).reset_cmd=false) := by
  obtain ⟨w,hw⟩ := exists_reset_free_or_positive hp κ c ring hn C
  exact ⟨run hp κ c ring C w,run_reachable hp κ c ring C w,hw⟩

#print axioms pipeline_follower_reset
#print axioms pipeline_terminal_echo
#print axioms pipeline_echo_walk
#print axioms pipeline_follower_labels
#print axioms exists_reset_free_or_positive
#print axioms exists_reset_free_or_positive_reachable

#print axioms run_reachable
#print axioms PPLLAstraR5ResetFrames.pipeline_followers_control
#print axioms PPLLAstraR5ResetFrames.pipeline_pPsi_responder_survives
#print axioms PPLLAstraR5ResetFrames.pipeline_zero_no_probe_barrier
end PPLLAstraR5ResetDrain
