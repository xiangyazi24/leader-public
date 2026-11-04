import Leader.Wu.ShortGap.GhostRoundInterface

/-!
# Strict accounting rounds and zero-debt service

The accounting index is carried by the active state. Round r starts with
all roots at generation at least r and zero predecessor debt. Service r
drains the generation-aware round-r debt, stored at latentDebt2 (r+1).
All transitions below use exactly one literal physical ghost step.
-/
namespace ShortGapGhostComposition2
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapLineage ShortGapLineageRetained ShortGapTwoEpoch
open ShortGapGenerationMask ShortGapDenialTransportLiteral
open ShortGapLineage2Closure ShortGapLineage2ClosureB
open FiniteUniformStoppingTree BalancedFailureRestartPartialExitEntry
open ShortGapPipelinedRearmSpec
set_option autoImplicit false

/-- A fully rearmed accounting cut. The four fields are precisely the
requested base conditions; no progress or closure law is carried. -/
structure RoundBase (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop where
  lineage : Lineage2 R s
  entered : ∀ i, r ≤ s.k i
  zero : latentDebt2 R r s = 0
  noSuccess : ¬ VirtualSuccess R r s

theorem RoundBase.toDom {R : RFrame} {r : Nat} {s : GhostRing2 R}
    (h : RoundBase R r s) : Dom R r s :=
  ⟨h.lineage,fun i => Nat.le_trans (Nat.sub_le _ _) (h.entered i),h.noSuccess⟩

/-- Once all owners entered r, generation masking discharges every
round-(r-1) token independently of its retained annotations. -/
theorem all_entered_debt_zero (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (h : ∀ i, r ≤ s.k i) : latentDebt2 R r s = 0 := by
  have ht := all_joined_tokens_done R r (curView R s) h
  simp [latentDebt2,tokens2,litTotalHops,ht,LitGapState.hops,ofFn_sum_const]

/-- The converse is the checked normalized-port argument: a lagging
root at zero debt would hold two denials and would already have JOINed. -/
theorem debt0_all_entered (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hn : ¬ VirtualSuccess R r s)
    (hz : latentDebt2 R r s = 0) : ∀ i, r ≤ s.k i := by
  have hd : DenialOnly2 R r s := by
    rcases denial2_or_predecessor_candidate R r s with hd | hc
    · exact hd
    · exact False.elim (hn ⟨r-1,candidate_round_le_maxGen R s hs _ hc,hc⟩)
  exact latentDebt2_zero_all_joined R r s hs hd hz

/-- Base conditions persist until the actual virtual-success port. -/
theorem RoundBase.step {R : RFrame} {r : Nat} {s : GhostRing2 R}
    (h : RoundBase R r s) (e : Vtx R)
    (hn : ¬ VirtualSuccess R r (ghostStep2 R s e)) : RoundBase R r (ghostStep2 R s e) where
  lineage := lineage2_step R s h.lineage e
  entered := fun i => Nat.le_trans (h.entered i) (Nat.le_add_right _ _)
  zero := all_entered_debt_zero R r _ (fun i => Nat.le_trans (h.entered i) (Nat.le_add_right _ _))
  noSuccess := hn

/-- Index-carrying round state; remaining Race excludes both terminals. -/
structure Round (R : RFrame) where
  idx : Nat
  state : GhostRing2 R
  base : RoundBase R idx state
  race : PeriodHIncidenceChoice.HasRace (word2 R idx state)

noncomputable def roundStep (R : RFrame) (s : Round R) (e : Fin R.n) : StopNode (Round R) := by
  classical
  let t := ghostStep2 R s.state (edgeVtx R e)
  exact if hv : VirtualSuccess R s.idx t then .success
    else if hr : PeriodHIncidenceChoice.HasRace (word2 R s.idx t) then
      .active ⟨s.idx,t,s.base.step _ hv,hr⟩ else .failure

def roundPotential (R : RFrame) : StopNode (Round R) → Nat
  | .active s => R.n * PeriodHIncidenceChoice.choiceRaceReserve (word2 R s.idx s.state)
  | .success | .failure => 0

/-- Specializing the literal child sum to zero predecessor debt gives
the reserve-only round Bellman inequality, with no latent-debt charge. -/
theorem reserve_childSum (R : RFrame) (s : Round R) :
    1 + (List.ofFn (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
      (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))))).sum ≤
      R.n * PeriodHIncidenceChoice.choiceRaceReserve (word2 R s.idx s.state) := by
  have hz : ∀ e, latentDebt2 R s.idx (ghostStep2 R s.state e) = 0 := by
    intro e
    exact all_entered_debt_zero R s.idx _ (fun i => Nat.le_trans (s.base.entered i) (Nat.le_add_right _ _))
  have h := ShortGapLineage2Closure.genPipelined2_childSum R s.idx s.state s.base.toDom s.race
  simpa only [roundDebt2,s.base.zero,hz,Nat.add_zero] using h

theorem round_bellman (R : RFrame) : NatBellmanSuperSolution (roundStep R) 1 (roundPotential R) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  have hsum : (List.ofFn (fun e => roundPotential R (roundStep R s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => R.n * PeriodHIncidenceChoice.choiceRaceReserve
        (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))))).sum := by
    apply ofFn_sum_le
    intro e
    unfold roundStep
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  rw [ofFn_sum_mul_left] at hsum
  have h := Nat.mul_le_mul_left R.n (reserve_childSum R s)
  rw [Nat.mul_add,Nat.mul_one] at h
  change 1*R.n + _ ≤ R.n * (R.n * _)
  rw [Nat.one_mul]
  omega

theorem roundStep_success_iff (R : RFrame) (s : Round R) (e : Fin R.n) :
    roundStep R s e = .success ↔ VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) := by
  classical
  unfold roundStep
  dsimp only
  split <;> simp_all
  split <;> simp_all

theorem roundStep_failure_iff (R : RFrame) (s : Round R) (e : Fin R.n) :
    roundStep R s e = .failure ↔ RoundFailure R s.idx (ghostStep2 R s.state (edgeVtx R e)) := by
  classical
  have hf : PeriodHIncidenceChoice.Frozen (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))) ↔
      ¬ PeriodHIncidenceChoice.HasRace (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))) := by
    simp only [PeriodHIncidenceChoice.Frozen,PeriodHIncidenceChoice.HasRace,not_exists]
  unfold roundStep
  dsimp only
  split
  · simp_all [RoundFailure]
  · split <;> simp_all [RoundFailure]

private theorem failureWeight_indicator {S : Type} (x : StopNode S) :
    failureWeight x = @ite Nat (x = .failure) (Classical.propDecidable _) 1 0 := by
  classical
  cases x <;> simp [failureWeight]

private theorem successWeight_indicator {S : Type} (x : StopNode S) :
    successWeight x = @ite Nat (x = .success) (Classical.propDecidable _) 1 0 := by
  classical
  cases x <;> simp [successWeight]

theorem round_balance (R : RFrame) (s : Round R) :
    (List.ofFn (fun e : Fin R.n => failureWeight (roundStep R s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => successWeight (roundStep R s e))).sum := by
  classical
  simp only [failureWeight_indicator,successWeight_indicator,roundStep_failure_iff,roundStep_success_iff]
  exact ShortGapLineage2Closure.genPipelined2_localBalance R s.idx s.state s.base.toDom s.race

noncomputable def ghostRoundSpec' (R : RFrame) : PipelinedRoundSpec R.n where
  Round := Round R
  step := roundStep R
  potential := roundPotential R
  bellman := round_bellman R
  balance := round_balance R

theorem roundPotential_le (R : RFrame) (s : Round R) :
    roundPotential R (.active s) ≤ R.n*R.m :=
  Nat.mul_le_mul_left R.n (ShortGapChoiceStopping.choiceRaceReserve_le _)

/-- A resolved history word stays fixed under every ghost step. -/
theorem frozen_word_step (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hf : PeriodHIncidenceChoice.Frozen (word2 R r s)) (e : Vtx R) :
    word2 R r (ghostStep2 R s e) = word2 R r s := by
  funext i
  have hn := hf i
  cases hh : s.hist i r with
  | none => exact False.elim (hn (by simp [word2,wordOf,curView,hh,choiceToWord]))
  | some c =>
    have hp := history2_monotone R s e i r c hh
    simp only [word2,wordOf,curView,hh,hp]

/-- Service r drains round r, with debt at index r+1. The zero-debt
state is an exit, so it is excluded from this active domain. -/
structure ServiceDom (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop where
  lineage : Lineage2 R s
  frozen : PeriodHIncidenceChoice.Frozen (word2 R r s)
  constant : PeriodHIncidenceChoice.Constant (word2 R r s)
  noSuccess : ¬ VirtualSuccess R r s
  positive : 0 < latentDebt2 R (r+1) s

theorem ServiceDom.toDom {R : RFrame} {r : Nat} {s : GhostRing2 R}
    (h : ServiceDom R r s) : Dom R (r+1) s :=
  ⟨h.lineage,by
    intro i
    simpa only [Nat.add_sub_cancel] using
      ShortGapGhostComposition.frozen_word_entered R s h.lineage r h.frozen i,h.noSuccess⟩

theorem ServiceDom.step {R : RFrame} {r : Nat} {s : GhostRing2 R}
    (h : ServiceDom R r s) (e : Vtx R)
    (hn : ¬ VirtualSuccess R r (ghostStep2 R s e))
    (hp : 0 < latentDebt2 R (r+1) (ghostStep2 R s e)) : ServiceDom R r (ghostStep2 R s e) where
  lineage := lineage2_step R s h.lineage e
  frozen := by rw [frozen_word_step R r s h.frozen e]; exact h.frozen
  constant := by rw [frozen_word_step R r s h.frozen e]; exact h.constant
  noSuccess := hn
  positive := hp

private theorem fresh_left_ccw (a : Agent) :
    (row (.root .race .toSend .free) a).1.ccwPort = some .free := by
  cases a with
  | interior t => cases t <;> rfl
  | root c cw ccw => cases ccw <;> rfl

/-- A fresh Race root cannot consume two denials in the same interaction
that first resolves it: one of its two own ports is still clear. -/
theorem fresh_no_join (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (i : Fin R.m)
    (hi : s.cfg (rootV R i) = .root .race .toSend .free) :
    fires R (physical2 R s) e i = false := by
  cases hf : fires R (physical2 R s) e i with
  | false => rfl
  | true =>
    obtain ⟨hinc,c,hraw⟩ := (fires_iff R (physical2 R s) e i).mp hf
    change rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial at hraw
    by_cases hl : rootV R i = e
    · have hh : s.cfg e = .root .race .toSend .free := hl ▸ hi
      have hp := congrArg Agent.ccwPort hraw
      rw [rawAt,if_pos hl,hh,fresh_left_ccw] at hp
      cases hp
    · by_cases hr : rootV R i = rn R e
      · have hh : s.cfg (rn R e) = .root .race .toSend .free := hr ▸ hi
        have hp := congrArg Agent.cwPort hraw
        rw [rawAt,if_neg hl,if_pos hr,hh,ShortGapTwoEpochLaws.row_right_cw] at hp
        cases hp
      · exact False.elim (hinc.elim hl hr)

/-- At a strict base, a Race in word r is a still-unresolved root of
generation exactly r; history cannot revert a recorded choice to Race. -/
theorem race_root_current (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hi : ∀ i, r ≤ s.k i) (i : Fin R.m)
    (hr : word2 R r s i = .race) :
    s.k i = r ∧ s.cfg (rootV R i) = .root .race .toSend .free := by
  have hh : s.hist i r = none := by
    cases he : s.hist i r with
    | none => rfl
    | some c =>
      have hn := hs.coherent.histValues i r c he
      cases c <;> simp_all [word2,wordOf,curView,choiceToWord]
  have hk : s.k i = r := by
    have hb := hi i
    by_cases h : r < s.k i
    · obtain ⟨c,hc⟩ := hs.coherent.histPast i r h
      change s.hist i r = some c at hc
      rw [hh] at hc; cases hc
    · omega
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots i
  have hnow := hs.coherent.histNow i c cw ccw hroot
  change s.cfg (rootV R i) = .root c cw ccw at hroot
  change s.hist i (s.k i) = resolvedOpt c at hnow
  rw [hk,hh] at hnow
  have hc : c = .race := by cases c <;> first | rfl | cases hnow
  refine ⟨hk,hs.coherent.raceReady i ?_⟩
  change (s.cfg (rootV R i)).choice = some .race
  rw [hroot,hc]; rfl

/-- A newly joined root has no choice recorded yet in its new generation. -/
theorem joined_word_race (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hf : fires R (physical2 R s) e i = true) :
    word2 R ((ghostStep2 R s e).k i) (ghostStep2 R s e) i = .race := by
  have hroot := root_cfg_join R s e i hf
  have hp := (lineage2_step R s hs e).coherent.histNow i .race .toSend .free hroot
  change (ghostStep2 R s e).hist i ((ghostStep2 R s e).k i) = none at hp
  simp [word2,wordOf,curView,hp,choiceToWord]

/-- A round failure really enters active service: its last unresolved
root could not JOIN in that resolving interaction. -/
theorem failure_service_entry (R : RFrame) (s : Round R) (e : Fin R.n)
    (hf : roundStep R s e = .failure) : ServiceDom R s.idx (ghostStep2 R s.state (edgeVtx R e)) := by
  have ht := lineage2_step R s.state s.base.lineage (edgeVtx R e)
  have hh := (roundStep_failure_iff R s e).mp hf
  have hd : Dom R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) := ⟨ht,by
    intro i
    simpa only [Nat.add_sub_cancel] using
      ShortGapGhostComposition.frozen_word_entered R _ ht s.idx hh.1 i,hh.2⟩
  obtain ⟨i,hi⟩ := s.race
  obtain ⟨hk,hroot⟩ := race_root_current R s.idx s.state s.base.lineage s.base.entered i hi
  have hj := fresh_no_join R s.state (edgeVtx R e) i hroot
  have hp : (ghostStep2 R s.state (edgeVtx R e)).k i < s.idx+1 := by
    simp [ghostStep2_k,hj,hk]
  exact ⟨ht,hh.1,roundFailure_uniform R s.idx _ (C4_step R s.state s.base.lineage _) hh,hh.2,
    ShortGapTwoEpochLaws.unjoined_debt_on_dom R (s.idx+1) _ (dom_accounting R _ _ hd) i hp⟩

/-- A service exit supplies both the next strict base and a genuine
remaining Race: some last lagging root JOINed on this edge. -/
theorem service_exit (R : RFrame) (r : Nat) (s : GhostRing2 R) (hs : ServiceDom R r s)
    (e : Vtx R) (hn : ¬ VirtualSuccess R r (ghostStep2 R s e))
    (hz : latentDebt2 R (r+1) (ghostStep2 R s e) = 0) :
    RoundBase R (r+1) (ghostStep2 R s e) ∧
      PeriodHIncidenceChoice.HasRace (word2 R (r+1) (ghostStep2 R s e)) := by
  have hpost := lineage2_step R s hs.lineage e
  have hentered := debt0_all_entered R (r+1) _ hpost hn hz
  refine ⟨⟨hpost,hentered,hz,hn⟩,?_⟩
  have hex : ∃ i, s.k i < r+1 := by
    apply Classical.byContradiction
    intro hh
    have ha : ∀ i, r+1 ≤ s.k i := by
      intro i
      have hi : ¬ s.k i < r+1 := fun hi => hh ⟨i,hi⟩
      omega
    have hz := all_entered_debt_zero R (r+1) s ha
    have hp := hs.positive
    omega
  obtain ⟨i,hi⟩ := hex
  have hnew := hentered i
  have hk := ghostStep2_k R s e i
  have hf : fires R (physical2 R s) e i = true := by
    cases hh : fires R (physical2 R s) e i with
    | true => rfl
    | false => simp only [hh,Bool.false_eq_true,if_false,Nat.add_zero] at hk; omega
  have heq : (ghostStep2 R s e).k i = r+1 := by
    simp only [hf,if_true] at hk
    omega
  exact ⟨i,heq ▸ joined_word_race R s hs.lineage e i hf⟩

structure Service (R : RFrame) where
  idx : Nat
  state : GhostRing2 R
  dom : ServiceDom R idx state

noncomputable def serviceStep (R : RFrame) (s : Service R) (e : Fin R.n) :
    ServiceOutcome (Service R) (Round R) := by
  classical
  let t := ghostStep2 R s.state (edgeVtx R e)
  exact if hv : VirtualSuccess R s.idx t then .succeed
    else if hz : latentDebt2 R (s.idx+1) t = 0 then
      .exit ⟨s.idx+1,t,(service_exit R s.idx s.state s.dom _ hv hz).1,
        (service_exit R s.idx s.state s.dom _ hv hz).2⟩
    else .cont ⟨s.idx,t,s.dom.step _ hv (Nat.pos_of_ne_zero hz)⟩

def servicePotential (R : RFrame) (s : Service R) : Nat :=
  R.n * latentDebt2 R (s.idx+1) s.state

private theorem sum_strict {n : Nat} (f g : Fin n → Nat) (i : Fin n)
    (hle : ∀ j, f j ≤ g j) (hlt : f i < g i) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht := ofFn_sum_le (fun j : Fin n => f j.succ) (fun j => g j.succ)
        (fun j => hle j.succ)
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      let j : Fin n := ⟨i.val-1,by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin n => f j.succ) (fun j => g j.succ) j
        (fun j => hle j.succ) (by simpa only [hj] using hlt)
      have h0 := hle 0
      omega

/-- Every service child has nonincreasing debt and one physical edge
strictly advances; service success and exit can only lower its potential. -/
theorem service_bellman (R : RFrame) : ServiceBellman (serviceStep R) 1 (servicePotential R) := by
  classical
  intro s
  have hd := dom_accounting R (s.idx+1) s.state s.dom.toDom
  have hle := ShortGapTwoEpochLaws.latentDebt2_step_le R (s.idx+1) s.state hd
  obtain ⟨e,he⟩ := ShortGapTwoEpochLaws.advancing_edge_lowers_latentDebt2 R (s.idx+1) s.state hd s.dom.positive
  have hlt := sum_strict
    (fun a : Fin R.n => latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R a)))
    (fun _ => latentDebt2 R (s.idx+1) s.state) (encE R e.1 e.2)
    (fun a => hle _) (by rw [edgeVtx_encE]; change latentDebt2 R (s.idx+1) (ghostStep2 R s.state e) < _; omega)
  rw [ofFn_sum_const] at hlt
  have hsum : (List.ofFn (fun a : Fin R.n =>
      serviceOutcomePotential (servicePotential R) (serviceStep R s a))).sum ≤
      (List.ofFn (fun a : Fin R.n => R.n * latentDebt2 R (s.idx+1)
        (ghostStep2 R s.state (edgeVtx R a)))).sum := by
    apply ofFn_sum_le
    intro a
    unfold serviceStep
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
  rw [ofFn_sum_mul_left] at hsum
  have hb : 1 + (List.ofFn (fun a : Fin R.n =>
      latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R a)))).sum ≤
      R.n * latentDebt2 R (s.idx+1) s.state := by omega
  have hm := Nat.mul_le_mul_left R.n hb
  rw [Nat.mul_add,Nat.mul_one] at hm
  change 1*R.n + _ ≤ R.n * (R.n * _)
  rw [Nat.one_mul]
  omega

/-- Uniform per-service budget, including any total-function fallback. -/
theorem servicePotential_le (R : RFrame) (s : Service R) :
    servicePotential R s ≤ R.n*R.m*(2*R.h-1) := by
  have h := ShortGapCohortCut.latentDebt_le R (s.idx+1) (curView R s.state)
  change latentDebt2 R (s.idx+1) s.state ≤ R.m*(2*R.h-1) at h
  have h' := Nat.mul_le_mul_left R.n h
  simpa only [servicePotential,Nat.mul_assoc] using h'

/-- The repository's actual clean start is uniform service for round 0:
k=0, history 0 resolved to the fixed base, and all gap tokens prelaunch. -/
def initialService (R : RFrame) : Service R where
  idx := 0
  state := ghostStart2 R
  dom := {
    lineage := lineage2_start R
    frozen := by
      intro i
      rcases R.hb with hb | hb <;>
        simp [word2,wordOf,curView,ghostStart2,ghostStart,hb,choiceToWord]
    constant := ⟨choiceToWord R.b,by intro i; rfl⟩
    noSuccess := (ShortGapLineage2Closure.dom_start R).2.2
    positive := by
      rw [latentDebt2_start]
      exact Nat.mul_pos (by have := R.hm; omega) (by have := R.hh; omega) }

/-- The interface requires a total entry function. Its fallback is never
used by restartStep: actual failures enter their own physical child. -/
noncomputable def serviceEntry (R : RFrame) (s : Round R) (e : Fin R.n) : Service R := by
  classical
  exact if hf : roundStep R s e = .failure then
    ⟨s.idx,ghostStep2 R s.state (edgeVtx R e),failure_service_entry R s e hf⟩
    else initialService R

theorem serviceEntry_of_failure (R : RFrame) (s : Round R) (e : Fin R.n)
    (hf : roundStep R s e = .failure) :
    (serviceEntry R s e).idx = s.idx ∧
      (serviceEntry R s e).state = ghostStep2 R s.state (edgeVtx R e) := by
  simp [serviceEntry,hf]

/-- Fully instantiated cross-round restart certificate. Both budgets
are literal: A=nm and service budget nm(2h-1). -/
noncomputable def ghostRearmSpec (R : RFrame) :
    PipelinedRearmSpec (ghostRoundSpec' R) (R.n*R.m) (R.n*R.m*(2*R.h-1)) where
  State := Service R
  step := serviceStep R
  entry := serviceEntry R
  potential := servicePotential R
  bellman := service_bellman R
  entry_le := fun s e => servicePotential_le R (serviceEntry R s e)
  exit_le := fun _ _ t _ => roundPotential_le R t

theorem ghostRearm_bellman (R : RFrame) :
    NatBellmanSuperSolution (ghostRearmSpec R).restartStep 1 (ghostRearmSpec R).restartPotential :=
  (ghostRearmSpec R).restart_natBellmanSuperSolution

theorem tightBudget_eq (R : RFrame) :
    2*(R.n*R.m) + R.n*R.m*(2*R.h-1) = R.n*R.m*(2*R.h+1) := by
  calc
    _ = R.n*R.m*(2+(2*R.h-1)) := by rw [Nat.mul_add]; ac_rfl
    _ = _ := congrArg (R.n*R.m*·) (by have := R.hh; omega)

/-- Tight composed cost from any strict round base, including partially
played words. This statement does not identify the clean service start
with a rearmed round base. -/
theorem composed_truncatedCost_le (R : RFrame) (s : Round R) (T : Nat) :
    truncatedActiveCostNumerator (ghostRearmSpec R).restartStep (.active (.round s)) T ≤
      R.n^T * (R.n*R.m*(2*R.h+1)) := by
  have h := (ghostRearmSpec R).base_truncatedCost_le s T
  have hp := roundPotential_le R s
  apply Nat.le_trans h (Nat.mul_le_mul_left _ ?_)
  rw [← tightBudget_eq]
  change roundPotential R (.active s) + _ ≤ _
  omega

/-- The physical clean start carries the service potential as well as
the restart reserve. Its exact initial credit is 4nmh. -/
theorem initialService_potential (R : RFrame) :
    (ghostRearmSpec R).restartPotential (.active (.reset (initialService R))) = 4*R.n*R.m*R.h := by
  change R.n * latentDebt2 R 1 (ghostStart2 R) + R.n*R.m +
    (R.n*R.m + R.n*R.m*(2*R.h-1)) = _
  rw [latentDebt2_start]
  have he : 2+(2*R.h-1)+(2*R.h-1) = 4*R.h := by have := R.hh; omega
  calc
    _ = R.n*R.m*(2+(2*R.h-1)+(2*R.h-1)) := by
      simp only [Nat.mul_add,Nat.mul_two]
      ac_rfl
    _ = _ := by rw [he]; ac_rfl

/-- Alternative composed bound for the unchanged physical clean start.
The larger constant pays its initial round-0 service explicitly. -/
theorem cleanStart_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (ghostRearmSpec R).restartStep
      (.active (.reset (initialService R))) T ≤ R.n^T * (4*R.n*R.m*R.h) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (ghostRearmSpec R).restartStep 1 (ghostRearmSpec R).restartPotential
    (ghostRearm_bellman R) (.active (.reset (initialService R))) T
  simpa only [Nat.one_mul,initialService_potential] using h

private theorem success_tail_of_cost_bound {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S) (s : S)
    (hn : ∀ s e, step s e ≠ .failure) (hB : 0 < B)
    (hc : ∀ T, truncatedActiveCostNumerator step (.active s) T ≤ n^T*B) (factor : Nat) :
    (factor-1)*n^(factor*B) ≤ factor*successCount step (.active s) (factor*B) := by
  have hd := horizon_mul_activeCount_le_truncatedActiveCostNumerator step (.active s) (factor*B)
  have hb := hc (factor*B)
  have hmul : B * (factor * activeCount step (.active s) (factor*B)) ≤ B*n^(factor*B) := by
    calc
      _ = (factor*B)*activeCount step (.active s) (factor*B) := by ac_rfl
      _ ≤ n^(factor*B)*B := Nat.le_trans hd hb
      _ = _ := Nat.mul_comm _ _
  have hactive := Nat.le_of_mul_le_mul_left hmul hB
  have hfailure := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure step hn s (factor*B)
  have hp := node_count_partition step (.active s) (factor*B)
  have hsum : activeCount step (.active s) (factor*B) + successCount step (.active s) (factor*B) = n^(factor*B) := by omega
  by_cases hf : factor = 0
  · simp [hf]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf
    simp only [Nat.add_sub_cancel,Nat.succ_eq_add_one] at hactive hsum ⊢
    rw [← hsum] at hactive ⊢
    rw [Nat.mul_add]
    simp only [Nat.add_mul,Nat.one_mul] at hactive ⊢
    omega

theorem composed_success_one_minus_inv_factor (R : RFrame) (s : Round R) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m*(2*R.h+1))) ≤
      factor*successCount (ghostRearmSpec R).restartStep (.active (.round s))
        (factor*(R.n*R.m*(2*R.h+1))) := by
  apply success_tail_of_cost_bound _ _ (ghostRearmSpec R).restartStep_ne_failure _
    (composed_truncatedCost_le R s) factor
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by have := R.hm; omega) R.hh) (by have := R.hm; omega)) (by omega)

theorem cleanStart_success_one_minus_inv_factor (R : RFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.m*R.h)) ≤
      factor*successCount (ghostRearmSpec R).restartStep (.active (.reset (initialService R)))
        (factor*(4*R.n*R.m*R.h)) := by
  apply success_tail_of_cost_bound _ _ (ghostRearmSpec R).restartStep_ne_failure _
    (cleanStart_truncatedCost_le R) factor
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
    (Nat.mul_pos (by have := R.hm; omega) R.hh)) (by have := R.hm; omega)) R.hh

/-- Relabelling the existing physical clean start cannot turn it into
an active strict round: entered forces index 0, whose word is resolved. -/
theorem cleanStart_not_active_round (R : RFrame) (r : Nat) :
    ¬ (RoundBase R r (ghostStart2 R) ∧ PeriodHIncidenceChoice.HasRace (word2 R r (ghostStart2 R))) := by
  rintro ⟨hb,hr⟩
  have hk := hb.entered ⟨0,by have := R.hm; omega⟩
  change r ≤ 0 at hk
  have hz : r = 0 := by omega
  subst r
  obtain ⟨i,hi⟩ := hr
  rcases R.hb with h | h <;> simp [word2,wordOf,curView,ghostStart2,ghostStart,h,choiceToWord] at hi

/-! The strict round-1 start is the rearmed all-Race configuration,
distinct from ghostStart2, which still owes uniform round-0 service. -/

def strictStart (R : RFrame) : GhostRing2 R where
  cfg v := if v.2.val = 0 then .root .race .toSend .free else .interior .empty
  k _ := 1
  hist _ q := if q = 0 then some R.b else none
  epoch _ := ⟨.idle,.idle⟩

theorem strictStart_root (R : RFrame) (g : Fin R.m) :
    (strictStart R).cfg (rootV R g) = .root .race .toSend .free := rfl

theorem strictStart_view_epoch (R : RFrame) (g : Fin R.m) :
    (view R (strictStart R)).epoch g = .delivered 0 R.b R.b := by
  simp [strictStart,view,prefixView,combinedView]

theorem strictStart_shape (R : RFrame) : C1 R (strictStart R) := by
  intro g
  rw [EpochShape,strictStart_view_epoch]
  refine ⟨Or.inr rfl,Or.inr rfl,rfl,rfl,?_⟩
  intro a ha
  change (strictStart R).cfg (g,a) = _
  change (if a.val = 0 then Agent.root .race .toSend .free else .interior .empty) = _
  rw [if_neg (by omega : a.val ≠ 0)]

/-- A concrete inhabitant of the strict base, retaining the completed
uniform round-0 history and fresh Race ports at generation 1. -/
theorem strictStart_lineage (R : RFrame) : Lineage2 R (strictStart R) := by
  apply (lineage2_iff_clauses R _).mpr
  refine ⟨?_,strictStart_shape R,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨fun i => ⟨.race,.toSend,.free,rfl⟩,fun _ => rfl,fun _ _ => rfl⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro g
      change _ ↔ Live ((view R (strictStart R)).epoch g)
      rw [strictStart_view_epoch]
      exact ⟨(fun h => by cases h),False.elim⟩
    · intro g
      change CwHeld (some .toSend) ↔ DeliveredAt ((view R (strictStart R)).epoch g) 1
      rw [strictStart_view_epoch]
      exact ⟨False.elim,fun h => by change 1 ≤ 0 at h; omega⟩
    · intro g h
      change DeliveredAt ((view R (strictStart R)).epoch g) 1 at h
      rw [strictStart_view_epoch] at h
      change 1 ≤ 0 at h
      omega
    · intro g _; rfl
    · intro g
      exact ⟨(fun h => by cases h),False.elim⟩
  · refine ⟨?_,?_,?_⟩
    · intro g
      change CcwHeld (some .free) ↔ ComparedAt ((view R (strictStart R)).epoch g) 1
      rw [strictStart_view_epoch]
      exact ⟨False.elim,fun h => by change 1 ≤ 0 at h; omega⟩
    · intro g h
      change ComparedAt ((view R (strictStart R)).epoch g) 1 at h
      rw [strictStart_view_epoch] at h
      change 1 ≤ 0 at h
      omega
    · intro g
      exact ⟨False.elim,fun h => h.elim id id⟩
  · refine ⟨?_,?_,?_,?_⟩
    · intro i q c hc
      change (if q = 0 then some R.b else none) = some c at hc
      split at hc
      · cases hc
        rcases R.hb with hb | hb <;> simp [hb]
      · cases hc
    · intro i q hq
      change q < 1 at hq
      have hq0 : q = 0 := by omega
      subst q
      exact ⟨R.b,rfl⟩
    · intro i c cw ccw hc
      change (strictStart R).cfg (rootV R i) = .root c cw ccw at hc
      rw [strictStart_root] at hc
      cases hc
      rfl
    · intro i q hq
      change 1 < q at hq
      change (if q = 0 then some R.b else none) = none
      exact if_neg (by omega)
  · intro g; trivial
  · intro g; trivial
  · apply C7_of_C1_completed_denials R _ (strictStart_shape R)
    intro i q hq
    change q < 1 at hq
    have hq0 : q = 0 := by omega
    subst q
    have hb : res R.b R.b = .denial := by rcases R.hb with hb | hb <;> simp [hb,res]
    exact ⟨⟨R.b,R.b,rfl,rfl,hb⟩,⟨R.b,R.b,rfl,rfl,hb⟩⟩

theorem strictStart_no_success (R : RFrame) : ¬ VirtualSuccess R 1 (strictStart R) := by
  rintro ⟨q,_,g,hg⟩
  have hw : ∀ i, word2 R q (strictStart R) i = choiceToWord
      ((if q = 0 then some R.b else none).getD .race) := fun _ => rfl
  have h0 := hg.1
  have h1 := hg.2
  change word2 R q (strictStart R) g = .out1 at h0
  change word2 R q (strictStart R) (next R g) = .in0 at h1
  rw [hw] at h0 h1
  rw [h0] at h1
  cases h1

def strictRoundStart (R : RFrame) : Round R where
  idx := 1
  state := strictStart R
  base := ⟨strictStart_lineage R,fun _ => Nat.le_refl _,
    all_entered_debt_zero R 1 _ (fun _ => Nat.le_refl _),strictStart_no_success R⟩
  race := ⟨⟨0,by have := R.hm; omega⟩,rfl⟩

/-- The tight budget is attained by the rearmed all-Race round base. -/
theorem strictRoundStart_potential (R : RFrame) :
    (ghostRearmSpec R).restartPotential (.active (.round (strictRoundStart R))) =
      R.n*R.m*(2*R.h+1) := by
  have hw : word2 R 1 (strictStart R) = fun _ => .race := rfl
  change R.n * PeriodHIncidenceChoice.choiceRaceReserve (word2 R 1 (strictStart R)) +
    (R.n*R.m + R.n*R.m*(2*R.h-1)) = _
  rw [hw]
  have hr : PeriodHIncidenceChoice.choiceRaceReserve (fun _ : Fin R.m => .race) = R.m :=
    ShortGapChoiceStopping.choiceRaceReserve_allRace R.m
  rw [hr]
  have h := tightBudget_eq R
  omega

theorem strictStart_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (ghostRearmSpec R).restartStep
      (.active (.round (strictRoundStart R))) T ≤ R.n^T*(R.n*R.m*(2*R.h+1)) :=
  composed_truncatedCost_le R (strictRoundStart R) T

/-! ## Realization of a selected historical candidate -/

/-- A lock is a real, immutable historical out1/in0 pair in a lineage
state. Endpoint generations and physical receipts are derived below. -/
structure Locked10 (R : RFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m) : Prop where
  lineage : Lineage2 R s
  left : s.hist g q = some .out1
  right : s.hist (next R g) q = some .in0

def BothCandidate (R : RFrame) (s : GhostRing2 R) (g : Fin R.m) : Prop :=
  (s.cfg (rootV R g)).cwPort = some .heldCandidate ∧
    (s.cfg (rootV R (next R g))).ccwPort = some .heldCandidate

theorem candidate10_to_Locked10 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (g : Fin R.m) (hc : PeriodHIncidenceChoice.Candidate10 (ring R) (word2 R q s) g) :
    Locked10 R s q g := by
  refine ⟨hs,?_,?_⟩
  · have h := hc.1
    cases he : s.hist g q with
    | none => simp [word2,wordOf,curView,he,choiceToWord] at h
    | some c => cases c <;> simp_all [word2,wordOf,curView,choiceToWord]
  · have h := hc.2
    rw [ring_next] at h
    change word2 R q s (next R g) = .in0 at h
    cases he : s.hist (next R g) q with
    | none => simp [word2,wordOf,curView,he,choiceToWord] at h
    | some c => cases c <;> simp_all [word2,wordOf,curView,choiceToWord]

theorem Locked10.step {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) (e : Vtx R) : Locked10 R (ghostStep2 R s e) q g :=
  ⟨lineage2_step R s h.lineage e,history2_monotone R s e g q .out1 h.left,
    history2_monotone R s e (next R g) q .in0 h.right⟩

/-- Historical candidate endpoints cannot have completed this round:
either completion would supply a contradictory historical denial. -/
theorem Locked10.generations {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) : s.k g = q ∧ s.k (next R g) = q := by
  have noDenial : ¬ HistoricalDenial R (view R s) g q := by
    rintro ⟨c,d,hc,hd,hv⟩
    change s.hist g q = some c at hc
    change s.hist (next R g) q = some d at hd
    rw [h.left] at hc
    rw [h.right] at hd
    cases hc; cases hd; cases hv
  have hL : q ≤ s.k g := by
    by_cases hh : s.k g < q
    · have hn := h.lineage.coherent.histFuture g q hh
      change s.hist g q = none at hn
      rw [h.left] at hn; cases hn
    · omega
  have hR : q ≤ s.k (next R g) := by
    by_cases hh : s.k (next R g) < q
    · have hn := h.lineage.coherent.histFuture (next R g) q hh
      change s.hist (next R g) q = none at hn
      rw [h.right] at hn; cases hn
    · omega
  constructor
  · by_cases hh : q < s.k g
    · exact False.elim (noDenial (h.lineage.coherent.joinedDenials g q hh).2.2.1)
    · omega
  · by_cases hh : q < s.k (next R g)
    · have hd := (h.lineage.coherent.joinedDenials (next R g) q hh).2.2.2
      rw [prev_next] at hd
      exact False.elim (noDenial hd)
    · omega

theorem Locked10.no_join {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) (e : Vtx R) :
    fires R (physical2 R s) e g = false ∧ fires R (physical2 R s) e (next R g) = false := by
  have hb := h.generations
  have ha := (h.step e).generations
  have hl := ghostStep2_k R s e g
  have hr := ghostStep2_k R s e (next R g)
  constructor
  · cases hf : fires R (physical2 R s) e g with
    | false => rfl
    | true => simp only [hf,if_true] at hl; omega
  · cases hf : fires R (physical2 R s) e (next R g) with
    | false => rfl
    | true => simp only [hf,if_true] at hr; omega

/-- Both endpoint choices are the recorded locked values. -/
theorem Locked10.root_choices {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) :
    (∃ cw ccw, s.cfg (rootV R g) = .root .out1 cw ccw) ∧
    (∃ cw ccw, s.cfg (rootV R (next R g)) = .root .in0 cw ccw) := by
  have hk := h.generations
  constructor
  · obtain ⟨c,cw,ccw,hc⟩ := h.lineage.coherent.roots g
    have hh := h.lineage.coherent.histNow g c cw ccw hc
    change s.hist g (s.k g) = resolvedOpt c at hh
    rw [hk.1,h.left] at hh
    cases c <;> first | exact ⟨cw,ccw,hc⟩ | cases hh
  · obtain ⟨c,cw,ccw,hc⟩ := h.lineage.coherent.roots (next R g)
    have hh := h.lineage.coherent.histNow (next R g) c cw ccw hc
    change s.hist (next R g) (s.k (next R g)) = resolvedOpt c at hh
    rw [hk.2,h.right] at hh
    cases c <;> first | exact ⟨cw,ccw,hc⟩ | cases hh

/-- Before comparison the right port is free. After comparison the
returning/delivered locked result holds candidate, never denial. -/
theorem Locked10.right_port {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) :
    (s.cfg (rootV R (next R g))).ccwPort =
      if ComparedAt ((view R s).epoch g) q then some .heldCandidate else some .free := by
  classical
  by_cases hc : ComparedAt ((view R s).epoch g) q
  · rw [if_pos hc]
    obtain ⟨c,d,hl,hr,hv⟩ := h.lineage.coherent.incomingValue g (by
      change ComparedAt ((view R s).epoch g) (s.k (next R g))
      rw [h.generations.2]; exact hc)
    change s.hist g (s.k (next R g)) = some c at hl
    change s.hist (next R g) (s.k (next R g)) = some d at hr
    rw [h.generations.2,h.left] at hl
    rw [h.generations.2,h.right] at hr
    cases hl; cases hr
    exact hv
  · rw [if_neg hc]
    have hn : ¬ CcwHeld (s.cfg (rootV R (next R g))).ccwPort := by
      intro hh
      have hv := (h.lineage.coherent.incoming g).mp hh
      change ComparedAt ((view R s).epoch g) (s.k (next R g)) at hv
      rw [h.generations.2] at hv
      exact hc hv
    obtain ⟨cw,ccw,hr⟩ := h.root_choices.2
    rw [hr] at hn ⊢
    cases ccw with
    | free => rfl
    | heldDenial => exact False.elim (hn trivial)
    | heldCandidate => exact False.elim (hn trivial)

/-- The literal selected-gap debt includes prelaunch and is zero only
after the candidate reply has reached the owner. -/
def latchDebt (R : RFrame) (q : Nat) (g : Fin R.m) (s : GhostRing2 R) : Nat :=
  (tokens2 R (q+1) s g).hops

theorem latchDebt_start_le (R : RFrame) (q : Nat) (g : Fin R.m) (s : GhostRing2 R) :
    latchDebt R q g s ≤ 2*R.h-1 := ShortGapCohortCut.token_hops_le _

theorem Locked10.delivered_latches {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) (hd : DeliveredAt ((view R s).epoch g) q) : BothCandidate R s g := by
  have hc : ComparedAt ((view R s).epoch g) q := by
    cases he : (view R s).epoch g <;> simp only [he,DeliveredAt] at hd <;>
      simp only [ComparedAt] <;> omega
  constructor
  · obtain ⟨c,d,hl,hr,hv⟩ := h.lineage.coherent.outgoingValue g (by
      change DeliveredAt ((view R s).epoch g) (s.k g)
      rw [h.generations.1]; exact hd)
    change s.hist g (s.k g) = some c at hl
    change s.hist (next R g) (s.k g) = some d at hr
    rw [h.generations.1,h.left] at hl
    rw [h.generations.1,h.right] at hr
    cases hl; cases hr
    exact hv
  · classical
    simpa only [if_pos hc] using h.right_port

theorem latchDebt_positive (R : RFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (hn : ¬ BothCandidate R s g) : 0 < latchDebt R q g s := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact hn (h.delivered_latches (zero_token2_completed R q s h.lineage g hz))

private theorem sum_focus_cancel {n : Nat} (f g : Fin n → Nat) (i : Fin n)
    (ho : ∀ j, j ≠ i → f j = g j) :
    (List.ofFn f).sum + g i = (List.ofFn g).sum + f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht := ofFn_sum_eq (fun j : Fin n => f j.succ) (fun j => g j.succ)
        (fun j => ho j.succ (by intro h; have := congrArg Fin.val h; simp at this))
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      let j : Fin n := ⟨i.val-1,by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin n => f j.succ) (fun j => g j.succ) j (by
        intro k hk
        apply ho k.succ
        intro he
        rw [← hj] at he
        exact hk (Fin.succ_inj.mp he))
      have h0 := ho 0 (Ne.symm hi)
      rw [hj] at ht
      omega

/-- Other gaps' exact token stutter lets a total-debt row theorem yield
the selected latch's own one-hop decrease without a denial-only premise. -/
private theorem latch_drop_of_total (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (g : Fin R.m) (e : Vtx R) (hg : g = e.1)
    (hd : latentDebt2 R (q+1) (ghostStep2 R s e) + 1 = latentDebt2 R (q+1) s) :
    latchDebt R q g (ghostStep2 R s e) + 1 = latchDebt R q g s := by
  have hh := sum_focus_cancel
    (fun j => (tokens2 R (q+1) (ghostStep2 R s e) j).hops)
    (fun j => (tokens2 R (q+1) s j).hops) g (by
      intro j hj
      rw [ShortGapTwoEpochLaws.other_gap_token_eq_lineage R (q+1) s hs e j (by simpa only [← hg] using hj)])
  change latentDebt2 R (q+1) (ghostStep2 R s e) + latchDebt R q g s =
    latentDebt2 R (q+1) s + latchDebt R q g (ghostStep2 R s e) at hh
  omega

private theorem locked_right_free {R : RFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g)
    (hc : (s.epoch g).cur = .idle ∨ ∃ c, (s.epoch g).cur = .outbound q c) :
    (s.cfg (rootV R (next R g))).ccwPort = some .free := by
  classical
  have hn : ¬ ComparedAt ((view R s).epoch g) q := by
    rcases hc with hi | ⟨c,hc⟩
    · have hh := (idle_prefix R s h.lineage g hi).2 q
      rw [h.generations.1] at hh
      exact fun hn => Nat.lt_irrefl q (hh.mp hn)
    · simp [view,prefixView,combinedView,hc,ComparedAt]
  simpa only [if_neg hn] using h.right_port

/-- The selected locked comparison has a free receiver and no JOIN,
so replacing the declaration by its reply consumes exactly one hop. -/
private theorem latch_comparison_drop (R : RFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (p : Fin R.h) (hp : 0 < p.val) (hlast : p.val+1 = R.h)
    (c : Choice) (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .decl c else .empty)) :
    latchDebt R q g (ghostStep2 R s (g,p)) + 1 = latchDebt R q g s := by
  obtain ⟨cw,ccw,hr⟩ := h.root_choices.2
  have hf := locked_right_free h (Or.inr ⟨c,he⟩)
  rw [hr] at hf
  have hc : ccw = .free := Option.some.inj hf
  subst ccw
  have hl : s.cfg (g,p) = .interior (.decl c) := by simpa using hslots p hp
  have hx := boundary_comparison R s h.lineage g p hp hlast c .in0 cw hl hr
  have hrn : rn R (g,p) = rootV R (next R g) := rn_of_last R (g,p) (by change ¬ p.val+1 < R.h; omega)
  have hpost := ShortGapTwoEpochLaws.boundary_token_replace R s g p hp hlast
    (.decl c) (.reply .in0) hslots (by rw [hrn,hl,hr]; rfl)
  have hp0 := tokenPos2_of_unique R s g p hp (.decl c) (by intro h; cases h) hslots
  have hp1 := tokenPos2_of_unique R (ghostStep2 R s (g,p)) g p hp (.reply .in0)
    (by intro h; cases h) hpost
  have hk0 : (curView R s).k g = q := h.generations.1
  have hk1 : (curView R (ghostStep2 R s (g,p))).k g = q := (h.step (g,p)).generations.1
  have he0 : (curView R s).epoch g = .outbound q c := he
  have he1 : (curView R (ghostStep2 R s (g,p))).epoch g = .returning q c .in0 := by
    simpa [curView,h.generations.1,resolveResp] using hx.1
  simp [latchDebt,tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hp0,hp1,ofPhase,p.isLt,
    (by omega : 1 ≤ p.val),(by omega : p.val ≤ R.h-1),LitGapState.hops]
  omega

/-- Every literal edge is nonincreasing for the selected locked gap.
This uses local row laws, not the denial-only accounting domain. -/
theorem latchDebt_step_le (R : RFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (e : Vtx R) :
    latchDebt R q g (ghostStep2 R s e) ≤ latchDebt R q g s := by
  by_cases hg : g = e.1
  · rcases e with ⟨j,a⟩
    change g = j at hg
    subst j
    have hk := h.generations.1
    have ht := h.lineage.current g
    have hshape := current_token_shape R s h.lineage g
    cases he : (s.epoch g).cur with
    | idle => exact idle_gap_token_debt_le R (q+1) s (g,a) g he
    | delivered t c d =>
      unfold latchDebt
      rw [ShortGapTwoEpochLaws.delivered_selected_token_eq R (q+1) s h.lineage (g,a) t c d he]
      exact Nat.le_refl _
    | outbound t c =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .decl c else .empty) at hslots
      by_cases hap : a = p
      · subst a
        by_cases hn : p.val+1 < R.h
        · have hd := latch_drop_of_total R s h.lineage q g (g,p) rfl
            (ShortGapTwoEpochLaws.forwarding_lowers_latentDebt2 R q s h.lineage g c p hp hn hk he hslots)
          omega
        · have hlast : p.val+1 = R.h := by have := p.isLt; omega
          have hd := latch_comparison_drop R s q g h p hp hlast c he hslots
          omega
      · unfold latchDebt
        rw [ShortGapTwoEpochLaws.outbound_wrong_edge R (q+1) s h.lineage g a p q c hp hap he hslots]
        exact Nat.le_refl _
    | returning t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .reply d else .empty) at hslots
      by_cases hap : a.val+1 = p.val
      · by_cases hp1 : p.val = 1
        · have ha : (g,a) = rootV R g := Prod.ext rfl (Fin.ext (by change a.val = 0; omega))
          rw [ha]
          have hd := latch_drop_of_total R s h.lineage q g (rootV R g) rfl
            (ShortGapTwoEpochLaws.delivery_lowers_latentDebt2 R q s h.lineage g c d p hp1 hk he hslots)
          omega
        · have hp2 : 1 < p.val := by omega
          let p' : Fin R.h := ⟨p.val-1,by have := p.isLt; omega⟩
          have hd := latch_drop_of_total R s h.lineage q g (g,p') rfl
            (ShortGapTwoEpochLaws.backward_lowers_latentDebt2 R q s h.lineage g c d p hp2 hk he hslots)
          have ha : a = p' := Fin.ext (by change a.val = p.val-1; omega)
          rw [ha]
          omega
      · unfold latchDebt
        rw [ShortGapTwoEpochLaws.returning_wrong_edge R (q+1) s h.lineage g a p q c d hp hap he hslots]
        exact Nat.le_refl _
  · unfold latchDebt
    rw [ShortGapTwoEpochLaws.other_gap_token_eq_lineage R (q+1) s h.lineage e g hg]
    exact Nat.le_refl _

private theorem latch_launch_drop (R : RFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (hi : (s.epoch g).cur = .idle) :
    latchDebt R q g (ghostStep2 R s (rootV R g)) + 1 = latchDebt R q g s := by
  obtain ⟨cw,ccw,hroot⟩ := h.root_choices.1
  have hs := h.lineage.idleSend g hi
  rw [hroot] at hs
  have hc : cw = .toSend := Option.some.inj hs
  subst cw
  by_cases hh : 1 < R.h
  · exact ShortGapTwoEpochLaws.prelaunch_token_debt_drop R q s h.lineage g .out1 ccw hroot hh h.generations.1 hi
  · have h1 : R.h = 1 := by have := R.hh; omega
    obtain ⟨dw,dd,hr⟩ := h.root_choices.2
    have hf := locked_right_free h (Or.inl hi)
    rw [hr] at hf
    have hd : dd = .free := Option.some.inj hf
    subst dd
    have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬ 0+1 < R.h; omega)
    have hraw : rawEpochs R (curView R s) (rootV R g) g = .delivered q .out1 .in0 := by
      rw [rawEpochs,if_pos rfl]
      change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
      rw [hroot,hrn,hr,h.generations.1]; rfl
    have hz := ShortGapTwoEpochLaws.token_zero_of_raw_delivered R q s (rootV R g) g .out1 .in0 h.generations.1 hraw
    have hk0 : (curView R s).k g = q := h.generations.1
    have he0 : (curView R s).epoch g = .idle := hi
    change (tokens2 R (q+1) (ghostStep2 R s (rootV R g)) g).hops + 1 = _
    rw [hz]
    simp [latchDebt,tokens2,tokensOf',cohortToken,hk0,he0,h1,LitGapState.hops]

/-- One designated physical edge advances every nonzero selected debt. -/
theorem latchDebt_advancing_edge (R : RFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (hp : 0 < latchDebt R q g s) :
    ∃ e : Fin R.n, latchDebt R q g (ghostStep2 R s (edgeVtx R e)) + 1 = latchDebt R q g s := by
  have hk := h.generations.1
  have ht := h.lineage.current g
  have hshape := current_token_shape R s h.lineage g
  have hex : ∃ e : Vtx R, latchDebt R q g (ghostStep2 R s e) + 1 = latchDebt R q g s := by
    cases he : (s.epoch g).cur with
    | idle => exact ⟨rootV R g,latch_launch_drop R s q g h he⟩
    | delivered t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      have hk0 : (curView R s).k g = q := hk
      have he0 : (curView R s).epoch g = .delivered q c d := hq ▸ he
      simp [latchDebt,tokens2,tokensOf',cohortToken,hk0,he0,LitGapState.hops] at hp
    | outbound t c =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .decl c else .empty) at hslots
      by_cases hn : p.val+1 < R.h
      · exact ⟨(g,p),latch_drop_of_total R s h.lineage q g (g,p) rfl
          (ShortGapTwoEpochLaws.forwarding_lowers_latentDebt2 R q s h.lineage g c p hp hn hk he hslots)⟩
      · exact ⟨(g,p),latch_comparison_drop R s q g h p hp (by have := p.isLt; omega) c he hslots⟩
    | returning t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .reply d else .empty) at hslots
      by_cases hp1 : p.val = 1
      · exact ⟨rootV R g,latch_drop_of_total R s h.lineage q g (rootV R g) rfl
          (ShortGapTwoEpochLaws.delivery_lowers_latentDebt2 R q s h.lineage g c d p hp1 hk he hslots)⟩
      · let p' : Fin R.h := ⟨p.val-1,by have := p.isLt; omega⟩
        exact ⟨(g,p'),latch_drop_of_total R s h.lineage q g (g,p') rfl
          (ShortGapTwoEpochLaws.backward_lowers_latentDebt2 R q s h.lineage g c d p (by omega) hk he hslots)⟩
  obtain ⟨e,he⟩ := hex
  exact ⟨encE R e.1 e.2,by rw [edgeVtx_encE]; exact he⟩

structure RealizeCore (R : RFrame) where
  idx : Nat
  gap : Fin R.m
  state : GhostRing2 R

def RealizeInv (R : RFrame) (x : RealizeCore R) : Prop :=
  Locked10 R x.state x.idx x.gap ∧ ¬ BothCandidate R x.state x.gap

abbrev RealizeState (R : RFrame) := {x : RealizeCore R // RealizeInv R x}

noncomputable def realizeStep (R : RFrame) (s : RealizeState R) (e : Fin R.n) : StopNode (RealizeState R) := by
  classical
  let t := ghostStep2 R s.val.state (edgeVtx R e)
  exact if ht : BothCandidate R t s.val.gap then .success
    else .active ⟨⟨s.val.idx,s.val.gap,t⟩,s.property.1.step _,ht⟩

def realizePotential (R : RFrame) : StopNode (RealizeState R) → Nat
  | .active s => R.n * latchDebt R s.val.idx s.val.gap s.val.state
  | .success | .failure => 0

theorem realize_bellman (R : RFrame) : NatBellmanSuperSolution (realizeStep R) 1 (realizePotential R) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  have hle := latchDebt_step_le R s.val.state s.val.idx s.val.gap s.property.1
  obtain ⟨e,he⟩ := latchDebt_advancing_edge R s.val.state s.val.idx s.val.gap s.property.1
    (latchDebt_positive R s.val.state s.val.idx s.val.gap s.property.1 s.property.2)
  have ht := sum_strict (fun a => latchDebt R s.val.idx s.val.gap (ghostStep2 R s.val.state (edgeVtx R a)))
    (fun _ => latchDebt R s.val.idx s.val.gap s.val.state) e (fun a => hle _) (by omega)
  rw [ofFn_sum_const] at ht
  have hsum : (List.ofFn (fun a : Fin R.n => realizePotential R (realizeStep R s a))).sum ≤
      (List.ofFn (fun a : Fin R.n => R.n*latchDebt R s.val.idx s.val.gap
        (ghostStep2 R s.val.state (edgeVtx R a)))).sum := by
    apply ofFn_sum_le
    intro a
    unfold realizeStep
    dsimp only
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  rw [ofFn_sum_mul_left] at hsum
  have hb : 1 + (List.ofFn (fun a : Fin R.n =>
      latchDebt R s.val.idx s.val.gap (ghostStep2 R s.val.state (edgeVtx R a)))).sum ≤
      R.n*latchDebt R s.val.idx s.val.gap s.val.state := by omega
  have hm := Nat.mul_le_mul_left R.n hb
  rw [Nat.mul_add,Nat.mul_one] at hm
  change 1*R.n + _ ≤ R.n*(R.n*_)
  rw [Nat.one_mul]
  omega

theorem switch_potential_le (R : RFrame) (s : RealizeState R) (credit : Nat) :
    realizePotential R (.active s) ≤ credit + R.n*(2*R.h-1) := by
  have h := Nat.mul_le_mul_left R.n (latchDebt_start_le R s.val.idx s.val.gap s.val.state)
  change R.n*latchDebt R s.val.idx s.val.gap s.val.state ≤ _
  omega

/-- Scan a fixed finite list in order, using only immutable payloads. -/
def findLockedPairs (R : RFrame) (s : GhostRing2 R) : List (Nat × Fin R.m) → Option (Nat × Fin R.m)
  | [] => none
  | p :: ps => if s.hist p.2 p.1 = some .out1 ∧ s.hist (next R p.2) p.1 = some .in0
      then some p else findLockedPairs R s ps

def lockedPairs (R : RFrame) (s : GhostRing2 R) : List (Nat × Fin R.m) :=
  (List.range (maxGen R s+1)).flatMap (fun q => (List.finRange R.m).map (fun g => (q,g)))

/-- Deterministic lexicographic search: generation first, gap second. -/
def firstLocked10 (R : RFrame) (s : GhostRing2 R) : Option (Nat × Fin R.m) :=
  findLockedPairs R s (lockedPairs R s)

private theorem findLockedPairs_sound (R : RFrame) (s : GhostRing2 R) (xs : List (Nat × Fin R.m))
    (p : Nat × Fin R.m) (h : findLockedPairs R s xs = some p) :
    s.hist p.2 p.1 = some .out1 ∧ s.hist (next R p.2) p.1 = some .in0 := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rw [findLockedPairs] at h
    split at h
    · rename_i ha
      cases h
      exact ha
    · exact ih h

private theorem findLockedPairs_complete (R : RFrame) (s : GhostRing2 R) (xs : List (Nat × Fin R.m))
    (h : ∃ p, p ∈ xs ∧ s.hist p.2 p.1 = some .out1 ∧ s.hist (next R p.2) p.1 = some .in0) :
    ∃ p, findLockedPairs R s xs = some p := by
  induction xs with
  | nil => obtain ⟨p,hp,_⟩ := h; cases hp
  | cons a xs ih =>
    rw [findLockedPairs]
    split
    · exact ⟨a,rfl⟩
    · rename_i hn
      apply ih
      obtain ⟨p,hp,hp'⟩ := h
      rcases List.mem_cons.mp hp with he | he
      · subst p; exact False.elim (hn hp')
      · exact ⟨p,he,hp'⟩

theorem firstLocked10_sound (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (g : Fin R.m) (h : firstLocked10 R s = some (q,g)) : Locked10 R s q g :=
  ⟨hs,(findLockedPairs_sound R s (lockedPairs R s) (q,g) h).1,
    (findLockedPairs_sound R s (lockedPairs R s) (q,g) h).2⟩

theorem firstLocked10_complete (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) : ∃ p, firstLocked10 R s = some p := by
  obtain ⟨q,hq,g,hg⟩ := hv
  have hc : PeriodHIncidenceChoice.Candidate10 (ring R) (word2 R q s) g := hg
  have hl := candidate10_to_Locked10 R s hs q g hc
  apply findLockedPairs_complete
  refine ⟨(q,g),?_,hl.left,hl.right⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨g,List.mem_finRange g,rfl⟩

theorem realizeStep_success_iff (R : RFrame) (s : RealizeState R) (e : Fin R.n) :
    realizeStep R s e = .success ↔ BothCandidate R (ghostStep2 R s.val.state (edgeVtx R e)) s.val.gap := by
  classical
  unfold realizeStep
  dsimp only
  split <;> simp_all

/-- Select a lock after actual virtual success. The impossible none
branch is eliminated by finite-search completeness, never reseeded. -/
noncomputable def switchToRealize (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) : StopNode (RealizeState R) := by
  classical
  exact match he : firstLocked10 R s with
    | none => False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rw [he] at hp; cases hp)
    | some (q,g) => if hb : BothCandidate R s g then .success
      else .active ⟨⟨q,g,s⟩,firstLocked10_sound R s hs q g he,hb⟩

theorem switchToRealize_le (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) :
    realizePotential R (switchToRealize R s hs hv) ≤ R.n*(2*R.h-1) := by
  classical
  unfold switchToRealize
  split
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul_left R.n (latchDebt_start_le R _ _ s)

abbrev AccountState (R : RFrame) := (ghostRearmSpec R).RestartState

def accountGhost (R : RFrame) : AccountState R → GhostRing2 R
  | .round s => s.state
  | .reset s => s.state

theorem account_lineage (R : RFrame) (s : AccountState R) : Lineage2 R (accountGhost R s) := by
  cases s with
  | round s => exact s.base.lineage
  | reset s => exact s.dom.lineage

theorem serviceStep_success_iff (R : RFrame) (s : Service R) (e : Fin R.n) :
    serviceStep R s e = .succeed ↔ VirtualSuccess R 0 (ghostStep2 R s.state (edgeVtx R e)) := by
  classical
  change serviceStep R s e = .succeed ↔ VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e))
  unfold serviceStep
  dsimp only
  split <;> simp_all
  split <;> simp_all

theorem account_success_iff (R : RFrame) (s : AccountState R) (e : Fin R.n) :
    (ghostRearmSpec R).restartStep s e = .success ↔
      VirtualSuccess R 0 (ghostStep2 R (accountGhost R s) (edgeVtx R e)) := by
  cases s with
  | round s =>
    have hh := roundStep_success_iff R s e
    change BalancedFailureRestart.liftRoundOutcome (serviceEntry R s e) (roundStep R s e) = .success ↔ _
    cases he : roundStep R s e <;> simpa only [he,BalancedFailureRestart.liftRoundOutcome,reduceCtorEq,accountGhost,VirtualSuccess] using hh
  | reset s =>
    have hh := serviceStep_success_iff R s e
    change liftServiceOutcome (serviceStep R s e) = .success ↔ _
    cases he : serviceStep R s e <;> simpa only [he,liftServiceOutcome,reduceCtorEq,accountGhost,VirtualSuccess] using hh

inductive CandidateRunState (R : RFrame) where
  | account : AccountState R → CandidateRunState R
  | realize : RealizeState R → CandidateRunState R

def candidateGhost (R : RFrame) : CandidateRunState R → GhostRing2 R
  | .account s => accountGhost R s
  | .realize s => s.val.state

def embedRealize (R : RFrame) : StopNode (RealizeState R) → StopNode (CandidateRunState R)
  | .active s => .active (.realize s)
  | .success => .success
  | .failure => .failure

/-- The account virtual-success port switches to a selected lock in its
actual ghost child. No extra physical interaction is charged for the
mode switch, and success is exposed only after both candidate latches. -/
noncomputable def physicalCandidateStep (R : RFrame) (s : CandidateRunState R) (e : Fin R.n) :
    StopNode (CandidateRunState R) := by
  classical
  exact match s with
    | .realize x => embedRealize R (realizeStep R x e)
    | .account x => match he : (ghostRearmSpec R).restartStep x e with
      | .active y => .active (.account y)
      | .failure => False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
      | .success => embedRealize R (switchToRealize R (ghostStep2 R (accountGhost R x) (edgeVtx R e))
        (lineage2_step R _ (account_lineage R x) _) ((account_success_iff R x e).mp he))

/-- Every account state retains one full latch budget, while realize
states charge only the selected physical gap's remaining hops. -/
noncomputable def physicalCandidatePotential (R : RFrame) : StopNode (CandidateRunState R) → Nat
  | .active (.account s) => (ghostRearmSpec R).restartPotential (.active s) + R.n*(2*R.h-1)
  | .active (.realize s) => realizePotential R (.active s)
  | .success | .failure => 0

theorem embedRealize_potential (R : RFrame) (x : StopNode (RealizeState R)) :
    physicalCandidatePotential R (embedRealize R x) = realizePotential R x := by cases x <;> rfl

/-- The reserved latch credit pays every switched success child. All
other account children retain that credit, so the uniform Bellman sum
is bounded by the accounting sum plus n times the latch budget. -/
theorem physicalCandidate_bellman (R : RFrame) :
    NatBellmanSuperSolution (physicalCandidateStep R) 1 (physicalCandidatePotential R) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  cases s with
  | realize x =>
    have h := (realize_bellman R).2.2 x
    change 1*R.n + (List.ofFn (fun e => physicalCandidatePotential R (embedRealize R (realizeStep R x e)))).sum ≤
      R.n * realizePotential R (.active x)
    simpa only [embedRealize_potential] using h
  | account x =>
    have h := (ghostRearm_bellman R).2.2 x
    have hpoint : ∀ e : Fin R.n, physicalCandidatePotential R (physicalCandidateStep R (.account x) e) ≤
        (ghostRearmSpec R).restartPotential ((ghostRearmSpec R).restartStep x e) + R.n*(2*R.h-1) := by
      intro e
      unfold physicalCandidateStep
      dsimp only
      split
      · rename_i y he
        rw [he]
        exact Nat.le_refl _
      · rename_i he
        exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
      · rw [embedRealize_potential]
        exact Nat.le_trans (switchToRealize_le R _ _ _) (Nat.le_add_left _ _)
    have hsum := ofFn_sum_le _ _ hpoint
    rw [ofFn_sum_add,ofFn_sum_const] at hsum
    change 1*R.n + _ ≤ R.n*((ghostRearmSpec R).restartPotential (.active x)+R.n*(2*R.h-1))
    rw [Nat.mul_add]
    omega

theorem switchToRealize_no_failure (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) : switchToRealize R s hs hv ≠ .failure := by
  classical
  unfold switchToRealize
  split
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split <;> intro h <;> cases h

theorem embedRealize_no_failure (R : RFrame) (x : StopNode (RealizeState R)) (hx : x ≠ .failure) :
    embedRealize R x ≠ .failure := by
  cases x with
  | active x => intro h; cases h
  | success => intro h; cases h
  | failure => exact False.elim (hx rfl)

theorem physicalCandidate_no_failure (R : RFrame) (s : CandidateRunState R) (e : Fin R.n) :
    physicalCandidateStep R s e ≠ .failure := by
  classical
  cases s with
  | realize x =>
    apply embedRealize_no_failure
    unfold realizeStep
    dsimp only
    split <;> intro h <;> cases h
  | account x =>
    unfold physicalCandidateStep
    dsimp only
    split
    · intro h; cases h
    · rename_i he
      exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
    · exact embedRealize_no_failure R _ (switchToRealize_no_failure R _ _ _)

theorem switchToRealize_success_sound (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) (h : switchToRealize R s hs hv = .success) : ∃ g, BothCandidate R s g := by
  classical
  unfold switchToRealize at h
  split at h
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split at h
    · rename_i q g he hb
      exact ⟨g,hb⟩
    · cases h

theorem physicalCandidate_success_sound (R : RFrame) (s : CandidateRunState R) (e : Fin R.n)
    (h : physicalCandidateStep R s e = .success) :
    ∃ g, BothCandidate R (ghostStep2 R (candidateGhost R s) (edgeVtx R e)) g := by
  classical
  have hemb : ∀ x : StopNode (RealizeState R), embedRealize R x = .success → x = .success := by
    intro x hx; cases x <;> first | rfl | cases hx
  cases s with
  | realize x =>
    exact ⟨x.val.gap,(realizeStep_success_iff R x e).mp (hemb _ h)⟩
  | account x =>
    unfold physicalCandidateStep at h
    dsimp only at h
    split at h
    · cases h
    · rename_i he
      exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
    ·
      exact switchToRealize_success_sound R _ _ _ (hemb _ h)

def physicalCandidateStart (R : RFrame) : CandidateRunState R := .account (.round (strictRoundStart R))
def physicalCandidateCleanStart (R : RFrame) : CandidateRunState R := .account (.reset (initialService R))

/-- Erasing the accounting mode yields exactly one literal interaction,
including the failure-to-service transition. -/
theorem account_step_erases (R : RFrame) (s t : AccountState R) (e : Fin R.n)
    (h : (ghostRearmSpec R).restartStep s e = .active t) :
    accountGhost R t = ghostStep2 R (accountGhost R s) (edgeVtx R e) := by
  classical
  cases s with
  | round s =>
    change BalancedFailureRestart.liftRoundOutcome (serviceEntry R s e) (roundStep R s e) = .active t at h
    cases he : roundStep R s e with
    | active y =>
      simp only [he,BalancedFailureRestart.liftRoundOutcome] at h
      cases h
      unfold roundStep at he
      dsimp only at he
      split at he
      · cases he
      · split at he
        · cases he; rfl
        · cases he
    | failure =>
      simp only [he,BalancedFailureRestart.liftRoundOutcome] at h
      cases h
      exact (serviceEntry_of_failure R s e he).2
    | success =>
      simp only [he,BalancedFailureRestart.liftRoundOutcome] at h
      cases h
  | reset s =>
    change liftServiceOutcome (serviceStep R s e) = .active t at h
    unfold serviceStep at h
    dsimp only at h
    split at h
    · cases h
    · split at h <;> cases h <;> rfl

theorem switchToRealize_active_state (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) (x : RealizeState R) (h : switchToRealize R s hs hv = .active x) :
    x.val.state = s := by
  classical
  unfold switchToRealize at h
  split at h
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split at h
    · cases h
    · cases h; rfl

theorem embedRealize_active_state (R : RFrame) (x : StopNode (RealizeState R))
    (y : CandidateRunState R) (h : embedRealize R x = .active y) :
    ∃ z, x = .active z ∧ y = .realize z := by
  cases x with
  | active z => cases h; exact ⟨z,rfl,rfl⟩
  | success => cases h
  | failure => cases h

/-- Neither entering service nor switching to realization inserts a
synthetic state update or an extra interaction. -/
theorem physicalCandidate_step_erases (R : RFrame) (s t : CandidateRunState R) (e : Fin R.n)
    (h : physicalCandidateStep R s e = .active t) :
    candidateGhost R t = ghostStep2 R (candidateGhost R s) (edgeVtx R e) := by
  classical
  cases s with
  | realize x =>
    obtain ⟨z,hz,rfl⟩ := embedRealize_active_state R _ _ h
    unfold realizeStep at hz
    dsimp only at hz
    split at hz
    · cases hz
    · cases hz; rfl
  | account x =>
    unfold physicalCandidateStep at h
    dsimp only at h
    split at h
    · rename_i y he
      cases h
      exact account_step_erases R x y e he
    · rename_i he
      exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
    · obtain ⟨z,hz,rfl⟩ := embedRealize_active_state R _ _ h
      exact switchToRealize_active_state R _ _ _ z hz

theorem physicalCandidate_start_le (R : RFrame) :
    physicalCandidatePotential R (.active (physicalCandidateStart R)) ≤
      R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1) := by
  change (ghostRearmSpec R).restartPotential (.active (.round (strictRoundStart R))) + _ ≤ _
  rw [strictRoundStart_potential]
  exact Nat.le_refl _

theorem physicalCandidate_cleanStart_le (R : RFrame) :
    physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) ≤
      4*R.n*R.m*R.h+R.n*(2*R.h-1) := by
  change (ghostRearmSpec R).restartPotential (.active (.reset (initialService R))) + _ ≤ _
  rw [initialService_potential]
  exact Nat.le_refl _

theorem physicalCandidate_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateStart R)) T ≤
      R.n^T*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (physicalCandidateStart R)) T
  simp only [Nat.one_mul] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (physicalCandidate_start_le R))

theorem physicalCandidate_clean_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.m*R.h+R.n*(2*R.h-1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (physicalCandidateCleanStart R)) T
  simp only [Nat.one_mul] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (physicalCandidate_cleanStart_le R))

theorem physicalCandidate_success_one_minus_inv_factor (R : RFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateStart R))
        (factor*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) := by
  apply success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) _
    (physicalCandidate_truncatedCost_le R) factor
  have h : 0 < R.n*R.m*(2*R.h+1) := Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (by have := R.hm; omega) R.hh) (by have := R.hm; omega)) (by omega)
  omega

theorem physicalCandidate_clean_success_one_minus_inv_factor (R : RFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.m*R.h+R.n*(2*R.h-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.m*R.h+R.n*(2*R.h-1))) := by
  apply success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) _
    (physicalCandidate_clean_truncatedCost_le R) factor
  have h : 0 < 4*R.n*R.m*R.h := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
    (Nat.mul_pos (by have := R.hm; omega) R.hh)) (by have := R.hm; omega)) R.hh
  omega

#print axioms debt0_all_entered
#print axioms round_bellman
#print axioms round_balance
#print axioms service_exit
#print axioms service_bellman
#print axioms ghostRearm_bellman
#print axioms composed_truncatedCost_le
#print axioms composed_success_one_minus_inv_factor
#print axioms strictStart_lineage
#print axioms strictRoundStart_potential
#print axioms cleanStart_not_active_round
#print axioms cleanStart_truncatedCost_le
#print axioms firstLocked10_sound
#print axioms firstLocked10_complete
#print axioms latchDebt_step_le
#print axioms latchDebt_advancing_edge
#print axioms realize_bellman
#print axioms switch_potential_le
#print axioms physicalCandidate_bellman
#print axioms physicalCandidate_step_erases
#print axioms physicalCandidate_success_sound
#print axioms physicalCandidate_no_failure
#print axioms physicalCandidate_truncatedCost_le
#print axioms physicalCandidate_success_one_minus_inv_factor
#print axioms physicalCandidate_clean_truncatedCost_le
#print axioms physicalCandidate_clean_success_one_minus_inv_factor

end ShortGapGhostComposition2
