import Leader.Wu.Elimination.SinkTwoGapEpochKernel

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapServiceRank LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs LDSinkTwoGapEpochCost LDSinkTwoGapEpochLaws
  LDSinkTwoGapEpochKernel PPLLRepair FiniteUniformStoppingTree
open Classical

namespace LDSinkTwoGapNoResetKernel

set_option autoImplicit false

noncomputable section

variable {n ψ : Nat}

inductive APhase where
  | transit
  | parked
  deriving DecidableEq

/-- No reset phase and no stored credit. -/
structure AState (n ψ : Nat) where
  conf : Fin n → AgentState ψ
  phase : APhase

/-- The union covers the recovery endpoints and the attack endpoints. -/
def NoResetSuccess (F : TwoGapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  EndpointDeleted F.attack C ∨ EndpointDeleted F.recovery C

/-- Supply the frame's common-j identity explicitly.
The three positions are i = recovery.pos 0, j = attack.pos 0,
and k = attack.pos attack.d. -/
theorem success2_covers_three (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ)
    (hshared : F.recovery.pos F.recovery.d = F.attack.pos 0) :
    NoResetSuccess F C ↔
      (C (F.recovery.pos 0)).leader = false ∨
      (C (F.attack.pos 0)).leader = false ∨
      (C (F.attack.pos F.attack.d)).leader = false := by
  unfold NoResetSuccess EndpointDeleted
  rw [hshared]
  constructor
  · intro h
    rcases h with (hj | hk) | (hi | hj)
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr hk)
    · exact Or.inl hi
    · exact Or.inr (Or.inl hj)
  · intro h
    rcases h with hi | hj | hk
    · exact Or.inr (Or.inl hi)
    · exact Or.inl (Or.inl hj)
    · exact Or.inl (Or.inr hk)

/-- Forget the restricted phase alphabet, without changing configuration. -/
def asEpoch (F : TwoGapFrame n) (x : AState n ψ) : EpochState n ψ F :=
  { conf := x.conf
    phase := match x.phase with
      | .transit => .transit
      | .parked => .parked }

def attemptStepConf (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) : Fin n → AgentState ψ :=
  epochStepConf hψ F (asEpoch F x) e

/-- Stronger than the old phase-indexed projection: no RoundActive premise
is needed, and the attack gap is selected in both new phases. -/
theorem attemptStepConf_eq_sinkStepC (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    attemptStepConf hψ F x e = sinkStepC hψ F.attack x.conf e := by
  rfl

/-- Absorption is an event on the victim edge, not merely an empty post-state.
The imported AbsorbedAt checks a pre-state live bullet and a post-state
shielded, surviving victim. Its post-state check includes same-step re-shielding.
The fresh-shot invariant below identifies that parked bullet with the tag. -/
def NoResetAbsorbedAt (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (Cpost : Fin n → AgentState ψ) : Prop :=
  x.phase = .parked ∧ e = F.attack.pos 0 ∧
    AbsorbedAt F x.conf Cpost

def advanceAPhase (F : TwoGapFrame n) (p : APhase)
    (C : Fin n → AgentState ψ) : APhase :=
  match p with
  | .transit =>
      if (C (F.attack.pos 1)).bullet = (2 : Fin 3) then .parked else .transit
  | .parked => .parked

def advanceAState (F : TwoGapFrame n) (x : AState n ψ)
    (C : Fin n → AgentState ψ) : AState n ψ :=
  { conf := C, phase := advanceAPhase F x.phase C }

/-- The actual physical classifier. Success has priority over absorption.
The post-configuration remains available through attemptStepConf for a later
outer recovery implementation; StopNode.failure itself carries no payload. -/
def attemptStepRaw (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) : StopNode (AState n ψ) := by
  classical
  exact
    let C' := attemptStepConf hψ F x e
    if NoResetSuccess F C' then .success
    else if NoResetAbsorbedAt F x e C' then .failure
    else .active (advanceAState F x C')

theorem attemptStepRaw_failure_iff (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    attemptStepRaw hψ F x e = .failure ↔
      ¬ NoResetSuccess F (attemptStepConf hψ F x e) ∧
      NoResetAbsorbedAt F x e (attemptStepConf hψ F x e) := by
  classical
  unfold attemptStepRaw
  dsimp only
  by_cases hs : NoResetSuccess F (attemptStepConf hψ F x e) <;>
    by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e) <;>
    simp [hs, ha]

theorem attemptStepRaw_active_data (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (h : attemptStepRaw hψ F x e = .active y) :
    ¬ NoResetSuccess F (attemptStepConf hψ F x e) ∧
    ¬ NoResetAbsorbedAt F x e (attemptStepConf hψ F x e) ∧
    y = advanceAState F x (attemptStepConf hψ F x e) := by
  classical
  unfold attemptStepRaw at h
  dsimp only at h
  by_cases hs : NoResetSuccess F (attemptStepConf hψ F x e)
  · rw [if_pos hs] at h
    cases h
  · rw [if_neg hs] at h
    by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e)
    · rw [if_pos ha] at h
      cases h
    · rw [if_neg ha] at h
      exact ⟨hs, ha, (StopNode.active.inj h).symm⟩

theorem attemptStepRaw_active_conf (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (h : attemptStepRaw hψ F x e = .active y) :
    y.conf = sinkStepC hψ F.attack x.conf e := by
  rw [(attemptStepRaw_active_data hψ F x e y h).2.2]
  rfl

/-! Rank arithmetic. Both phases read W on the attack gap. -/

def H (F : TwoGapFrame n) : Nat :=
  4 * (F.recovery.d + F.attack.d) + 2

def phaseDebtA (F : TwoGapFrame n) (p : APhase) : Nat :=
  if p = .transit then H F else 0

def W (F : TwoGapFrame n) (C : Fin n → AgentState ψ) : Nat :=
  LDSinkGapServiceRank.gapWC F.attack C

def R (F : TwoGapFrame n) (x : AState n ψ) : Nat :=
  1 + phaseDebtA F x.phase + W F x.conf

theorem R_pos (F : TwoGapFrame n) (x : AState n ψ) : 0 < R F x := by
  unfold R
  omega

theorem R_le (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (_hrec : GapInvariant hψ F.recovery x.conf)
    (hatt : GapInvariant hψ F.attack x.conf) :
    R F x ≤ 16 * (F.recovery.d + F.attack.d) := by
  have hw : W F x.conf ≤ 2 * F.attack.d :=
    LDSinkGapServiceRank.gapWC_le_two_d hψ F.attack x.conf hatt
  have ha := F.recovery.hd
  have hb := F.attack.hd
  cases hp : x.phase <;> simp [R, phaseDebtA, H, hp] <;> omega

theorem phaseDebtA_advance_le (F : TwoGapFrame n) (p : APhase)
    (C : Fin n → AgentState ψ) :
    phaseDebtA F (advanceAPhase F p C) ≤ phaseDebtA F p := by
  cases p with
  | parked => simp [advanceAPhase, phaseDebtA]
  | transit =>
      by_cases hb : (C (F.attack.pos 1)).bullet = (2 : Fin 3)
      · simp [advanceAPhase, phaseDebtA, hb]
      · simp [advanceAPhase, phaseDebtA, hb]

theorem R_advance_le (F : TwoGapFrame n) (x : AState n ψ)
    (C : Fin n → AgentState ψ) (hw : W F C ≤ W F x.conf) :
    R F (advanceAState F x C) ≤ R F x := by
  have hp := phaseDebtA_advance_le F x.phase C
  change 1 + phaseDebtA F (advanceAPhase F x.phase C) + W F C ≤
    1 + phaseDebtA F x.phase + W F x.conf
  omega

theorem R_advance_lt (F : TwoGapFrame n) (x : AState n ψ)
    (C : Fin n → AgentState ψ) (hw : W F C < W F x.conf) :
    R F (advanceAState F x C) < R F x := by
  have hp := phaseDebtA_advance_le F x.phase C
  change 1 + phaseDebtA F (advanceAPhase F x.phase C) + W F C <
    1 + phaseDebtA F x.phase + W F x.conf
  omega

def rawStoppedR (F : TwoGapFrame n) : StopNode (AState n ψ) → Nat
  | .active x => R F x
  | .success => 0
  | .failure => 0

/-! Explicit fresh-shot domain, not an assertion about all configurations. -/

/-- There is exactly one nonzero bullet in positions 1,...,d, and it is live.
An entrance theorem must establish that it is the fresh k-shot. -/
def UniqueLiveShot (F : TwoGapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  ∃ t : Nat, 0 < t ∧ t ≤ F.attack.d ∧
    (C (F.attack.pos t)).bullet = (2 : Fin 3) ∧
    ∀ u : Nat, 0 < u → u ≤ F.attack.d →
      (C (F.attack.pos u)).bullet ≠ (0 : Fin 3) → u = t

structure TagDomain (F : TwoGapFrame n) (x : AState n ψ) : Prop where
  shot : UniqueLiveShot F x.conf
  parked_iff : x.phase = .parked ↔
    (x.conf (F.attack.pos 1)).bullet = (2 : Fin 3)
  /-- Kept explicit: the numerical C5 lemmas require this exact premise. -/
  not_done : ¬ GapDoneC F.attack x.conf

structure AInvariant (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) : Prop where
  recovery : GapInvariant hψ F.recovery x.conf
  attack : GapInvariant hψ F.attack x.conf
  tag : TagDomain F x

abbrev AActive (hψ : ψ > 0) (F : TwoGapFrame n) :=
  { x : AState n ψ // AInvariant hψ F x }

/-- A conservative fresh entrance; no entrance-construction theorem is claimed. -/
def AttemptEntrance (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) : Prop :=
  AInvariant hψ F x ∧ x.phase = .transit ∧
    (x.conf (F.attack.pos F.attack.d)).bullet = (2 : Fin 3)

/-- No RoundActive or old parked/recovery projection is used. -/
theorem activeGapProjectionNoReset (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    W F (attemptStepConf hψ F x e) =
      LDSinkGapServiceRank.gapWC F.attack (sinkStepC hψ F.attack x.conf e) := by
  rfl

theorem raw_nonincrease (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) :
    rawStoppedR F (attemptStepRaw hψ F x.1 e) ≤ R F x.1 := by
  have hw : W F (attemptStepConf hψ F x.1 e) ≤ W F x.1.conf := by
    rw [activeGapProjectionNoReset]
    exact LDSinkGapCleanupBound.gapWC_step_le'
      hψ F.attack x.1.conf x.2.attack x.2.tag.not_done e
  have hr := R_advance_le F x.1 (attemptStepConf hψ F x.1 e) hw
  unfold attemptStepRaw
  dsimp only
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact hr

theorem raw_strictDrop (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) :
    ∃ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x.1 e) < R F x.1 := by
  obtain ⟨e, he⟩ := LDSinkGapCleanupBound.exists_gapWC_step_lt'
    hψ F.attack x.1.conf x.2.attack x.2.tag.not_done
  have hw : W F (attemptStepConf hψ F x.1 e) < W F x.1.conf := by
    rw [activeGapProjectionNoReset]
    exact he
  have hr := R_advance_lt F x.1 (attemptStepConf hψ F x.1 e) hw
  refine ⟨e, ?_⟩
  unfold attemptStepRaw
  dsimp only
  split
  · exact R_pos F x.1
  · split
    · exact R_pos F x.1
    · exact hr

/-! Restrict by a proved closure law, never by a new stopping condition. -/

def AttemptClosed (hψ : ψ > 0) (F : TwoGapFrame n) : Prop :=
  ∀ (x : AActive hψ F) (e : Fin n) (y : AState n ψ),
    attemptStepRaw hψ F x.1 e = .active y → AInvariant hψ F y

structure AttemptLaws (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  continuation : AttemptClosed hψ F
  nonincrease : ∀ (x : AActive hψ F) (e : Fin n),
    rawStoppedR F (attemptStepRaw hψ F x.1 e) ≤ R F x.1
  strictDrop : ∀ x : AActive hψ F, ∃ e : Fin n,
    rawStoppedR F (attemptStepRaw hψ F x.1 e) < R F x.1

/-- Package a raw node using a proof only for its active case.
Pattern matching is on the node argument, with the proof argument introduced
after that node. Both terminal cases are unchanged. -/
def liftNode (hψ : ψ > 0) (F : TwoGapFrame n) :
    (z : StopNode (AState n ψ)) →
      (∀ y : AState n ψ, z = .active y → AInvariant hψ F y) →
      StopNode (AActive hψ F)
  | .active y, h => .active ⟨y, h y rfl⟩
  | .success, _ => .success
  | .failure, _ => .failure

/-- Only the active child is packaged with its closure proof.
There is no extra test of invariant membership in this definition. -/
def attemptStep (hψ : ψ > 0) (F : TwoGapFrame n)
    (hc : AttemptClosed hψ F) (x : AActive hψ F) (e : Fin n) :
    StopNode (AActive hψ F) :=
  liftNode hψ F (attemptStepRaw hψ F x.1 e) (hc x e)

def eraseAttemptNode (hψ : ψ > 0) (F : TwoGapFrame n) :
    StopNode (AActive hψ F) → StopNode (AState n ψ)
  | .active x => .active x.1
  | .success => .success
  | .failure => .failure

/-- Erasure is definitional on each constructor of the raw node. -/
theorem eraseAttemptNode_liftNode (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : StopNode (AState n ψ))
    (h : ∀ y : AState n ψ, z = .active y → AInvariant hψ F y) :
    eraseAttemptNode hψ F (liftNode hψ F z h) = z := by
  cases z <;> rfl

theorem attemptStep_erases (hψ : ψ > 0) (F : TwoGapFrame n)
    (hc : AttemptClosed hψ F) (x : AActive hψ F) (e : Fin n) :
    eraseAttemptNode hψ F (attemptStep hψ F hc x e) =
      attemptStepRaw hψ F x.1 e := by
  exact eraseAttemptNode_liftNode hψ F
    (attemptStepRaw hψ F x.1 e) (hc x e)

def stoppedR (hψ : ψ > 0) (F : TwoGapFrame n) :
    StopNode (AActive hψ F) → Nat
  | .active x => R F x.1
  | .success => 0
  | .failure => 0

def attemptPotential (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : StopNode (AActive hψ F)) : Nat :=
  n * stoppedR hψ F z

/-- Rank erasure is also definitional on each raw-node constructor. -/
theorem stoppedR_liftNode (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : StopNode (AState n ψ))
    (h : ∀ y : AState n ψ, z = .active y → AInvariant hψ F y) :
    stoppedR hψ F (liftNode hψ F z h) = rawStoppedR F z := by
  cases z <;> rfl

theorem stoppedR_attemptStep (hψ : ψ > 0) (F : TwoGapFrame n)
    (hc : AttemptClosed hψ F) (x : AActive hψ F) (e : Fin n) :
    stoppedR hψ F (attemptStep hψ F hc x e) =
      rawStoppedR F (attemptStepRaw hψ F x.1 e) := by
  exact stoppedR_liftNode hψ F
    (attemptStepRaw hψ F x.1 e) (hc x e)

/-- Local copy avoids depending on visibility of the EpochCost helper. -/
private theorem one_add_sum_le_mul {m r : Nat} (f : Fin m → Nat)
    (hle : ∀ e, f e ≤ r) (hlt : ∃ e, f e < r) :
    1 + (List.ofFn f).sum ≤ m * r := by
  induction m with
  | zero =>
      obtain ⟨e, _⟩ := hlt
      exact Fin.elim0 e
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      by_cases hzero : f 0 < r
      · have ht : (List.ofFn (fun e : Fin m => f e.succ)).sum ≤ m * r := by
          calc
            (List.ofFn (fun e : Fin m => f e.succ)).sum ≤
                (List.ofFn (fun _ : Fin m => r)).sum :=
              ofFn_sum_le _ _ (fun e => hle e.succ)
            _ = m * r := ofFn_sum_const m r
        omega
      · have hhead : f 0 = r := by
          have hh := hle 0
          omega
        have htail : ∃ e : Fin m, f e.succ < r := by
          obtain ⟨e, he⟩ := hlt
          revert he
          refine Fin.cases ?_ ?_ e
          · intro he
            exact (hzero he).elim
          · intro e he
            exact ⟨e, he⟩
        have ht := ih (fun e : Fin m => f e.succ)
          (fun e => hle e.succ) htail
        omega

theorem attempt_bellman_of_laws (hψ : ψ > 0) (F : TwoGapFrame n)
    (hL : AttemptLaws hψ F) :
    NatBellmanSuperSolution (attemptStep hψ F hL.continuation) 1
      (attemptPotential hψ F) := by
  refine ⟨by simp [attemptPotential, stoppedR],
    by simp [attemptPotential, stoppedR], ?_⟩
  intro x
  have hle : ∀ e : Fin n,
      stoppedR hψ F (attemptStep hψ F hL.continuation x e) ≤ R F x.1 := by
    intro e
    rw [stoppedR_attemptStep]
    exact hL.nonincrease x e
  have hlt : ∃ e : Fin n,
      stoppedR hψ F (attemptStep hψ F hL.continuation x e) < R F x.1 := by
    obtain ⟨e, he⟩ := hL.strictDrop x
    refine ⟨e, ?_⟩
    rw [stoppedR_attemptStep]
    exact he
  have hbudget :
      1 + (List.ofFn (fun e : Fin n =>
        stoppedR hψ F (attemptStep hψ F hL.continuation x e))).sum ≤
        n * R F x.1 :=
    one_add_sum_le_mul _ hle hlt
  change 1 * n + (List.ofFn (fun e : Fin n =>
    n * stoppedR hψ F (attemptStep hψ F hL.continuation x e))).sum ≤
      n * (n * R F x.1)
  rw [ofFn_sum_mul_left]
  simpa only [Nat.mul_add, Nat.mul_one, Nat.one_mul] using
    Nat.mul_le_mul_left n hbudget

/-- This costs the inner attempt up to either terminal, not the outer retry. -/
theorem attempt_cost_le_of_laws (hψ : ψ > 0) (F : TwoGapFrame n)
    (hL : AttemptLaws hψ F) (x : AActive hψ F) (T : Nat) :
    truncatedActiveCostNumerator (attemptStep hψ F hL.continuation)
        (.active x) T ≤
      n ^ T * (n * 16 * (F.recovery.d + F.attack.d)) := by
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (attemptStep hψ F hL.continuation) 1 (attemptPotential hψ F)
    (attempt_bellman_of_laws hψ F hL) (.active x) T
  have hr := R_le hψ F x.1 x.2.recovery x.2.attack
  have hc' :
      truncatedActiveCostNumerator (attemptStep hψ F hL.continuation)
          (.active x) T ≤ n ^ T * (n * R F x.1) := by
    simpa only [Nat.one_mul, attemptPotential, stoppedR] using hc
  have hb := Nat.mul_le_mul_left (n ^ T) (Nat.mul_le_mul_left n hr)
  exact Nat.le_trans hc' (by simpa only [Nat.mul_assoc] using hb)

/-! Discharge every non-boundary preservation case using C5. -/

theorem attackInvariant_of_continuation (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y)
    (hn : ¬ GapDoneC F.attack y.conf) :
    GapInvariant hψ F.attack y.conf := by
  have hc := LDSinkGapBlockedPreStep.sinkStepC_invariant_or_done'
    (hψ := hψ) (F := F.attack) (C := x.1.conf) (e := e)
    x.2.attack x.2.tag.not_done
  have hconf := attemptStepRaw_active_conf hψ F x.1 e y hy
  have hc' : GapDoneC F.attack y.conf ∨ GapInvariant hψ F.attack y.conf := by
    simpa only [hconf] using hc
  rcases hc' with hd | hi
  · exact (hn hd).elim
  · exact hi

theorem recoveryInvariant_of_nonterminal (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y)
    (hn0 : ¬ GapDoneC F.recovery x.1.conf)
    (hn1 : ¬ GapDoneC F.recovery y.conf) :
    GapInvariant hψ F.recovery y.conf := by
  have hc := LDSinkGapBlockedPreStep.sinkStepC_invariant_or_done'
    (hψ := hψ) (F := F.recovery) (C := x.1.conf) (e := e)
    x.2.recovery hn0
  have hconf : y.conf = sinkStepC hψ F.recovery x.1.conf e :=
    (attemptStepRaw_active_conf hψ F x.1 e y hy).trans
      (twoGap_sinkStepC_eq hψ F x.1.conf e).symm
  have hc' : GapDoneC F.recovery y.conf ∨ GapInvariant hψ F.recovery y.conf := by
    simpa only [hconf] using hc
  rcases hc' with hd | hi
  · exact (hn1 hd).elim
  · exact hi

/-- No escrow, projection, nonincrease, or strict-drop conclusion is assumed. -/
structure AttemptResidual (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  tagContinuation :
    ∀ (x : AActive hψ F) (e : Fin n) (y : AState n ψ),
      attemptStepRaw hψ F x.1 e = .active y → TagDomain F y
  recoveryBoundary :
    ∀ (x : AActive hψ F) (e : Fin n) (y : AState n ψ),
      attemptStepRaw hψ F x.1 e = .active y →
      (GapDoneC F.recovery x.1.conf ∨ GapDoneC F.recovery y.conf) →
      GapInvariant hψ F.recovery y.conf

theorem attemptClosed_of_residual (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptResidual hψ F) : AttemptClosed hψ F := by
  intro x e y hy
  have ht := hR.tagContinuation x e y hy
  have ha := attackInvariant_of_continuation hψ F x e y hy ht.not_done
  have hr : GapInvariant hψ F.recovery y.conf := by
    by_cases h0 : GapDoneC F.recovery x.1.conf
    · exact hR.recoveryBoundary x e y hy (Or.inl h0)
    · by_cases h1 : GapDoneC F.recovery y.conf
      · exact hR.recoveryBoundary x e y hy (Or.inr h1)
      · exact recoveryInvariant_of_nonterminal hψ F x e y hy h0 h1
  exact ⟨hr, ha, ht⟩

theorem attemptLaws_of_residual (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptResidual hψ F) : AttemptLaws hψ F := by
  exact ⟨attemptClosed_of_residual hψ F hR,
    raw_nonincrease hψ F, raw_strictDrop hψ F⟩

end -- noncomputable section

end LDSinkTwoGapNoResetKernel

#print axioms LDSinkTwoGapNoResetKernel.success2_covers_three
#print axioms LDSinkTwoGapNoResetKernel.attemptStepRaw_failure_iff
#print axioms LDSinkTwoGapNoResetKernel.R_le
#print axioms LDSinkTwoGapNoResetKernel.phaseDebtA_advance_le
#print axioms LDSinkTwoGapNoResetKernel.activeGapProjectionNoReset
#print axioms LDSinkTwoGapNoResetKernel.raw_nonincrease
#print axioms LDSinkTwoGapNoResetKernel.raw_strictDrop
#print axioms LDSinkTwoGapNoResetKernel.eraseAttemptNode_liftNode
#print axioms LDSinkTwoGapNoResetKernel.attemptStep_erases
#print axioms LDSinkTwoGapNoResetKernel.stoppedR_liftNode
#print axioms LDSinkTwoGapNoResetKernel.stoppedR_attemptStep
#print axioms LDSinkTwoGapNoResetKernel.attempt_bellman_of_laws
#print axioms LDSinkTwoGapNoResetKernel.attempt_cost_le_of_laws
#print axioms LDSinkTwoGapNoResetKernel.attackInvariant_of_continuation
#print axioms LDSinkTwoGapNoResetKernel.recoveryInvariant_of_nonterminal
#print axioms LDSinkTwoGapNoResetKernel.attemptClosed_of_residual
#print axioms LDSinkTwoGapNoResetKernel.attemptLaws_of_residual
