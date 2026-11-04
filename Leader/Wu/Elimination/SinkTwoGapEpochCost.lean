import Leader.Wu.Elimination.SinkTwoGapEpoch


open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs PPLLRepair FiniteUniformStoppingTree
open Classical


namespace LDSinkTwoGapEpochCost


set_option autoImplicit false


variable {n ψ : Nat}


/-! ## Phase debt -/


/-- One lexicographic phase block.  It dominates the sum of the largest
possible local K2 rank and the largest within-phase service reserve, while
remaining linear in the two gap lengths. -/
def phaseSpan (F : TwoGapFrame n) : Nat :=
  4 * (F.recovery.d + F.attack.d) + 2


/-- The ordered part of the live outer-round phases:


    resetK > seekK > transit > parked.


`seekJ` is kept at parked level, while `favorable` is the zero-debt marker. -/
def phaseLevel : GhostPhase → Nat
  | .seekK => 2
  | .transit => 1
  | .parked => 0
  | .resetK => 3
  | .seekJ => 0
  | .favorable => 0


/-- Requested remaining service budget inside each phase.  `seekJ` uses the
same j-cycle reserve as `parked`; `favorable` carries no service debt. -/
def phaseServiceDebt (F : TwoGapFrame n) : GhostPhase → Nat
  | .seekK => 2 * F.attack.d + 1
  | .transit => F.attack.d
  | .parked => 1 + 2 * F.recovery.d
  | .resetK => 2 * F.attack.d
  | .seekJ => 1 + 2 * F.recovery.d
  | .favorable => 0


/-- Lexicographic ghost debt.  The phase order is prepaid by whole
`phaseSpan` blocks; the requested service count is the within-block offset. -/
def phaseDebt (F : TwoGapFrame n) (p : GhostPhase) : Nat :=
  phaseLevel p * phaseSpan F + phaseServiceDebt F p


/-- Uniform upper bound for the K2 rank selected by a ghost phase. -/
def localRankBound (F : TwoGapFrame n) : GhostPhase → Nat
  | .seekK => 2 * F.attack.d
  | .transit => 2 * F.attack.d
  | .parked => 2 * F.recovery.d
  | .resetK => 2 * F.attack.d
  | .seekJ => 2 * F.recovery.d
  | .favorable => 0


/-- `resetK` is strictly above `seekK`, despite its smaller local service
budget, because it occupies the next lexicographic block. -/
theorem phaseDebt_resetK_gt_seekK (F : TwoGapFrame n) :
    phaseDebt F .seekK < phaseDebt F .resetK := by
  simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt]
  omega


/-- The rest of the requested phase order. -/
theorem phaseDebt_seekK_gt_transit (F : TwoGapFrame n) :
    phaseDebt F .transit < phaseDebt F .seekK := by
  simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt]
  omega


theorem phaseDebt_transit_gt_parked (F : TwoGapFrame n) :
    phaseDebt F .parked < phaseDebt F .transit := by
  simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt]
  omega


/-- Every non-favorable ghost phase carries positive debt. -/
theorem phaseDebt_pos_of_not_favorable (F : TwoGapFrame n)
    (p : GhostPhase) (hp : p ≠ .favorable) :
    0 < phaseDebt F p := by
  cases p <;>
    simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt] at hp ⊢ <;>
    omega


/-- Every phase except `transit` is definitionally fixed by `advancePhase`. -/
theorem advancePhase_eq_self_of_ne_transit (F : TwoGapFrame n)
    (p : GhostPhase) (C : Fin n → AgentState ψ) (hp : p ≠ .transit) :
    advancePhase F p C = p := by
  cases p with
  | seekK => rfl
  | transit => exact False.elim (hp rfl)
  | parked => rfl
  | resetK => rfl
  | seekJ => rfl
  | favorable => rfl


/-- `advancePhase` itself never raises the phase debt.  Its only proper phase
change is `transit -> parked`. -/
theorem phaseDebt_advancePhase_le (F : TwoGapFrame n) (p : GhostPhase)
    (C : Fin n → AgentState ψ) :
    phaseDebt F (advancePhase F p C) ≤ phaseDebt F p := by
  cases p with
  | seekK => exact Nat.le_refl _
  | transit =>
      simp only [advancePhase]
      split
      · simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt]
        omega
      · exact Nat.le_refl _
  | parked => exact Nat.le_refl _
  | resetK => exact Nat.le_refl _
  | seekJ => exact Nat.le_refl _
  | favorable => exact Nat.le_refl _


/-- On a proper `advancePhase` change, the dropped phase debt pays for the
entire local-rank budget of the new phase.  The change hypothesis is necessary:
without it the statement is false on every positive self-phase. -/
theorem phaseDebt_advance_dominates_local (F : TwoGapFrame n)
    (p : GhostPhase) (C : Fin n → AgentState ψ)
    (hchange : advancePhase F p C ≠ p) :
    phaseDebt F (advancePhase F p C) +
        localRankBound F (advancePhase F p C) ≤ phaseDebt F p := by
  cases p with
  | seekK => exact False.elim (hchange rfl)
  | transit =>
      by_cases hb :
          (C (F.attack.pos 1)).bullet = (2 : Fin 3)
      · have hphase : advancePhase F .transit C = .parked := by
          simp [advancePhase, hb]
        rw [hphase]
        simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt,
          localRankBound]
        omega
      · have hphase : advancePhase F .transit C = .transit := by
          simp [advancePhase, hb]
        exact False.elim (hchange hphase)
  | parked => exact False.elim (hchange rfl)
  | resetK => exact False.elim (hchange rfl)
  | seekJ => exact False.elim (hchange rfl)
  | favorable => exact False.elim (hchange rfl)


/-- Exact exceptional raise introduced by the outer-round absorption restart. -/
def absorptionRaise (F : TwoGapFrame n) : Nat :=
  10 * F.recovery.d + 14 * F.attack.d + 5


/-- The exceptional `parked -> resetK` transition raises phase debt by exactly
`10r + 14a + 5`. -/
theorem phaseDebt_resetK_eq_parked_add_absorptionRaise
    (F : TwoGapFrame n) :
    phaseDebt F .resetK =
      phaseDebt F .parked + absorptionRaise F := by
  simp [phaseDebt, phaseLevel, phaseSpan, phaseServiceDebt, absorptionRaise]
  omega


theorem phaseDebt_parked_lt_resetK (F : TwoGapFrame n) :
    phaseDebt F .parked < phaseDebt F .resetK := by
  have heq := phaseDebt_resetK_eq_parked_add_absorptionRaise F
  have hpos : 0 < absorptionRaise F := by
    simp [absorptionRaise]
  omega


/-- Pure bookkeeping classification: an ordinary `advancePhase` move is
nonincreasing; the only separately admitted outer-round phase jump is exactly
`parked -> resetK`, with the explicit raise above. -/
theorem phaseDebt_round_change_classification
    (F : TwoGapFrame n) (p q : GhostPhase)
    (C : Fin n → AgentState ψ)
    (hchange :
      q = advancePhase F p C ∨
        (p = .parked ∧ q = .resetK)) :
    phaseDebt F q ≤ phaseDebt F p ∨
      (p = .parked ∧ q = .resetK ∧
        phaseDebt F q = phaseDebt F p + absorptionRaise F) := by
  rcases hchange with hadvance | habsorb
  · left
    subst q
    exact phaseDebt_advancePhase_le F p C
  · right
    rcases habsorb with ⟨hp, hq⟩
    subst p
    subst q
    exact ⟨rfl, rfl,
      phaseDebt_resetK_eq_parked_add_absorptionRaise F⟩


/-! ## Round rank -/


/-- Current K2 one-gap rank of the active service.  The recovery gap is active
while parked / seeking j; the attack gap is active in the K-side phases.
`favorable` has no local service rank. -/
noncomputable def localRank (F : TwoGapFrame n)
    (x : EpochState n ψ F) : Nat :=
  match x.phase with
  | .seekK => LDSinkGapServiceRank.gapWC F.attack x.conf
  | .transit => LDSinkGapServiceRank.gapWC F.attack x.conf
  | .parked => LDSinkGapServiceRank.gapWC F.recovery x.conf
  | .resetK => LDSinkGapServiceRank.gapWC F.attack x.conf
  | .seekJ => LDSinkGapServiceRank.gapWC F.recovery x.conf
  | .favorable => 0


/-- The active K2 rank is bounded by the phase-selected local-rank budget. -/
theorem localRank_le_localRankBound (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F)
    (hRecovery : GapInvariant hψ F.recovery x.conf)
    (hAttack : GapInvariant hψ F.attack x.conf) :
    localRank F x ≤ localRankBound F x.phase := by
  have hrec := LDSinkGapServiceRank.gapWC_le_two_d
    hψ F.recovery x.conf hRecovery
  have hatt := LDSinkGapServiceRank.gapWC_le_two_d
    hψ F.attack x.conf hAttack
  cases hphase : x.phase with
  | seekK =>
      simpa [localRank, localRankBound, hphase] using hatt
  | transit =>
      simpa [localRank, localRankBound, hphase] using hatt
  | parked =>
      simpa [localRank, localRankBound, hphase] using hrec
  | resetK =>
      simpa [localRank, localRankBound, hphase] using hatt
  | seekJ =>
      simpa [localRank, localRankBound, hphase] using hrec
  | favorable =>
      simp [localRank, localRankBound, hphase]


/-- One-unit active floor plus lexicographic phase debt plus the active K2
rank.  The phase multiplier is already absorbed into `phaseDebt`; multiplying
by another linear span here would destroy the desired linear bound. -/
noncomputable def roundRank (F : TwoGapFrame n)
    (x : EpochState n ψ F) : Nat :=
  if Success F x.conf then 0
  else 1 + phaseDebt F x.phase + localRank F x


/-- `roundRank` vanishes exactly at success, not merely at a zero local K2
rank or a favorable ghost marker. -/
theorem roundRank_eq_zero_iff_success (F : TwoGapFrame n)
    (x : EpochState n ψ F) :
    roundRank F x = 0 ↔ Success F x.conf := by
  constructor
  · intro hz
    by_cases hs : Success F x.conf
    · exact hs
    · unfold roundRank at hz
      rw [if_neg hs] at hz
      omega
  · intro hs
    simp [roundRank, hs]


theorem roundRank_pos_of_not_success (F : TwoGapFrame n)
    (x : EpochState n ψ F) (hs : ¬ Success F x.conf) :
    0 < roundRank F x := by
  unfold roundRank
  rw [if_neg hs]
  omega


/-- Smallest clean coefficient `c` for the uniform bound
`roundRank ≤ c * (recovery.d + attack.d) + c` obtained from
`1 + 3 * phaseSpan + max serviceDebt + max localRank`. -/
def roundRankConstant : Nat := 16


/-- The phase bookkeeping plus one active K2 rank stays linear. -/
theorem roundRank_le (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F)
    (hRecovery : GapInvariant hψ F.recovery x.conf)
    (hAttack : GapInvariant hψ F.attack x.conf) :
    roundRank F x ≤
      roundRankConstant * (F.recovery.d + F.attack.d) +
        roundRankConstant := by
  have hrec := LDSinkGapServiceRank.gapWC_le_two_d
    hψ F.recovery x.conf hRecovery
  have hatt := LDSinkGapServiceRank.gapWC_le_two_d
    hψ F.attack x.conf hAttack
  have hrecPos := F.recovery.hd
  have hattPos := F.attack.hd
  by_cases hs : Success F x.conf
  · simp [roundRank, hs]
  · cases hphase : x.phase <;>
      simp [roundRank, hs, localRank, hphase, phaseDebt, phaseLevel,
        phaseSpan, phaseServiceDebt, roundRankConstant] <;>
      omega


/-- The advertised bound at an epoch entrance. -/
theorem roundRank_le_of_entrance (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (hx : Entrance hψ F x) :
    roundRank F x ≤
      roundRankConstant * (F.recovery.d + F.attack.d) +
        roundRankConstant := by
  exact roundRank_le hψ F x hx.1 hx.2.1


/-- This is the explicit prepaid seam requested for the unique absorption
raise.  It is deliberately a Prop obligation, not a theorem: the pasted
`Entrance` definition by itself does not contain this quantitative credit. -/
def AbsorptionPrepaidAtEntrance (hψ : ψ > 0)
    (F : TwoGapFrame n) : Prop :=
  ∀ x : EpochState n ψ F,
    Entrance hψ F x →
    ¬ Success F x.conf →
    absorptionRaise F ≤ roundRank F x


/-! ## The stopped outer-round process -/


/-- Bellman-active states are exactly positive-rank states.  By the theorem
above these are precisely the non-success configurations. -/
abbrev RoundActive (F : TwoGapFrame n) :=
  {x : EpochState n ψ F // 0 < roundRank F x}


/-- `roundStep` retyped onto the non-success active carrier.  The branching is
identical to `roundStep`: success stops; parked absorption restarts at
`resetK`; every other non-success edge uses `advancePhase`. -/
noncomputable def roundStepStopped (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : RoundActive (ψ := ψ) F) (e : Fin n) :
    StopNode (RoundActive (ψ := ψ) F) :=
  let C' := epochStepConf hψ F x.1 e
  if hs : Success F C' then
    .success
  else if ParkedAbsorption F x.1 C' then
    .active ⟨{ conf := C', phase := .resetK },
      roundRank_pos_of_not_success F _ hs⟩
  else
    .active ⟨{ conf := C', phase := advancePhase F x.1.phase C' },
      roundRank_pos_of_not_success F _ hs⟩


/-- Lift the state rank to stopped nodes. -/
noncomputable def stoppedRoundRank (F : TwoGapFrame n) :
    StopNode (RoundActive (ψ := ψ) F) → Nat
  | .active x => roundRank F x.1
  | .success => 0
  | .failure => 0


/-- Scheduler-scaled Bellman potential. -/
noncomputable def roundPotential (F : TwoGapFrame n) :
    StopNode (RoundActive (ψ := ψ) F) → Nat :=
  fun z => n * stoppedRoundRank F z


/-- Kernel-facing contract.  The first two fields are exactly the missing
edgewise rank theorem: every raw scheduler child is nonincreasing and at least
one raw edge strictly drops.  `RoundActive` already excludes Success.
The third field exposes the pure phase-retirement fact in the same contract. -/
structure RoundRankLaws (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  nonincrease :
    ∀ (x : RoundActive (ψ := ψ) F) (e : Fin n),
      stoppedRoundRank F (roundStepStopped hψ F x e) ≤
        roundRank F x.1
  strictDrop :
    ∀ x : RoundActive (ψ := ψ) F,
      ∃ e : Fin n,
        stoppedRoundRank F (roundStepStopped hψ F x e) <
          roundRank F x.1
  phaseAdvanceRetires :
    ∀ (p : GhostPhase) (C : Fin n → AgentState ψ),
      phaseDebt F (advancePhase F p C) ≤ phaseDebt F p


/-! ## Arithmetic consequences of the laws -/


/-- If all `m` children are at most `r` and one is strictly below `r`, their
sum leaves one unit of Bellman slack. -/
private theorem one_add_ofFn_sum_le_mul
    {m r : Nat} (f : Fin m → Nat)
    (hle : ∀ e, f e ≤ r)
    (hlt : ∃ e, f e < r) :
    1 + (List.ofFn f).sum ≤ m * r := by
  induction m with
  | zero =>
      rcases hlt with ⟨e, _⟩
      exact Fin.elim0 e
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      rcases hlt with ⟨e, he⟩
      cases e using Fin.cases with
      | zero =>
          have htail :
              (List.ofFn (fun i : Fin m => f i.succ)).sum ≤ m * r := by
            calc
              (List.ofFn (fun i : Fin m => f i.succ)).sum ≤
                  (List.ofFn (fun _ : Fin m => r)).sum := by
                    apply ofFn_sum_le
                    intro i
                    exact hle i.succ
              _ = m * r := ofFn_sum_const m r
          have hhead : f 0 + 1 ≤ r := by omega
          omega
      | succ i =>
          have htail :
              1 + (List.ofFn (fun j : Fin m => f j.succ)).sum ≤
                m * r :=
            ih (fun j : Fin m => f j.succ)
              (fun j => hle j.succ) ⟨i, he⟩
          have hhead : f 0 ≤ r := hle 0
          omega


/-- Pointwise rank laws imply the division-free Bellman supersolution. -/
theorem roundRank_bellman_of_laws (hψ : ψ > 0) (F : TwoGapFrame n)
    (hL : RoundRankLaws hψ F) :
    NatBellmanSuperSolution (roundStepStopped hψ F) 1
      (roundPotential F) := by
  refine ⟨by simp [roundPotential, stoppedRoundRank],
    by simp [roundPotential, stoppedRoundRank], ?_⟩
  intro x
  have hbudget :
      1 + (List.ofFn (fun e : Fin n =>
        stoppedRoundRank F (roundStepStopped hψ F x e))).sum ≤
        n * roundRank F x.1 :=
    one_add_ofFn_sum_le_mul
      (fun e : Fin n =>
        stoppedRoundRank F (roundStepStopped hψ F x e))
      (fun e => hL.nonincrease x e)
      (hL.strictDrop x)
  change 1 * n +
      (List.ofFn (fun e : Fin n =>
        n * stoppedRoundRank F (roundStepStopped hψ F x e))).sum ≤
      n * (n * roundRank F x.1)
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hscaled := Nat.mul_le_mul_left n hbudget
  simpa [Nat.mul_add] using hscaled


/-- Finite-horizon active-cost bound at an entrance.  The only kernel input is
`RoundRankLaws`; the rest is the generic stopped-tree Bellman arithmetic plus
`roundRank_le_of_entrance`. -/
theorem round_cost_le_of_laws (hψ : ψ > 0) (F : TwoGapFrame n)
    (hL : RoundRankLaws hψ F)
    (x : EpochState n ψ F) (hx : Entrance hψ F x)
    (hs : ¬ Success F x.conf) (T : Nat) :
    truncatedActiveCostNumerator (roundStepStopped hψ F)
        (.active ⟨x, roundRank_pos_of_not_success F x hs⟩) T ≤
      n ^ T *
        (n * (roundRankConstant *
          (F.recovery.d + F.attack.d) + roundRankConstant)) := by
  have hraw :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (roundStepStopped hψ F) 1 (roundPotential F)
      (roundRank_bellman_of_laws hψ F hL)
      (.active ⟨x, roundRank_pos_of_not_success F x hs⟩) T
  have hcost :
      truncatedActiveCostNumerator (roundStepStopped hψ F)
          (.active ⟨x, roundRank_pos_of_not_success F x hs⟩) T ≤
        n ^ T * (n * roundRank F x) := by
    simpa [roundPotential, stoppedRoundRank] using hraw
  have hrank := roundRank_le_of_entrance hψ F x hx
  calc
    truncatedActiveCostNumerator (roundStepStopped hψ F)
        (.active ⟨x, roundRank_pos_of_not_success F x hs⟩) T ≤
        n ^ T * (n * roundRank F x) := hcost
    _ ≤ n ^ T *
        (n * (roundRankConstant *
          (F.recovery.d + F.attack.d) + roundRankConstant)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n hrank)


end LDSinkTwoGapEpochCost


#print axioms LDSinkTwoGapEpochCost.phaseDebt_resetK_gt_seekK
#print axioms LDSinkTwoGapEpochCost.phaseDebt_seekK_gt_transit
#print axioms LDSinkTwoGapEpochCost.phaseDebt_transit_gt_parked
#print axioms LDSinkTwoGapEpochCost.phaseDebt_pos_of_not_favorable
#print axioms LDSinkTwoGapEpochCost.advancePhase_eq_self_of_ne_transit
#print axioms LDSinkTwoGapEpochCost.phaseDebt_advancePhase_le
#print axioms LDSinkTwoGapEpochCost.phaseDebt_advance_dominates_local
#print axioms LDSinkTwoGapEpochCost.phaseDebt_resetK_eq_parked_add_absorptionRaise
#print axioms LDSinkTwoGapEpochCost.phaseDebt_round_change_classification
#print axioms LDSinkTwoGapEpochCost.localRank_le_localRankBound
#print axioms LDSinkTwoGapEpochCost.roundRank_eq_zero_iff_success
#print axioms LDSinkTwoGapEpochCost.roundRank_le
#print axioms LDSinkTwoGapEpochCost.roundRank_bellman_of_laws
#print axioms LDSinkTwoGapEpochCost.round_cost_le_of_laws
