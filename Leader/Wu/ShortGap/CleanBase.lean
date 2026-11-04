import Leader.Wu.ShortGap.StrictRoundService
import Leader.Wu.ShortGap.GhostVarLength

/-!
# The original clean state is a base, but not an active round

The two imported implementations initialize every physical root to the fixed
resolved choice `R.b`, record that choice at generation 0, and set k=0.
Consequently all four fields of `RoundBase 0` hold, while the separate
`Round.race` field fails. Positive indices instead fail `RoundBase.entered`.
Neither an index shift nor deleting a successor-only premise changes this.

The necessary preparation for the next strict base is service of generation
0 until its debt at index 1 vanishes, or an earlier virtual candidate occurs.
We expose that exact stopping condition and its service-only cost. This does
not identify preparation completion with physical candidate realization, and
does not assert that the smaller end-to-end numerical bound is false under
every possible alternative potential.
-/

namespace ShortGapCleanBase
open FiniteUniformStoppingTree BalancedFailureRestartPartialExitEntry
set_option autoImplicit false

/-! The standalone preparation stops on either service exit or its sidecar.
Its success symbol means only completion of preparation. -/

/-- Forget the exit payload only for measuring the duration of service. -/
def finishService {S Q : Type} : ServiceOutcome S Q → StopNode S
  | .cont s => .active s
  | .exit _ | .succeed => .success

/-- The residual service potential is zero at both preparation terminals. -/
def preparationPotential {S : Type} (p : S → Nat) : StopNode S → Nat
  | .active s => p s
  | .success | .failure => 0

theorem finishService_potential {S Q : Type} (p : S → Nat) (x : ServiceOutcome S Q) :
    preparationPotential p (finishService x) = serviceOutcomePotential p x := by
  cases x <;> rfl

/-- The existing service certificate measures precisely the time to its
first exit or sidecar success; it needs no round reserve. -/
theorem preparation_bellman {S Q : Type} {n : Nat}
    (step : S → Fin n → ServiceOutcome S Q) (p : S → Nat)
    (h : ServiceBellman step 1 p) :
    NatBellmanSuperSolution (fun s e => finishService (step s e)) 1 (preparationPotential p) := by
  refine ⟨rfl,rfl,?_⟩
  intro s
  change 1*n + _ ≤ n*p s
  simpa only [finishService_potential] using h s

namespace Variable
open ShortGapGhostVarLength ShortGapLiteralGapRows

/-- An alias of the actual imported clean state, without reseeding it. -/
abbrev cleanGhost (R : VFrame) := ghostStart2 R

theorem cleanGhost_history (R : VFrame) (i : Fin R.m) (q : Nat) :
    (cleanGhost R).hist i q = if q = 0 then some R.b else none := rfl

theorem cleanGhost_root (R : VFrame) (i : Fin R.m) :
    (cleanGhost R).cfg (rootV R i) = .root R.b .toSend .free := rfl

theorem cleanGhost_word_zero (R : VFrame) (i : Fin R.m) :
    word2 R 0 (cleanGhost R) i = ShortGapLineage.choiceToWord R.b := rfl

/-- The predecessor convention is already correct at zero for every state. -/
theorem predecessor_debt_zero (R : VFrame) (s : GhostRing2 R) :
    latentDebt2 R 0 s = 0 := all_entered_debt_zero R 0 s (fun _ => Nat.zero_le _)

theorem generation_mask_zero (R : VFrame) (s : GhostRing2 R) (i : Fin R.m) :
    genMask2 R 0 s i = true := by simp [genMask2]

/-- No RoundBase field needs repair: the unchanged clean state inhabits
its zero fiber using the imported lineage and no-success producers. -/
theorem cleanGhost_roundBase_zero (R : VFrame) : RoundBase R 0 (cleanGhost R) where
  lineage := lineage2_start R
  entered := fun _ => Nat.zero_le _
  zero := predecessor_debt_zero R _
  noSuccess := (initialService R).dom.noSuccess

/-- At every positive index it is exactly the entered field that fails. -/
theorem cleanGhost_not_entered_succ (R : VFrame) (r : Nat) :
    ¬ (∀ i, r+1 ≤ (cleanGhost R).k i) := by
  intro h
  have hi := h ⟨0,by have := R.hm; omega⟩
  change r+1 ≤ 0 at hi
  omega

theorem cleanGhost_roundBase_iff (R : VFrame) (r : Nat) :
    RoundBase R r (cleanGhost R) ↔ r = 0 := by
  constructor
  · intro h
    have hi := h.entered ⟨0,by have := R.hm; omega⟩
    change r ≤ 0 at hi
    omega
  · rintro rfl
    exact cleanGhost_roundBase_zero R

/-- The independent active-word field fails because generation 0 is
already a constant resolved word. This is the actual semantic obstruction. -/
theorem cleanGhost_noRace_zero (R : VFrame) :
    ¬ PeriodHIncidenceChoice.HasRace (word2 R 0 (cleanGhost R)) := by
  rintro ⟨i,hi⟩
  exact (initialService R).dom.frozen i hi

theorem cleanGhost_not_active (R : VFrame) (r : Nat) :
    ¬ (RoundBase R r (cleanGhost R) ∧ PeriodHIncidenceChoice.HasRace (word2 R r (cleanGhost R))) := by
  rintro ⟨hb,hr⟩
  have h := (cleanGhost_roundBase_iff R r).mp hb
  subst r
  exact cleanGhost_noRace_zero R hr

/-- The discrepancy is physical as well as historical: even the root's
actual choice is not Race. Changing only annotations cannot fix this fact. -/
theorem cleanGhost_root_not_race (R : VFrame) (i : Fin R.m) :
    (cleanGhost R).cfg (rootV R i) ≠ .root .race .toSend .free := by
  rw [cleanGhost_root]
  rcases R.hb with h | h <;> rw [h] <;> intro he <;> cases he

theorem cleanGhost_reserve_zero (R : VFrame) :
    PeriodHIncidenceChoice.choiceRaceReserve (word2 R 0 (cleanGhost R)) = 0 := by
  have hf : ∀ i, word2 R 0 (cleanGhost R) i ≠ .race := (initialService R).dom.frozen
  simp [PeriodHIncidenceChoice.choiceRaceReserve,hf,ofFn_sum_const]

/-- Deleting HasRace would invalidate the old reserve child sum at this
very state: the right side is zero and the unit running cost is positive. -/
theorem cleanGhost_reserve_childSum_false (R : VFrame) :
    ¬ (1 + (List.ofFn (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
      (word2 R 0 (ghostStep2 R (cleanGhost R) (edgeVtx R e))))).sum ≤
      R.n * PeriodHIncidenceChoice.choiceRaceReserve (word2 R 0 (cleanGhost R))) := by
  rw [cleanGhost_reserve_zero, Nat.mul_zero]
  omega

/-- Among lineage states without virtual success, zero generation-0 debt
is necessary and sufficient for the next strict base. This is a stopping
condition, not a claim of an optimal expected preparation cost. -/
theorem next_base_iff_zero_debt (R : VFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hn : ¬ VirtualSuccess R 1 s) :
    RoundBase R 1 s ↔ latentDebt2 R 1 s = 0 := by
  exact ⟨fun h => h.zero,fun hz => ⟨hs,debt0_all_entered R 1 s hs hn hz,hz,hn⟩⟩

theorem cleanGhost_preparation_debt (R : VFrame) :
    latentDebt2 R 1 (cleanGhost R) = 2*R.n-R.m := latentDebt2_start R

theorem cleanGhost_preparation_positive (R : VFrame) :
    0 < latentDebt2 R 1 (cleanGhost R) := (initialService R).dom.positive

/-- Reuse the unchanged service, stopping only its duration counter. -/
noncomputable def preparationStep (R : VFrame) (s : Service R) (e : Fin R.n) : StopNode (Service R) :=
  finishService (serviceStep R s e)

theorem preparationStep_bellman (R : VFrame) :
    NatBellmanSuperSolution (preparationStep R) 1 (preparationPotential (servicePotential R)) :=
  preparation_bellman (serviceStep R) (servicePotential R) (service_bellman R)

/-- Every preparation exit supplies either a virtual candidate or the next
actual active round, in the very same physical child. -/
theorem preparation_success_sound (R : VFrame) (s : Service R) (e : Fin R.n)
    (h : preparationStep R s e = .success) :
    VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) ∨
      (RoundBase R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) ∧
        PeriodHIncidenceChoice.HasRace (word2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)))) := by
  classical
  by_cases hv : VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e))
  · exact Or.inl hv
  · apply Or.inr
    have hz : latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) = 0 := by
      apply Classical.byContradiction
      intro hn
      simp [preparationStep,serviceStep,hv,hn,finishService] at h
    exact service_exit R s.idx s.state s.dom _ hv hz

theorem preparation_step_erases (R : VFrame) (s t : Service R) (e : Fin R.n)
    (h : preparationStep R s e = .active t) :
    t.state = ghostStep2 R s.state (edgeVtx R e) := by
  classical
  unfold preparationStep serviceStep at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- Exact initial service credit, excluding all subsequent round costs. -/
theorem preparation_initial_potential (R : VFrame) :
    servicePotential R (initialService R) = R.n*(2*R.n-R.m) := by
  change R.n*latentDebt2 R 1 (cleanGhost R) = _
  rw [cleanGhost_preparation_debt]

theorem preparation_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (preparationStep R) (.active (initialService R)) T ≤
      R.n^T*(R.n*(2*R.n-R.m)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (preparationStep R) 1 (preparationPotential (servicePotential R))
    (preparationStep_bellman R) (.active (initialService R)) T
  simpa only [Nat.one_mul,preparationPotential,preparation_initial_potential] using h

/-- The unchanged preparation-plus-round certificate has the original
larger clean-start budget; no tighter bound is inferred from RoundBase 0. -/
theorem physicalCandidate_clean_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.n+R.n*(2*hMax R-1)) :=
  ShortGapGhostVarLength.physicalCandidate_clean_truncatedCost_le R T

theorem physicalCandidate_clean_success_one_minus_inv_factor (R : VFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.n+R.n*(2*hMax R-1))) :=
  ShortGapGhostVarLength.physicalCandidate_clean_success_one_minus_inv_factor R factor

/-- An active service cannot already be the next strict base. -/
theorem service_not_next_base (R : VFrame) (s : Service R) :
    ¬ RoundBase R (s.idx+1) s.state := by
  intro h
  have hp := s.dom.positive
  rw [h.zero] at hp
  omega

/-- Exact earliest exit condition of this service interface. A candidate
may interrupt preparation before zero debt; otherwise zero debt is required. -/
theorem preparation_success_iff (R : VFrame) (s : Service R) (e : Fin R.n) :
    preparationStep R s e = .success ↔
      VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) ∨
        latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) = 0 := by
  classical
  unfold preparationStep serviceStep
  dsimp only
  split
  · rename_i hv
    simp [finishService,hv]
  · rename_i hv
    split <;> simp_all [finishService]

/-- The larger existing credit is precisely strict-start credit plus
initial service credit; the latch allowance cancels from this comparison. -/
theorem clean_credit_decomposition (R : VFrame) :
    physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) =
      (R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) + servicePotential R (initialService R) := by
  change servicePotential R (initialService R) + R.n*R.m +
    (R.n*R.m+R.n*(2*R.n-R.m)) + R.n*(2*hMax R-1) = _
  have h := tightBudget_eq R
  omega

/-- Thus the unchanged certificate cannot supply a start-credit bound
with the strict constant. This is not a lower bound on true stopping time. -/
theorem current_clean_credit_exceeds_tight (R : VFrame) :
    R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1) <
      physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) := by
  have hp : 0 < servicePotential R (initialService R) :=
    Nat.mul_pos (n_pos R) (initialService R).dom.positive
  rw [clean_credit_decomposition]
  omega

/-- No index-carrying active round can have this unchanged clean state. -/
theorem no_round_with_clean_state (R : VFrame) :
    ¬ (∃ s : Round R, s.state = cleanGhost R) := by
  rintro ⟨s,he⟩
  have hb := s.base
  have hr := s.race
  rw [he] at hb hr
  exact cleanGhost_not_active R s.idx ⟨hb,hr⟩

/-- The initial history is recorded at every root, contradicting the
empty-history premise used by the proposed zero-index shortcut. -/
theorem cleanGhost_history_zero_ne_none (R : VFrame) (i : Fin R.m) :
    (cleanGhost R).hist i 0 ≠ none := by
  change some R.b ≠ none
  intro h
  cases h

end Variable

namespace Uniform
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapLineage ShortGapLineageRetained ShortGapTwoEpoch
open ShortGapGenerationMask ShortGapDenialTransportLiteral
open ShortGapLineage2Closure ShortGapLineage2ClosureB ShortGapGhostComposition2

/-- An alias of the actual imported clean state, without reseeding it. -/
abbrev cleanGhost (R : RFrame) := ghostStart2 R

theorem cleanGhost_history (R : RFrame) (i : Fin R.m) (q : Nat) :
    (cleanGhost R).hist i q = if q = 0 then some R.b else none := rfl

theorem cleanGhost_root (R : RFrame) (i : Fin R.m) :
    (cleanGhost R).cfg (rootV R i) = .root R.b .toSend .free := rfl

theorem cleanGhost_word_zero (R : RFrame) (i : Fin R.m) :
    word2 R 0 (cleanGhost R) i = ShortGapLineage.choiceToWord R.b := rfl

/-- The predecessor convention is already correct at zero for every state. -/
theorem predecessor_debt_zero (R : RFrame) (s : GhostRing2 R) :
    latentDebt2 R 0 s = 0 := all_entered_debt_zero R 0 s (fun _ => Nat.zero_le _)

theorem generation_mask_zero (R : RFrame) (s : GhostRing2 R) (i : Fin R.m) :
    genMask2 R 0 s i = true := by simp [genMask2,genMask]

/-- No RoundBase field needs repair: the unchanged clean state inhabits
its zero fiber using the imported lineage and no-success producers. -/
theorem cleanGhost_roundBase_zero (R : RFrame) : RoundBase R 0 (cleanGhost R) where
  lineage := lineage2_start R
  entered := fun _ => Nat.zero_le _
  zero := predecessor_debt_zero R _
  noSuccess := (initialService R).dom.noSuccess

/-- At every positive index it is exactly the entered field that fails. -/
theorem cleanGhost_not_entered_succ (R : RFrame) (r : Nat) :
    ¬ (∀ i, r+1 ≤ (cleanGhost R).k i) := by
  intro h
  have hi := h ⟨0,by have := R.hm; omega⟩
  change r+1 ≤ 0 at hi
  omega

theorem cleanGhost_roundBase_iff (R : RFrame) (r : Nat) :
    RoundBase R r (cleanGhost R) ↔ r = 0 := by
  constructor
  · intro h
    have hi := h.entered ⟨0,by have := R.hm; omega⟩
    change r ≤ 0 at hi
    omega
  · rintro rfl
    exact cleanGhost_roundBase_zero R

/-- The independent active-word field fails because generation 0 is
already a constant resolved word. This is the actual semantic obstruction. -/
theorem cleanGhost_noRace_zero (R : RFrame) :
    ¬ PeriodHIncidenceChoice.HasRace (word2 R 0 (cleanGhost R)) := by
  rintro ⟨i,hi⟩
  exact (initialService R).dom.frozen i hi

theorem cleanGhost_not_active (R : RFrame) (r : Nat) :
    ¬ (RoundBase R r (cleanGhost R) ∧ PeriodHIncidenceChoice.HasRace (word2 R r (cleanGhost R))) := by
  rintro ⟨hb,hr⟩
  have h := (cleanGhost_roundBase_iff R r).mp hb
  subst r
  exact cleanGhost_noRace_zero R hr

/-- The discrepancy is physical as well as historical: even the root's
actual choice is not Race. Changing only annotations cannot fix this fact. -/
theorem cleanGhost_root_not_race (R : RFrame) (i : Fin R.m) :
    (cleanGhost R).cfg (rootV R i) ≠ .root .race .toSend .free := by
  rw [cleanGhost_root]
  rcases R.hb with h | h <;> rw [h] <;> intro he <;> cases he

theorem cleanGhost_reserve_zero (R : RFrame) :
    PeriodHIncidenceChoice.choiceRaceReserve (word2 R 0 (cleanGhost R)) = 0 := by
  have hf : ∀ i, word2 R 0 (cleanGhost R) i ≠ .race := (initialService R).dom.frozen
  simp [PeriodHIncidenceChoice.choiceRaceReserve,hf,ofFn_sum_const]

/-- Deleting HasRace would invalidate the old reserve child sum at this
very state: the right side is zero and the unit running cost is positive. -/
theorem cleanGhost_reserve_childSum_false (R : RFrame) :
    ¬ (1 + (List.ofFn (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
      (word2 R 0 (ghostStep2 R (cleanGhost R) (edgeVtx R e))))).sum ≤
      R.n * PeriodHIncidenceChoice.choiceRaceReserve (word2 R 0 (cleanGhost R))) := by
  rw [cleanGhost_reserve_zero, Nat.mul_zero]
  omega

/-- Among lineage states without virtual success, zero generation-0 debt
is necessary and sufficient for the next strict base. This is a stopping
condition, not a claim of an optimal expected preparation cost. -/
theorem next_base_iff_zero_debt (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hn : ¬ VirtualSuccess R 1 s) :
    RoundBase R 1 s ↔ latentDebt2 R 1 s = 0 := by
  exact ⟨fun h => h.zero,fun hz => ⟨hs,debt0_all_entered R 1 s hs hn hz,hz,hn⟩⟩

theorem cleanGhost_preparation_debt (R : RFrame) :
    latentDebt2 R 1 (cleanGhost R) = R.m*(2*R.h-1) := latentDebt2_start R

theorem cleanGhost_preparation_positive (R : RFrame) :
    0 < latentDebt2 R 1 (cleanGhost R) := (initialService R).dom.positive

/-- Reuse the unchanged service, stopping only its duration counter. -/
noncomputable def preparationStep (R : RFrame) (s : Service R) (e : Fin R.n) : StopNode (Service R) :=
  finishService (serviceStep R s e)

theorem preparationStep_bellman (R : RFrame) :
    NatBellmanSuperSolution (preparationStep R) 1 (preparationPotential (servicePotential R)) :=
  preparation_bellman (serviceStep R) (servicePotential R) (service_bellman R)

/-- Every preparation exit supplies either a virtual candidate or the next
actual active round, in the very same physical child. -/
theorem preparation_success_sound (R : RFrame) (s : Service R) (e : Fin R.n)
    (h : preparationStep R s e = .success) :
    VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) ∨
      (RoundBase R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) ∧
        PeriodHIncidenceChoice.HasRace (word2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)))) := by
  classical
  by_cases hv : VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e))
  · exact Or.inl hv
  · apply Or.inr
    have hz : latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) = 0 := by
      apply Classical.byContradiction
      intro hn
      simp [preparationStep,serviceStep,hv,hn,finishService] at h
    exact service_exit R s.idx s.state s.dom _ hv hz

theorem preparation_step_erases (R : RFrame) (s t : Service R) (e : Fin R.n)
    (h : preparationStep R s e = .active t) :
    t.state = ghostStep2 R s.state (edgeVtx R e) := by
  classical
  unfold preparationStep serviceStep at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- Exact initial service credit, excluding all subsequent round costs. -/
theorem preparation_initial_potential (R : RFrame) :
    servicePotential R (initialService R) = R.n*R.m*(2*R.h-1) := by
  change R.n*latentDebt2 R 1 (cleanGhost R) = _
  rw [cleanGhost_preparation_debt]
  exact (Nat.mul_assoc _ _ _).symm

theorem preparation_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (preparationStep R) (.active (initialService R)) T ≤
      R.n^T*(R.n*R.m*(2*R.h-1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (preparationStep R) 1 (preparationPotential (servicePotential R))
    (preparationStep_bellman R) (.active (initialService R)) T
  simpa only [Nat.one_mul,preparationPotential,preparation_initial_potential] using h

/-- The unchanged preparation-plus-round certificate has the original
larger clean-start budget; no tighter bound is inferred from RoundBase 0. -/
theorem physicalCandidate_clean_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.m*R.h+R.n*(2*R.h-1)) :=
  ShortGapGhostComposition2.physicalCandidate_clean_truncatedCost_le R T

theorem physicalCandidate_clean_success_one_minus_inv_factor (R : RFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.m*R.h+R.n*(2*R.h-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.m*R.h+R.n*(2*R.h-1))) :=
  ShortGapGhostComposition2.physicalCandidate_clean_success_one_minus_inv_factor R factor

/-- An active service cannot already be the next strict base. -/
theorem service_not_next_base (R : RFrame) (s : Service R) :
    ¬ RoundBase R (s.idx+1) s.state := by
  intro h
  have hp := s.dom.positive
  rw [h.zero] at hp
  omega

/-- Exact earliest exit condition of this service interface. A candidate
may interrupt preparation before zero debt; otherwise zero debt is required. -/
theorem preparation_success_iff (R : RFrame) (s : Service R) (e : Fin R.n) :
    preparationStep R s e = .success ↔
      VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) ∨
        latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) = 0 := by
  classical
  unfold preparationStep serviceStep
  dsimp only
  split
  · rename_i hv
    simp [finishService,hv]
  · rename_i hv
    split <;> simp_all [finishService]

/-- The larger existing credit is precisely strict-start credit plus
initial service credit; the latch allowance cancels from this comparison. -/
theorem clean_credit_decomposition (R : RFrame) :
    physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) =
      (R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) + servicePotential R (initialService R) := by
  change servicePotential R (initialService R) + R.n*R.m +
    (R.n*R.m+R.n*R.m*(2*R.h-1)) + R.n*(2*R.h-1) = _
  have h := tightBudget_eq R
  omega

/-- Thus the unchanged certificate cannot supply a start-credit bound
with the strict constant. This is not a lower bound on true stopping time. -/
theorem current_clean_credit_exceeds_tight (R : RFrame) :
    R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1) <
      physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) := by
  have hp : 0 < servicePotential R (initialService R) :=
    Nat.mul_pos (Nat.mul_pos (by have := R.hm; omega) R.hh) (initialService R).dom.positive
  rw [clean_credit_decomposition]
  omega

/-- No index-carrying active round can have this unchanged clean state. -/
theorem no_round_with_clean_state (R : RFrame) :
    ¬ (∃ s : Round R, s.state = cleanGhost R) := by
  rintro ⟨s,he⟩
  have hb := s.base
  have hr := s.race
  rw [he] at hb hr
  exact cleanGhost_not_active R s.idx ⟨hb,hr⟩

/-- The initial history is recorded at every root, contradicting the
empty-history premise used by the proposed zero-index shortcut. -/
theorem cleanGhost_history_zero_ne_none (R : RFrame) (i : Fin R.m) :
    (cleanGhost R).hist i 0 ≠ none := by
  change some R.b ≠ none
  intro h
  cases h

end Uniform

#print axioms Uniform.cleanGhost_roundBase_zero
#print axioms Uniform.cleanGhost_roundBase_iff
#print axioms Uniform.predecessor_debt_zero
#print axioms Uniform.generation_mask_zero
#print axioms Uniform.cleanGhost_not_entered_succ
#print axioms Uniform.cleanGhost_noRace_zero
#print axioms Uniform.no_round_with_clean_state
#print axioms Uniform.cleanGhost_root_not_race
#print axioms Uniform.cleanGhost_history_zero_ne_none
#print axioms Uniform.cleanGhost_reserve_childSum_false
#print axioms Uniform.next_base_iff_zero_debt
#print axioms Uniform.cleanGhost_preparation_positive
#print axioms Uniform.preparationStep_bellman
#print axioms Uniform.preparation_success_iff
#print axioms Uniform.preparation_success_sound
#print axioms Uniform.preparation_step_erases
#print axioms Uniform.preparation_initial_potential
#print axioms Uniform.preparation_truncatedCost_le
#print axioms Uniform.clean_credit_decomposition
#print axioms Uniform.current_clean_credit_exceeds_tight
#print axioms Uniform.physicalCandidate_clean_truncatedCost_le
#print axioms Uniform.physicalCandidate_clean_success_one_minus_inv_factor
#print axioms Variable.cleanGhost_roundBase_zero
#print axioms Variable.cleanGhost_roundBase_iff
#print axioms Variable.predecessor_debt_zero
#print axioms Variable.generation_mask_zero
#print axioms Variable.cleanGhost_not_entered_succ
#print axioms Variable.cleanGhost_noRace_zero
#print axioms Variable.no_round_with_clean_state
#print axioms Variable.cleanGhost_root_not_race
#print axioms Variable.cleanGhost_history_zero_ne_none
#print axioms Variable.cleanGhost_reserve_childSum_false
#print axioms Variable.next_base_iff_zero_debt
#print axioms Variable.cleanGhost_preparation_positive
#print axioms Variable.preparationStep_bellman
#print axioms Variable.preparation_success_iff
#print axioms Variable.preparation_success_sound
#print axioms Variable.preparation_step_erases
#print axioms Variable.preparation_initial_potential
#print axioms Variable.preparation_truncatedCost_le
#print axioms Variable.clean_credit_decomposition
#print axioms Variable.current_clean_credit_exceeds_tight
#print axioms Variable.physicalCandidate_clean_truncatedCost_le
#print axioms Variable.physicalCandidate_clean_success_one_minus_inv_factor

end ShortGapCleanBase
