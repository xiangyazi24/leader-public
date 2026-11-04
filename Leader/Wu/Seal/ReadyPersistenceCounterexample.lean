import Leader.Wu.Seal.ReadySuffixHalfMass

/-!
# A transient loaded edge and the exact suffix swap

Readiness itself is not persistent.  On seven sites, `D A C C C C C` is
ready at its first edge, but selecting the outgoing `A C` edge changes it to
`D B D C C C C`.  The home count is unchanged and no ready edge remains.

This is the narrow counterexample that necessitates the first-relevant-clock
involution in `PPartialSealSweepReadySuffixHalfMassSol`.  Swapping that single
outgoing clock to the original loaded edge instead drops the unique home.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepReadyPersistenceCounterexampleSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLStaticDoubleCoverNoGo
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepConcurrentCounterfamilySol
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepReadySuffixHalfMassSol

set_option autoImplicit false

/-- Concrete nontrivial ring for the transient-readiness regression. -/
theorem homeFrontSevenRing : DirectedRing 7 := ⟨by omega⟩

/-- The seven-site word `D A C C C C C`. -/
def homeFrontSevenTransientReadySource :
    Fin 7 → SealSweepHomeFrontSite := fun i =>
  if i = 0 then (false, true)
  else if i = 1 then (true, true)
  else (false, false)

/-- Its endpoint after selecting edge one: `D B D C C C C`. -/
def homeFrontSevenTransientReadyEscaped :
    Fin 7 → SealSweepHomeFrontSite := fun i =>
  if i = 0 then (false, true)
  else if i = 1 then (true, false)
  else if i = 2 then (false, true)
  else (false, false)

private theorem homeFrontFinSeven_cases (i : Fin 7) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by
    omega
  rcases hi with hi | hi | hi | hi | hi | hi | hi
  · exact Or.inl (Fin.ext hi)
  · exact Or.inr (Or.inl (Fin.ext hi))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext hi)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hi))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hi)))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hi))))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext hi))))))

theorem homeFrontSevenTransientReadySource_ready :
    HomeFrontHitReady homeFrontSevenRing
      homeFrontSevenTransientReadySource := by
  exact ⟨0, rfl⟩

theorem homeFrontSevenTransientReady_out_step_eq :
    localStep homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenTransientReadySource 1 =
      homeFrontSevenTransientReadyEscaped := by
  funext i
  rcases homeFrontFinSeven_cases i with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem homeFrontSevenTransientReady_homeCount_eq :
    homeFrontHomeCount homeFrontSevenTransientReadyEscaped =
      homeFrontHomeCount homeFrontSevenTransientReadySource := by
  rfl

theorem homeFrontSevenTransientReadyEscaped_not_ready :
    ¬ HomeFrontHitReady homeFrontSevenRing
      homeFrontSevenTransientReadyEscaped := by
  rintro ⟨edge, hedge⟩
  rcases homeFrontFinSeven_cases edge with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [homeFrontSevenTransientReadyEscaped,
      DirectedRing.rightNeighbor, sealSweepFrontHitsHomePair] at hedge

/-- A loaded edge can disappear in one non-hit step without any home loss. -/
theorem homeFrontSevenTransientReady_not_persistent :
    HomeFrontHitReady homeFrontSevenRing
        homeFrontSevenTransientReadySource ∧
      homeFrontHomeCount
          (localStep homeFrontSevenRing sealSweepHomeFrontPair
            homeFrontSevenTransientReadySource 1) =
        homeFrontHomeCount homeFrontSevenTransientReadySource ∧
      ¬ HomeFrontHitReady homeFrontSevenRing
        (localStep homeFrontSevenRing sealSweepHomeFrontPair
          homeFrontSevenTransientReadySource 1) := by
  refine ⟨homeFrontSevenTransientReadySource_ready, ?_, ?_⟩
  · rw [homeFrontSevenTransientReady_out_step_eq]
    exact homeFrontSevenTransientReady_homeCount_eq
  · rw [homeFrontSevenTransientReady_out_step_eq]
    exact homeFrontSevenTransientReadyEscaped_not_ready

/-- The escaping one-letter word is genuinely bad for the endpoint test. -/
theorem homeFrontSevenTransientReady_out_word_bad :
    homeFrontDropOrReadyEndpointTest homeFrontSevenRing
      homeFrontSevenTransientReadySource
      (runLocalSchedule homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenTransientReadySource [1]) = false := by
  have hrun : runLocalSchedule homeFrontSevenRing sealSweepHomeFrontPair
      homeFrontSevenTransientReadySource [1] =
        homeFrontSevenTransientReadyEscaped := by
    simpa only [runLocalSchedule] using
      homeFrontSevenTransientReady_out_step_eq
  rw [hrun]
  cases htest : homeFrontDropOrReadyEndpointTest homeFrontSevenRing
      homeFrontSevenTransientReadySource
      homeFrontSevenTransientReadyEscaped with
  | false => rfl
  | true =>
      exfalso
      rcases (homeFrontDropOrReadyEndpointTest_spec homeFrontSevenRing
        homeFrontSevenTransientReadySource
        homeFrontSevenTransientReadyEscaped).1 htest with hdrop | hready
      · rw [homeFrontSevenTransientReady_homeCount_eq] at hdrop
        omega
      · exact homeFrontSevenTransientReadyEscaped_not_ready hready

/-- The first-relevant-clock involution replaces that outgoing clock by the
loaded edge zero. -/
theorem homeFrontSevenTransientReady_swap_out_to_hit :
    homeFrontReadySuffixSwap 0
        (homeFrontSevenRing.rightNeighbor 0) ([1] : DetSchedule 7) = [0] := by
  rfl

/-- The swapped one-letter word drops the unique home, so it is good even
though its future trajectory has already diverged from the bad word. -/
theorem homeFrontSevenTransientReady_swapped_word_good :
    homeFrontDropOrReadyEndpointTest homeFrontSevenRing
      homeFrontSevenTransientReadySource
      (runLocalSchedule homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenTransientReadySource
        (homeFrontReadySuffixSwap 0
          (homeFrontSevenRing.rightNeighbor 0) [1])) = true := by
  rw [homeFrontSevenTransientReady_swap_out_to_hit]
  apply (homeFrontDropOrReadyEndpointTest_spec homeFrontSevenRing
    homeFrontSevenTransientReadySource _).2
  left
  simpa only [runLocalSchedule] using
    homeFrontHomeCount_localStep_lt_of_hit homeFrontSevenRing
      (by omega) homeFrontSevenTransientReadySource 0 (by rfl)

/-! ## Three-home positive trace refuting AB-phase ready persistence -/

/-- A quotient configuration contains a blocked `A B` bond. -/
def HomeFrontHasAB
    (ring : DirectedRing 7)
    (X : Fin 7 → SealSweepHomeFrontSite) : Prop :=
  ∃ e : Fin 7,
    X e = (true, true) ∧
      X (ring.rightNeighbor e) = (true, false)

/-- Transparent front count for the concrete seven-site audit. -/
def homeFrontSevenFrontCount
    (X : Fin 7 → SealSweepHomeFrontSite) : Nat :=
  (List.ofFn fun i : Fin 7 => if (X i).2 then 1 else 0).sum

/-- Concrete home/front balance, stated independently of physical reachability. -/
def HomeFrontSevenBalanced
    (X : Fin 7 → SealSweepHomeFrontSite) : Prop :=
  homeFrontSevenFrontCount X = homeFrontHomeCount X

/-- All-closed three-home source `A A C C A C C`. -/
def homeFrontSevenAACCACC : Fin 7 → SealSweepHomeFrontSite := fun i =>
  if i = 0 then (true, true)
  else if i = 1 then (true, true)
  else if i = 4 then (true, true)
  else (false, false)

/-- After edge one: `A B D C A C C`. -/
def homeFrontSevenABDCACC : Fin 7 → SealSweepHomeFrontSite := fun i =>
  if i = 0 then (true, true)
  else if i = 1 then (true, false)
  else if i = 2 then (false, true)
  else if i = 4 then (true, true)
  else (false, false)

/-- After the subsequent edge two: `A B C D A C C`. -/
def homeFrontSevenABCDACC : Fin 7 → SealSweepHomeFrontSite := fun i =>
  if i = 0 then (true, true)
  else if i = 1 then (true, false)
  else if i = 3 then (false, true)
  else if i = 4 then (true, true)
  else (false, false)

/-- After the subsequent edge four: `A B C D B D C`. -/
def homeFrontSevenABCDBDC : Fin 7 → SealSweepHomeFrontSite := fun i =>
  if i = 0 then (true, true)
  else if i = 1 then (true, false)
  else if i = 3 then (false, true)
  else if i = 4 then (true, false)
  else if i = 5 then (false, true)
  else (false, false)

/-- Exact physical section of the all-closed three-home source. -/
def sealSweepPhysicalSevenAACCACC (kappa tau : Nat) :
    SealSweepConfig 7 OverlayNoGoPsi kappa tau := fun i =>
  sealSweepHomeFrontSection kappa tau (homeFrontSevenAACCACC i)

theorem sealSweepPhysicalSevenAACCACC_projection (kappa tau : Nat) :
    sealSweepHomeFrontConfig
        (sealSweepPhysicalSevenAACCACC kappa tau) =
      homeFrontSevenAACCACC := by
  funext i
  exact sealSweepHomeFrontSite_section kappa tau
    (homeFrontSevenAACCACC i)

theorem sealSweepPhysicalSevenAACCACC_allClosed (kappa tau : Nat) :
    SealSweepAllClosed (sealSweepPhysicalSevenAACCACC kappa tau) := by
  intro i
  rcases homeFrontFinSeven_cases i with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem sealSweepPhysicalSevenAACCACC_positive (kappa tau : Nat) :
    0 < sealSweepLeaderCount
      (sealSweepPhysicalSevenAACCACC kappa tau) := by
  apply (sealSweep_hasLeader_iff_leaderCount_pos _).1
  exact ⟨0, rfl⟩

/-- The three-home source belongs to the exact positive quotient image. -/
theorem homeFrontSevenAACCACC_positiveState (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      homeFrontSevenRing homeFrontSevenAACCACC := by
  refine ⟨sealSweepPhysicalSevenAACCACC kappa tau, ?_,
    sealSweepPhysicalSevenAACCACC_projection kappa tau⟩
  exact allClosedPositive_mem_positiveDescendant homeFrontSevenRing _
    ⟨sealSweepPhysicalSevenAACCACC_allClosed kappa tau,
      sealSweepPhysicalSevenAACCACC_positive kappa tau⟩

theorem homeFrontSevenAACCACC_edge_one :
    localStep homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenAACCACC 1 = homeFrontSevenABDCACC := by
  funext i
  rcases homeFrontFinSeven_cases i with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem homeFrontSevenABDCACC_edge_two :
    localStep homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenABDCACC 2 = homeFrontSevenABCDACC := by
  funext i
  rcases homeFrontFinSeven_cases i with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem homeFrontSevenABCDACC_edge_four :
    localStep homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenABCDACC 4 = homeFrontSevenABCDBDC := by
  funext i
  rcases homeFrontFinSeven_cases i with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The full quotient trace is exactly `1,2,4`. -/
theorem homeFrontSeven_threeHome_trace :
    runLocalSchedule homeFrontSevenRing sealSweepHomeFrontPair
        homeFrontSevenAACCACC [1, 2, 4] =
      homeFrontSevenABCDBDC := by
  simp only [runLocalSchedule]
  rw [homeFrontSevenAACCACC_edge_one,
    homeFrontSevenABDCACC_edge_two,
    homeFrontSevenABCDACC_edge_four]

theorem homeFrontSevenABDCACC_hasAB :
    HomeFrontHasAB homeFrontSevenRing homeFrontSevenABDCACC := by
  exact ⟨0, rfl, rfl⟩

theorem homeFrontSevenABCDACC_hasAB :
    HomeFrontHasAB homeFrontSevenRing homeFrontSevenABCDACC := by
  exact ⟨0, rfl, rfl⟩

theorem homeFrontSevenABCDBDC_hasAB :
    HomeFrontHasAB homeFrontSevenRing homeFrontSevenABCDBDC := by
  exact ⟨0, rfl, rfl⟩

theorem homeFrontSevenABDCACC_not_ready :
    ¬ HomeFrontHitReady homeFrontSevenRing homeFrontSevenABDCACC := by
  intro h
  obtain ⟨edge, hedge⟩ := h
  rcases homeFrontFinSeven_cases edge with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change false = true at hedge
    contradiction

theorem homeFrontSevenABCDACC_ready :
    HomeFrontHitReady homeFrontSevenRing homeFrontSevenABCDACC := by
  exact ⟨3, rfl⟩

theorem homeFrontSevenABCDBDC_not_ready :
    ¬ HomeFrontHitReady homeFrontSevenRing homeFrontSevenABCDBDC := by
  intro h
  obtain ⟨edge, hedge⟩ := h
  rcases homeFrontFinSeven_cases edge with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change false = true at hedge
    contradiction

theorem homeFrontSevenAACCACC_homeCount :
    homeFrontHomeCount homeFrontSevenAACCACC = 3 := by
  rfl

theorem homeFrontSevenABDCACC_homeCount :
    homeFrontHomeCount homeFrontSevenABDCACC = 3 := by
  rfl

theorem homeFrontSevenABCDACC_homeCount :
    homeFrontHomeCount homeFrontSevenABCDACC = 3 := by
  rfl

theorem homeFrontSevenABCDBDC_homeCount :
    homeFrontHomeCount homeFrontSevenABCDBDC = 3 := by
  rfl

theorem homeFrontSevenABDCACC_balanced :
    HomeFrontSevenBalanced homeFrontSevenABDCACC := by
  rfl

/-- The first `A C` move reaches a nonready, balanced, three-home `A B` state
inside the exact positive image. -/
theorem homeFrontSevenABDCACC_positive_certificate (kappa tau : Nat) :
    HomeFrontHasAB homeFrontSevenRing homeFrontSevenABDCACC ∧
      ¬ HomeFrontHitReady homeFrontSevenRing homeFrontSevenABDCACC ∧
      HomeFrontSevenBalanced homeFrontSevenABDCACC ∧
      homeFrontHomeCount homeFrontSevenABDCACC = 3 ∧
      SealSweepPositiveHomeFrontState
        (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
        homeFrontSevenRing homeFrontSevenABDCACC := by
  refine ⟨homeFrontSevenABDCACC_hasAB,
    homeFrontSevenABDCACC_not_ready,
    homeFrontSevenABDCACC_balanced,
    homeFrontSevenABDCACC_homeCount, ?_⟩
  have hstep := positiveHomeFrontState_localStep
    (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
    homeFrontSevenRing homeFrontSevenAACCACC
    (homeFrontSevenAACCACC_positiveState kappa tau) 1
  rw [homeFrontSevenAACCACC_edge_one] at hstep
  exact hstep

/-- In the positive three-home `A B` phase, edge two creates a separate
loaded edge `D A`; edge four then removes that readiness without lowering the
home count.  The original blocked `A B` bond persists throughout. -/
theorem homeFrontSeven_AB_phase_ready_not_persistent :
    HomeFrontHasAB homeFrontSevenRing homeFrontSevenABDCACC ∧
      ¬ HomeFrontHitReady homeFrontSevenRing homeFrontSevenABDCACC ∧
      localStep homeFrontSevenRing sealSweepHomeFrontPair
          homeFrontSevenABDCACC 2 = homeFrontSevenABCDACC ∧
      HomeFrontHasAB homeFrontSevenRing homeFrontSevenABCDACC ∧
      HomeFrontHitReady homeFrontSevenRing homeFrontSevenABCDACC ∧
      localStep homeFrontSevenRing sealSweepHomeFrontPair
          homeFrontSevenABCDACC 4 = homeFrontSevenABCDBDC ∧
      homeFrontHomeCount homeFrontSevenABCDBDC =
        homeFrontHomeCount homeFrontSevenABCDACC ∧
      HomeFrontHasAB homeFrontSevenRing homeFrontSevenABCDBDC ∧
      ¬ HomeFrontHitReady homeFrontSevenRing homeFrontSevenABCDBDC := by
  exact ⟨homeFrontSevenABDCACC_hasAB,
    homeFrontSevenABDCACC_not_ready,
    homeFrontSevenABDCACC_edge_two,
    homeFrontSevenABCDACC_hasAB,
    homeFrontSevenABCDACC_ready,
    homeFrontSevenABCDACC_edge_four,
    homeFrontSevenABCDBDC_homeCount.trans
      homeFrontSevenABCDACC_homeCount.symm,
    homeFrontSevenABCDBDC_hasAB,
    homeFrontSevenABCDBDC_not_ready⟩

/-! ## The unbounded `C`-padding family -/

variable {m : Nat}

/-- All-closed three-home source `A A C C A C C ... C`. -/
def homeFrontPaddedAACCACC (m : Nat) (hm : 7 ≤ m) :
    Fin m → SealSweepHomeFrontSite := fun i =>
  if i.val = 0 then (true, true)
  else if i.val = 1 then (true, true)
  else if i.val = 4 then (true, true)
  else (false, false)

/-- First padded intermediate `A B D C A C C ... C`. -/
def homeFrontPaddedABDCACC (m : Nat) (hm : 7 ≤ m) :
    Fin m → SealSweepHomeFrontSite := fun i =>
  if i.val = 0 then (true, true)
  else if i.val = 1 then (true, false)
  else if i.val = 2 then (false, true)
  else if i.val = 4 then (true, true)
  else (false, false)

/-- Ready padded intermediate `A B C D A C C ... C`. -/
def homeFrontPaddedABCDACC (m : Nat) (hm : 7 ≤ m) :
    Fin m → SealSweepHomeFrontSite := fun i =>
  if i.val = 0 then (true, true)
  else if i.val = 1 then (true, false)
  else if i.val = 3 then (false, true)
  else if i.val = 4 then (true, true)
  else (false, false)

/-- Escaped padded endpoint `A B C D B D C ... C`. -/
def homeFrontPaddedABCDBDC (m : Nat) (hm : 7 ≤ m) :
    Fin m → SealSweepHomeFrontSite := fun i =>
  if i.val = 0 then (true, true)
  else if i.val = 1 then (true, false)
  else if i.val = 3 then (false, true)
  else if i.val = 4 then (true, false)
  else if i.val = 5 then (false, true)
  else (false, false)

private theorem padded_rightNeighbor_one
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ring.rightNeighbor (⟨1, by omega⟩ : Fin m) =
      (⟨2, by omega⟩ : Fin m) := by
  apply Fin.ext
  change (1 + 1) % m = 2
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem padded_rightNeighbor_two
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ring.rightNeighbor (⟨2, by omega⟩ : Fin m) =
      (⟨3, by omega⟩ : Fin m) := by
  apply Fin.ext
  change (2 + 1) % m = 3
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem padded_rightNeighbor_four
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ring.rightNeighbor (⟨4, by omega⟩ : Fin m) =
      (⟨5, by omega⟩ : Fin m) := by
  apply Fin.ext
  change (4 + 1) % m = 5
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem padded_rightNeighbor_zero
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ring.rightNeighbor (⟨0, by omega⟩ : Fin m) =
      (⟨1, by omega⟩ : Fin m) := by
  apply Fin.ext
  change (0 + 1) % m = 1
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem padded_rightNeighbor_three
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ring.rightNeighbor (⟨3, by omega⟩ : Fin m) =
      (⟨4, by omega⟩ : Fin m) := by
  apply Fin.ext
  change (3 + 1) % m = 4
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem padded_rightNeighbor_five
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ring.rightNeighbor (⟨5, by omega⟩ : Fin m) =
      (⟨6, by omega⟩ : Fin m) := by
  apply Fin.ext
  change (5 + 1) % m = 6
  rw [Nat.mod_eq_of_lt (by omega)]

theorem homeFrontPadded_step_one
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    localStep ring sealSweepHomeFrontPair
        (homeFrontPaddedAACCACC m hm) (⟨1, by omega⟩ : Fin m) =
      homeFrontPaddedABDCACC m hm := by
  let p1 : Fin m := ⟨1, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  have h12 : ring.rightNeighbor p1 = p2 :=
    padded_rightNeighbor_one ring hm
  have hpair :
      sealSweepHomeFrontPair
          (homeFrontPaddedAACCACC m hm p1)
          (homeFrontPaddedAACCACC m hm p2) =
        ((true, false), (false, true)) := by
    rfl
  change localStep ring sealSweepHomeFrontPair
      (homeFrontPaddedAACCACC m hm) p1 =
    homeFrontPaddedABDCACC m hm
  funext i
  simp only [localStep]
  rw [h12, hpair]
  by_cases hi1 : i = p1
  · subst i
    simp [p1, p2, homeFrontPaddedABDCACC]
  · by_cases hi2 : i = p2
    · subst i
      have h21 : p2 ≠ p1 := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [p1, p2] at hv
        omega
      simp [hi1, h21, p1, p2, homeFrontPaddedABDCACC]
    · have hv1 : i.val ≠ 1 := by
        intro h
        apply hi1
        apply Fin.ext
        simpa [p1] using h
      have hv2 : i.val ≠ 2 := by
        intro h
        apply hi2
        apply Fin.ext
        simpa [p2] using h
      simp [hi1, hi2, homeFrontPaddedAACCACC,
        homeFrontPaddedABDCACC, hv1, hv2]

theorem homeFrontPadded_step_two
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    localStep ring sealSweepHomeFrontPair
        (homeFrontPaddedABDCACC m hm) (⟨2, by omega⟩ : Fin m) =
      homeFrontPaddedABCDACC m hm := by
  let p2 : Fin m := ⟨2, by omega⟩
  let p3 : Fin m := ⟨3, by omega⟩
  have h23 : ring.rightNeighbor p2 = p3 :=
    padded_rightNeighbor_two ring hm
  have hpair :
      sealSweepHomeFrontPair
          (homeFrontPaddedABDCACC m hm p2)
          (homeFrontPaddedABDCACC m hm p3) =
        ((false, false), (false, true)) := by
    rfl
  change localStep ring sealSweepHomeFrontPair
      (homeFrontPaddedABDCACC m hm) p2 =
    homeFrontPaddedABCDACC m hm
  funext i
  simp only [localStep]
  rw [h23, hpair]
  by_cases hi2 : i = p2
  · subst i
    simp [p2, p3, homeFrontPaddedABCDACC]
  · by_cases hi3 : i = p3
    · subst i
      have h32 : p3 ≠ p2 := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [p2, p3] at hv
        omega
      simp [hi2, h32, p2, p3, homeFrontPaddedABCDACC]
    · have hv2 : i.val ≠ 2 := by
        intro h
        apply hi2
        apply Fin.ext
        simpa [p2] using h
      have hv3 : i.val ≠ 3 := by
        intro h
        apply hi3
        apply Fin.ext
        simpa [p3] using h
      simp [hi2, hi3, homeFrontPaddedABDCACC,
        homeFrontPaddedABCDACC, hv2, hv3]

theorem homeFrontPadded_step_four
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    localStep ring sealSweepHomeFrontPair
        (homeFrontPaddedABCDACC m hm) (⟨4, by omega⟩ : Fin m) =
      homeFrontPaddedABCDBDC m hm := by
  let p4 : Fin m := ⟨4, by omega⟩
  let p5 : Fin m := ⟨5, by omega⟩
  have h45 : ring.rightNeighbor p4 = p5 :=
    padded_rightNeighbor_four ring hm
  have hpair :
      sealSweepHomeFrontPair
          (homeFrontPaddedABCDACC m hm p4)
          (homeFrontPaddedABCDACC m hm p5) =
        ((true, false), (false, true)) := by
    rfl
  change localStep ring sealSweepHomeFrontPair
      (homeFrontPaddedABCDACC m hm) p4 =
    homeFrontPaddedABCDBDC m hm
  funext i
  simp only [localStep]
  rw [h45, hpair]
  by_cases hi4 : i = p4
  · subst i
    simp [p4, p5, homeFrontPaddedABCDBDC]
  · by_cases hi5 : i = p5
    · subst i
      have h54 : p5 ≠ p4 := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [p4, p5] at hv
        omega
      simp [hi4, h54, p4, p5, homeFrontPaddedABCDBDC]
    · have hv4 : i.val ≠ 4 := by
        intro h
        apply hi4
        apply Fin.ext
        simpa [p4] using h
      have hv5 : i.val ≠ 5 := by
        intro h
        apply hi5
        apply Fin.ext
        simpa [p5] using h
      simp [hi4, hi5, homeFrontPaddedABCDACC,
        homeFrontPaddedABCDBDC, hv4, hv5]

/-- The padded family keeps an explicit blocked `A B` bond. -/
def PaddedHomeFrontHasAB
    (ring : DirectedRing m)
    (X : Fin m → SealSweepHomeFrontSite) : Prop :=
  ∃ e : Fin m,
    X e = (true, true) ∧
      X (ring.rightNeighbor e) = (true, false)

theorem homeFrontPaddedABDCACC_hasAB
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    PaddedHomeFrontHasAB ring (homeFrontPaddedABDCACC m hm) := by
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  have h01 : ring.rightNeighbor p0 = p1 :=
    padded_rightNeighbor_zero ring hm
  refine ⟨p0, ?_, ?_⟩
  · rfl
  · rw [h01]
    rfl

theorem homeFrontPaddedABCDACC_hasAB
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    PaddedHomeFrontHasAB ring (homeFrontPaddedABCDACC m hm) := by
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  have h01 : ring.rightNeighbor p0 = p1 :=
    padded_rightNeighbor_zero ring hm
  refine ⟨p0, ?_, ?_⟩
  · rfl
  · rw [h01]
    rfl

theorem homeFrontPaddedABCDBDC_hasAB
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    PaddedHomeFrontHasAB ring (homeFrontPaddedABCDBDC m hm) := by
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  have h01 : ring.rightNeighbor p0 = p1 :=
    padded_rightNeighbor_zero ring hm
  refine ⟨p0, ?_, ?_⟩
  · rfl
  · rw [h01]
    rfl

theorem homeFrontPaddedABDCACC_not_ready
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ¬ HomeFrontHitReady ring (homeFrontPaddedABDCACC m hm) := by
  rintro ⟨edge, hedge⟩
  by_cases h0 : edge.val = 0
  · have he : edge = (⟨0, by omega⟩ : Fin m) := Fin.ext h0
    rw [he, padded_rightNeighbor_zero ring hm] at hedge
    change false = true at hedge
    contradiction
  · by_cases h2 : edge.val = 2
    · have he : edge = (⟨2, by omega⟩ : Fin m) := Fin.ext h2
      rw [he, padded_rightNeighbor_two ring hm] at hedge
      change false = true at hedge
      contradiction
    · by_cases h4 : edge.val = 4
      · have he : edge = (⟨4, by omega⟩ : Fin m) := Fin.ext h4
        rw [he, padded_rightNeighbor_four ring hm] at hedge
        change false = true at hedge
        contradiction
      · have hfront :
          (homeFrontPaddedABDCACC m hm edge).2 = false := by
          simp [homeFrontPaddedABDCACC, h0, h2, h4]
        simp [sealSweepFrontHitsHomePair, hfront] at hedge

theorem homeFrontPaddedABCDACC_ready
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    HomeFrontHitReady ring (homeFrontPaddedABCDACC m hm) := by
  let p3 : Fin m := ⟨3, by omega⟩
  let p4 : Fin m := ⟨4, by omega⟩
  have h34 : ring.rightNeighbor p3 = p4 :=
    padded_rightNeighbor_three ring hm
  refine ⟨p3, ?_⟩
  rw [h34]
  rfl

theorem homeFrontPaddedABCDBDC_not_ready
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    ¬ HomeFrontHitReady ring (homeFrontPaddedABCDBDC m hm) := by
  rintro ⟨edge, hedge⟩
  by_cases h0 : edge.val = 0
  · have he : edge = (⟨0, by omega⟩ : Fin m) := Fin.ext h0
    rw [he, padded_rightNeighbor_zero ring hm] at hedge
    change false = true at hedge
    contradiction
  · by_cases h3 : edge.val = 3
    · have he : edge = (⟨3, by omega⟩ : Fin m) := Fin.ext h3
      rw [he, padded_rightNeighbor_three ring hm] at hedge
      change false = true at hedge
      contradiction
    · by_cases h5 : edge.val = 5
      · have he : edge = (⟨5, by omega⟩ : Fin m) := Fin.ext h5
        rw [he, padded_rightNeighbor_five ring hm] at hedge
        change false = true at hedge
        contradiction
      · have hfront :
          (homeFrontPaddedABCDBDC m hm edge).2 = false := by
          simp [homeFrontPaddedABCDBDC, h0, h3, h5]
        simp [sealSweepFrontHitsHomePair, hfront] at hedge

theorem homeFrontPadded_same_home_bits
    (hm : 7 ≤ m) :
    ∀ i : Fin m,
      (homeFrontPaddedABDCACC m hm i).1 =
        (homeFrontPaddedABCDBDC m hm i).1 := by
  intro i
  by_cases h0 : i.val = 0 <;>
    by_cases h1 : i.val = 1 <;>
      by_cases h4 : i.val = 4 <;>
        simp [homeFrontPaddedABDCACC, homeFrontPaddedABCDBDC,
          h0, h1, h4]

/-- Exact padded quotient trace `1,2,4`. -/
theorem homeFrontPadded_threeHome_trace
    (ring : DirectedRing m) (hm : 7 ≤ m) :
    runLocalSchedule ring sealSweepHomeFrontPair
        (homeFrontPaddedAACCACC m hm)
        [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩] =
      homeFrontPaddedABCDBDC m hm := by
  simp only [runLocalSchedule]
  rw [homeFrontPadded_step_one ring hm,
    homeFrontPadded_step_two ring hm,
    homeFrontPadded_step_four ring hm]

/-- Exact physical section of the padded all-closed three-home source. -/
def sealSweepPhysicalPaddedAACCACC
    (m : Nat) (hm : 7 ≤ m) (kappa tau : Nat) :
    SealSweepConfig m OverlayNoGoPsi kappa tau := fun i =>
  sealSweepHomeFrontSection kappa tau (homeFrontPaddedAACCACC m hm i)

theorem sealSweepPhysicalPaddedAACCACC_projection
    (hm : 7 ≤ m) (kappa tau : Nat) :
    sealSweepHomeFrontConfig
        (sealSweepPhysicalPaddedAACCACC m hm kappa tau) =
      homeFrontPaddedAACCACC m hm := by
  funext i
  exact sealSweepHomeFrontSite_section kappa tau
    (homeFrontPaddedAACCACC m hm i)

theorem sealSweepPhysicalPaddedAACCACC_allClosed
    (hm : 7 ≤ m) (kappa tau : Nat) :
    SealSweepAllClosed
      (sealSweepPhysicalPaddedAACCACC m hm kappa tau) := by
  intro i
  by_cases h0 : i.val = 0 <;>
    by_cases h1 : i.val = 1 <;>
      by_cases h4 : i.val = 4 <;>
        simp [sealSweepPhysicalPaddedAACCACC,
          homeFrontPaddedAACCACC, sealSweepHomeFrontSection,
          exactLS, exactFS, h0, h1, h4]

theorem sealSweepPhysicalPaddedAACCACC_positive
    (hm : 7 ≤ m) (kappa tau : Nat) :
    0 < sealSweepLeaderCount
      (sealSweepPhysicalPaddedAACCACC m hm kappa tau) := by
  apply (sealSweep_hasLeader_iff_leaderCount_pos _).1
  refine ⟨(⟨0, by omega⟩ : Fin m), ?_⟩
  rfl

/-- Every padded first intermediate lies in the exact positive quotient
image: it is one local step from an all-closed positive physical source. -/
theorem homeFrontPaddedABDCACC_positiveState
    (ring : DirectedRing m) (hm : 7 ≤ m) (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      ring (homeFrontPaddedABDCACC m hm) := by
  have hsource : SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      ring (homeFrontPaddedAACCACC m hm) := by
    refine ⟨sealSweepPhysicalPaddedAACCACC m hm kappa tau, ?_,
      sealSweepPhysicalPaddedAACCACC_projection hm kappa tau⟩
    exact allClosedPositive_mem_positiveDescendant ring _
      ⟨sealSweepPhysicalPaddedAACCACC_allClosed hm kappa tau,
        sealSweepPhysicalPaddedAACCACC_positive hm kappa tau⟩
  have hstep := positiveHomeFrontState_localStep
    (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
    ring (homeFrontPaddedAACCACC m hm) hsource
      (⟨1, by omega⟩ : Fin m)
  rw [homeFrontPadded_step_one ring hm] at hstep
  exact hstep

/-- Unbounded reachable regression.  For every ring size at least seven,
the fixed `A B` bond survives while readiness appears and then disappears;
the home bits are identical before and after the two-step escape. -/
theorem homeFrontPadded_AB_phase_ready_not_persistent
    (ring : DirectedRing m) (hm : 7 ≤ m) (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
        (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
        ring (homeFrontPaddedABDCACC m hm) ∧
      PaddedHomeFrontHasAB ring (homeFrontPaddedABDCACC m hm) ∧
      ¬ HomeFrontHitReady ring (homeFrontPaddedABDCACC m hm) ∧
      localStep ring sealSweepHomeFrontPair
          (homeFrontPaddedABDCACC m hm) (⟨2, by omega⟩ : Fin m) =
        homeFrontPaddedABCDACC m hm ∧
      PaddedHomeFrontHasAB ring (homeFrontPaddedABCDACC m hm) ∧
      HomeFrontHitReady ring (homeFrontPaddedABCDACC m hm) ∧
      localStep ring sealSweepHomeFrontPair
          (homeFrontPaddedABCDACC m hm) (⟨4, by omega⟩ : Fin m) =
        homeFrontPaddedABCDBDC m hm ∧
      PaddedHomeFrontHasAB ring (homeFrontPaddedABCDBDC m hm) ∧
      ¬ HomeFrontHitReady ring (homeFrontPaddedABCDBDC m hm) ∧
      (∀ i : Fin m,
        (homeFrontPaddedABDCACC m hm i).1 =
          (homeFrontPaddedABCDBDC m hm i).1) := by
  exact ⟨homeFrontPaddedABDCACC_positiveState ring hm kappa tau,
    homeFrontPaddedABDCACC_hasAB ring hm,
    homeFrontPaddedABDCACC_not_ready ring hm,
    homeFrontPadded_step_two ring hm,
    homeFrontPaddedABCDACC_hasAB ring hm,
    homeFrontPaddedABCDACC_ready ring hm,
    homeFrontPadded_step_four ring hm,
    homeFrontPaddedABCDBDC_hasAB ring hm,
    homeFrontPaddedABCDBDC_not_ready ring hm,
    homeFrontPadded_same_home_bits hm⟩

#print axioms homeFrontSevenTransientReady_not_persistent
#print axioms homeFrontSevenTransientReady_out_word_bad
#print axioms homeFrontSevenTransientReady_swapped_word_good
#print axioms homeFrontSevenAACCACC_positiveState
#print axioms homeFrontSevenABDCACC_positive_certificate
#print axioms homeFrontSeven_AB_phase_ready_not_persistent
#print axioms homeFrontPaddedABDCACC_positiveState
#print axioms homeFrontPadded_AB_phase_ready_not_persistent

end PPartialSealSweepReadyPersistenceCounterexampleSol
end PPLLCompleteMultiLeaderCleanup
