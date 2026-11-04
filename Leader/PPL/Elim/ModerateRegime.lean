import Leader.PPL.Elim.Regimes
import Leader.PPL.Elim.CleanReadyCost
import Leader.PPL.Elim.ControlRows
import Leader.PPL.Elim.BoundaryRegime

/-!
# LD(736): moderate regime repair

The original `ModerateLD` in `LDLocalRegimes.lean` omits the PB-domain
hypothesis used by the paper proof and by the available clean-ready /
controlled-vulnerable machinery.

This file therefore exposes the corrected headline and isolates exactly one
remaining producer: the payload-preserving moderate attempt monitor.  All
generic geometric-restart arithmetic after that producer is proved here.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/--
The single missing File-7 producer.

Its intended implementation is the planned physical monitor

  attacker CR -> target clean dummy -> vulnerable -> live recovery -> retry.

The three clauses after validity are exactly the already-audited attempt
endpoints:
* one-attempt cost at most n * (8a + 7b);
* completed retry mass at most 95/96;
* repeated-kernel cost dominates the raw tagged-deletion cost.

No restart factor is hidden here.  The theorem `moderate_ld_corrected`
below obtains the factor 96 solely from `retry_cost_of_retry_mass`.

The intended discharge uses:
* `cleanReady_cost_proved` for CR preparation;
* `controlRowSpec_proved` for the controlled vulnerable row;
* `weighted_changeOfMeasure_nonretry`,
  `weighted_changeOfMeasure_success`, `compensator_cleared`,
  `moderate_collapse_moment`, and `W1_scaled` for the 95/96 estimate;
* PB closure and `SealedStepSpec` to retain the payload through preparation,
  vulnerable failure, and live recovery.
-/
def ModerateAttemptProducerSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      (C : Config n)
      (hPB : PPL.Elim.PB ring C)
      (F : TripleFrame ring C),
      2 ≤ F.b →
      F.a ≤ 2 * F.b →
      ∃ AttemptState : Type,
        ∃ K : RetryKernel AttemptState (Config n) n,
          K.valid C ∧
          (∀ s, K.valid s → ∀ T,
            attemptCostNumerator K (.active (K.start s)) T ≤
              n ^ T * (n * (8 * F.a + 7 * F.b))) ∧
          (∀ s, K.valid s → ∀ T,
            96 * retryCount K (.active (K.start s)) T ≤
              95 * n ^ T) ∧
          (∀ T,
            costNumerator
                (stepE ring) (TaggedDeleted F) C T ≤
              repeatCostNumerator K C T)

/--
Corrected moderate-regime headline.

The only state-domain premise missing from the old `ModerateLD` is PB.
The consumer already has `2 ≤ leaderCount C`; that fact is logically
redundant once a `TripleFrame ring C` exists, because `F.A.left` and
`F.A.right` are distinct leaders.  It is therefore not repeated here.

`SealedStepSpec` remains explicit because it is still a named physical
interface on current main and is available at the final regime split.
-/
def ModerateLDCorrected : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      (C : Config n),
      PPL.Elim.PB ring C →
      ∀ F : TripleFrame ring C,
        2 ≤ F.b →
        F.a ≤ 2 * F.b →
        ∀ T,
          costNumerator
              (stepE ring) (TaggedDeleted F) C T ≤
            n ^ T * (736 * n * (F.a + F.b))

/--
Everything after the missing attempt producer is unconditional core-Nat
arithmetic.  The factor 96 is supplied by the generic payload-preserving
retry theorem, and the moderate assumption a ≤ 2b is used only in the final
coefficient inequality.
-/
theorem moderate_ld_corrected
    (hAttempt : ModerateAttemptProducerSpec) :
    ModerateLDCorrected := by
  unfold ModerateLDCorrected
  intro hSealed n ring C hPB F hb hab T
  unfold ModerateAttemptProducerSpec at hAttempt
  rcases
      hAttempt hSealed ring C hPB F hb hab with
    ⟨AttemptState, K, hvalid, hcost, hretry, hdom⟩
  have hretry' :
      ∀ s, K.valid s → ∀ t,
        96 * retryCount K (.active (K.start s)) t ≤
          (96 - 1) * n ^ t := by
    intro s hs t
    simpa using hretry s hs t
  have hrepeat :=
    retry_cost_of_retry_mass
      K 96 (n * (8 * F.a + 7 * F.b))
      (by decide)
      hcost hretry' C hvalid T
  have hcoef :
      96 * (8 * F.a + 7 * F.b) ≤
        736 * (F.a + F.b) := by
    omega
  have hcoef' :
      96 * (n * (8 * F.a + 7 * F.b)) ≤
        736 * n * (F.a + F.b) := by
    calc
      96 * (n * (8 * F.a + 7 * F.b)) =
          n * (96 * (8 * F.a + 7 * F.b)) := by
        ac_rfl
      _ ≤ n * (736 * (F.a + F.b)) :=
        Nat.mul_le_mul_left n hcoef
      _ = 736 * n * (F.a + F.b) := by
        ac_rfl
  calc
    costNumerator
        (stepE ring) (TaggedDeleted F) C T ≤
      repeatCostNumerator K C T := hdom T
    _ ≤
      n ^ T *
        (96 * (n * (8 * F.a + 7 * F.b))) := hrepeat
    _ ≤
      n ^ T *
        (736 * n * (F.a + F.b)) :=
      Nat.mul_le_mul_left (n ^ T) hcoef'

/--
The final LD(736) conclusion follows from the corrected moderate theorem
without changing either existing file.

The two CR stage Props are no longer parameters here: `crSweepStep` and
`crReturnStep` are proved on current main and are supplied directly to the
existing long/boundary interface.  The moderate branch receives the PB
premise that was omitted from the old `ModerateLD`.
-/
theorem ld736_costNumerator_of_moderate_corrected
    (hModerate : ModerateLDCorrected)
    (hPhysical : LongBoundaryPhysicalSpec)
    (hSealed : SealedStepSpec)
    {n : Nat} (_hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C) :
    ∀ T : Nat,
      costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (736 * n * (F.a + F.b)) := by
  intro T
  have hbpos : 0 < F.b := by
    rw [← F.B_gap]
    exact F.B.gap_pos
  by_cases hb1 : F.b = 1
  · have hboundary :=
      boundary_ld
        hPhysical crSweepStep crReturnStep hSealed
        ring C hPB h2 F hb1 T
    have hconst : 6 ≤ 736 := by
      decide
    have hcoef :
        6 * n * (F.a + 1) ≤
          736 * n * (F.a + F.b) := by
      rw [hb1]
      calc
        6 * n * (F.a + 1) =
            6 * (n * (F.a + 1)) := by
          simp [Nat.mul_assoc]
        _ ≤ 736 * (n * (F.a + 1)) :=
          Nat.mul_le_mul_right _ hconst
        _ = 736 * n * (F.a + 1) := by
          simp [Nat.mul_assoc]
    exact
      Nat.le_trans hboundary
        (Nat.mul_le_mul_left (n ^ T) hcoef)
  · have hb2 : 2 ≤ F.b := by
      omega
    by_cases hab : F.a ≤ 2 * F.b
    · unfold ModerateLDCorrected at hModerate
      exact
        hModerate hSealed ring C hPB F hb2 hab T
    · have hlongRange :
          2 * F.b + 1 ≤ F.a := by
        omega
      have hlong :=
        long_ld
          hPhysical crSweepStep crReturnStep hSealed
          ring C hPB h2 F hb2 hlongRange T
      have hconst : 112 ≤ 736 := by
        decide
      have hcoef :
          112 * n * (F.a + F.b) ≤
            736 * n * (F.a + F.b) := by
        calc
          112 * n * (F.a + F.b) =
              112 * (n * (F.a + F.b)) := by
            simp [Nat.mul_assoc]
          _ ≤ 736 * (n * (F.a + F.b)) :=
            Nat.mul_le_mul_right _ hconst
          _ = 736 * n * (F.a + F.b) := by
            simp [Nat.mul_assoc]
      exact
        Nat.le_trans hlong
          (Nat.mul_le_mul_left (n ^ T) hcoef)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.moderate_ld_corrected
#print axioms PPL.Convergence.LDLocal.ld736_costNumerator_of_moderate_corrected
