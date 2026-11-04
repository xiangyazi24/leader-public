import Leader.PPL.Elim.TwoLeaderSealedProduct
import Leader.PPL.Elim.LocalDeletionCounting

/-!
# LD(736): boundary and long-attacker regimes

This is Wave 5 File 7, part 1.  File 4 supplies the corrected File-3 phase
interface, including current strict-interior followers in `PhaseHolds`.
The File-2 drain and repair obligations are already discharged by
`crDrainStep` and `crRepairStep`; `CRSweepStepSpec` and
`CRReturnStepSpec` remain explicit hypotheses.

The absent File-5 physical monitor is isolated once, in
`LongBoundaryPhysicalSpec`.  Its long-regime conjunct stops at the exact
payload-preserving `RetryKernel` interface, so the geometric restart is
proved here with File 6 rather than hidden in the hypothesis.  Any eventual
File-5 implementation discharging that conjunct must use the corrected
`VulnerableState` invariant from the §7 amendment, in particular
`targetUnshielded : (cfg F.j).shield = false`.

The moderate regime is intentionally only a named hypothesis in this part.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The moderate-regime headline from the File-7 plan, packaged as the named
hypothesis requested for this part. -/
def ModerateLD : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    (C : Config n) (F : TripleFrame ring C),
    2 ≤ F.b →
    F.a ≤ 2 * F.b →
    ∀ T,
      costNumerator (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (736 * n * (F.a + F.b))

/-- The one remaining physical/composition obligation for this part.

The long conjunct is exactly the attempt-level endpoint needed by File 6:
uniform one-attempt cost `7*n*(a+b)`, completed retry mass at most
`15/16`, and domination of the physical first-hit cost by repeated-kernel
cost.  The `16` restart factor is *not* assumed: `long_ld` derives it with
`retry_cost_of_retry_mass`.

The boundary conjunct is the no-retry composition of target CR, attacker clean
live hit, and the literal one-edge target deletion.  It is isolated here
because File 3's `cleanLiveHit_cost` and File 5's monitor layer are not on
main yet.

Both conjuncts explicitly consume the corrected File-2 sweep/return
hypotheses and File-3 `SealedStepSpec`. -/
def LongBoundaryPhysicalSpec : Prop :=
  ∀ (hSweep : CRSweepStepSpec)
    (hReturn : CRReturnStepSpec)
    (hSealed : SealedStepSpec),
    (∀ {n : Nat} (ring : DirectedRing n)
      (C : Config n)
      (hPB : PPL.Elim.PB ring C)
      (h2 : 2 ≤ PPL.Elim.leaderCount C)
      (F : TripleFrame ring C),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      ∃ AttemptState : Type,
        ∃ K : RetryKernel AttemptState (Config n) n,
          K.valid C ∧
          (∀ s, K.valid s → ∀ T,
            attemptCostNumerator K (.active (K.start s)) T ≤
              n ^ T * (7 * n * (F.a + F.b))) ∧
          (∀ s, K.valid s → ∀ T,
            16 * retryCount K (.active (K.start s)) T ≤
              15 * n ^ T) ∧
          (∀ T,
            costNumerator (stepE ring) (TaggedDeleted F) C T ≤
              repeatCostNumerator K C T)) ∧
    (∀ {n : Nat} (ring : DirectedRing n)
      (C : Config n)
      (hPB : PPL.Elim.PB ring C)
      (h2 : 2 ≤ PPL.Elim.leaderCount C)
      (F : TripleFrame ring C),
      F.b = 1 →
      ∀ T,
        costNumerator (stepE ring) (TaggedDeleted F) C T ≤
          n ^ T * (6 * n * (F.a + 1)))

/-! ## Long-attacker regime -/

theorem long_ld
    (hPhysical : LongBoundaryPhysicalSpec)
    (hSweep : CRSweepStepSpec)
    (hReturn : CRReturnStepSpec)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C)
    (hb : 2 ≤ F.b) (hab : 2 * F.b + 1 ≤ F.a) :
    ∀ T,
      costNumerator (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (112 * n * (F.a + F.b)) := by
  intro T
  unfold LongBoundaryPhysicalSpec at hPhysical
  rcases
      hPhysical hSweep hReturn hSealed |>.1
        ring C hPB h2 F hb hab with
    ⟨AttemptState, K, hvalid, hcost, hretry, hdom⟩
  have hretry' :
      ∀ s, K.valid s → ∀ t,
        16 * retryCount K (.active (K.start s)) t ≤
          (16 - 1) * n ^ t := by
    intro s hs t
    simpa using hretry s hs t
  have hrepeat :=
    retry_cost_of_retry_mass
      K 16 (7 * n * (F.a + F.b))
      (by decide)
      hcost hretry' C hvalid T
  have hcoef :
      16 * (7 * n * (F.a + F.b)) =
        112 * n * (F.a + F.b) := by
    rw [Nat.mul_assoc 7 n, Nat.mul_assoc 112 n, ← Nat.mul_assoc 16 7]
  calc
    costNumerator (stepE ring) (TaggedDeleted F) C T
        ≤ repeatCostNumerator K C T := hdom T
    _ ≤ n ^ T * (16 * (7 * n * (F.a + F.b))) := hrepeat
    _ = n ^ T * (112 * n * (F.a + F.b)) := by
      rw [hcoef]

/-! ## Boundary b=1 -/

theorem boundary_ld
    (hPhysical : LongBoundaryPhysicalSpec)
    (hSweep : CRSweepStepSpec)
    (hReturn : CRReturnStepSpec)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C)
    (hb : F.b = 1) :
    ∀ T,
      costNumerator (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (6 * n * (F.a + 1)) := by
  unfold LongBoundaryPhysicalSpec at hPhysical
  exact
    hPhysical hSweep hReturn hSealed |>.2
      ring C hPB h2 F hb

/-! ## Final integral regime split -/

theorem ld736_costNumerator
    (hModerate : ModerateLD)
    (hPhysical : LongBoundaryPhysicalSpec)
    (hSweep : CRSweepStepSpec)
    (hReturn : CRReturnStepSpec)
    (hSealed : SealedStepSpec)
    {n : Nat} (_hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C) :
    ∀ T : Nat,
      K2ArbitraryElimination.FiniteAccounting.costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (736 * n * (F.a + F.b)) := by
  intro T
  have hbpos : 0 < F.b := by
    rw [← F.B_gap]
    exact F.B.gap_pos
  by_cases hb1 : F.b = 1
  · have hboundary :=
      boundary_ld
        hPhysical hSweep hReturn hSealed
        ring C hPB h2 F hb1 T
    have hconst : 6 ≤ 736 := by decide
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
    · unfold ModerateLD at hModerate
      exact hModerate ring C F hb2 hab T
    · have hlongRange : 2 * F.b + 1 ≤ F.a := by
        omega
      have hlong :=
        long_ld
          hPhysical hSweep hReturn hSealed
          ring C hPB h2 F hb2 hlongRange T
      have hconst : 112 ≤ 736 := by decide
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

#print axioms PPL.Convergence.LDLocal.long_ld
#print axioms PPL.Convergence.LDLocal.boundary_ld
#print axioms PPL.Convergence.LDLocal.ld736_costNumerator

end PPL.Convergence.LDLocal
