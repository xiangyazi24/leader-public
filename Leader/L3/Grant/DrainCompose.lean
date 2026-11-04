import Leader.L3.Grant.DrainWarm

/-!
# Stopped-prefix cost composition for the canonical grant drain

Different stage targets use the same physical transition and same
scheduler. First hitting the intermediate target does not require
that target to remain closed. The final result is conditional on
the explicitly named, presently unproved stage interfaces.
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The true stopped-prefix comparison, for any chain and targets.
An exact intermediate-hit endpoint pays at most the uniform second
stage cost. No independence between the two clocks is assumed. -/
theorem grantDrainComposeIntermediateCost
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (Intermediate Final : X → Prop) (B : Nat)
    (hAfter : ∀ y : X, Intermediate y →
      ∀ T : Nat, costNumerator next Final y T ≤ n ^ T * B) :
    ∀ T : Nat, ∀ x : X,
      costNumerator next Final x T ≤
        costNumerator next Intermediate x T + n ^ T * B := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      simp [costNumerator_zero]
  | succ T ih =>
      intro x
      by_cases hFinal : Final x
      · rw [costNumerator_terminal next Final x hFinal (T + 1)]
        exact Nat.zero_le _
      · by_cases hIntermediate : Intermediate x
        · calc
            costNumerator next Final x (T + 1) ≤
                n ^ (T + 1) * B := hAfter x hIntermediate (T + 1)
            _ ≤ costNumerator next Intermediate x (T + 1) +
                  n ^ (T + 1) * B := Nat.le_add_left _ _
        · rw [costNumerator_succ next Final x hFinal T,
              costNumerator_succ next Intermediate x hIntermediate T]
          have hSum :
              (List.ofFn (fun e : Fin n =>
                costNumerator next Final (next x e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                costNumerator next Intermediate (next x e) T)).sum +
                n * (n ^ T * B) := by
            have hPoint :=
              ofFn_sum_le
                (fun e : Fin n =>
                  costNumerator next Final (next x e) T)
                (fun e : Fin n =>
                  costNumerator next Intermediate (next x e) T +
                    n ^ T * B)
                (fun e => ih (next x e))
            rw [ofFn_sum_add, ofFn_sum_const] at hPoint
            exact hPoint
          have hScale :
              n * (n ^ T * B) = n ^ (T + 1) * B := by
            rw [Nat.pow_succ]
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          calc
            n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  costNumerator next Final (next x e) T)).sum ≤
              n ^ (T + 1) +
                ((List.ofFn (fun e : Fin n =>
                  costNumerator next Intermediate (next x e) T)).sum +
                  n * (n ^ T * B)) :=
              Nat.add_le_add_left hSum _
            _ = (n ^ (T + 1) +
                  (List.ofFn (fun e : Fin n =>
                    costNumerator next Intermediate (next x e) T)).sum) +
                    n ^ (T + 1) * B := by
              rw [hScale]
              exact (Nat.add_assoc _ _ _).symm

/-- Exact additive cost composition at arbitrary first-hit cuts. -/
theorem grantDrainComposeTwoCosts
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (First Final : X → Prop) (x : X) (A B : Nat)
    (hFirst : ∀ T : Nat,
      costNumerator next First x T ≤ n ^ T * A)
    (hAfter : ∀ y : X, First y →
      ∀ T : Nat,
        costNumerator next Final y T ≤ n ^ T * B) :
    ∀ T : Nat,
      costNumerator next Final x T ≤ n ^ T * (A + B) := by
  intro T
  have hPrefix :=
    grantDrainComposeIntermediateCost next First Final B
      hAfter T x
  calc
    costNumerator next Final x T ≤
        costNumerator next First x T + n ^ T * B := hPrefix
    _ ≤ n ^ T * A + n ^ T * B :=
      Nat.add_le_add_right (hFirst T) _
    _ = n ^ T * (A + B) := by rw [Nat.mul_add]

/-- Four stages are combined by applying the two-stage lemma
three times to exactly the same physical chain. -/
theorem grantDrainComposeFourCosts
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (First Second Third Final : X → Prop)
    (x : X) (A B C D : Nat)
    (hFirst : ∀ T : Nat,
      costNumerator next First x T ≤ n ^ T * A)
    (hSecond : ∀ y : X, First y →
      ∀ T : Nat,
        costNumerator next Second y T ≤ n ^ T * B)
    (hThird : ∀ y : X, Second y →
      ∀ T : Nat,
        costNumerator next Third y T ≤ n ^ T * C)
    (hFourth : ∀ y : X, Third y →
      ∀ T : Nat,
        costNumerator next Final y T ≤ n ^ T * D) :
    ∀ T : Nat,
      costNumerator next Final x T ≤
        n ^ T * (((A + B) + C) + D) := by
  have hSecondFromStart :=
    grantDrainComposeTwoCosts next First Second x A B
      hFirst hSecond
  have hThirdFromStart :=
    grantDrainComposeTwoCosts next Second Third x (A + B) C
      hSecondFromStart hThird
  exact grantDrainComposeTwoCosts
    next Third Final x ((A + B) + C) D
    hThirdFromStart hFourth

/-- Expected hitting time with the almost-sure clause, obtained
from the already-proved UniformFirstHit conversion. -/
theorem grantDrainComposeFourExpected
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (First Second Third Final : X → Prop)
    (x : X) (A B C D : Nat)
    (hn : 0 < n)
    (hFirst : ∀ T : Nat,
      costNumerator next First x T ≤ n ^ T * A)
    (hSecond : ∀ y : X, First y →
      ∀ T : Nat,
        costNumerator next Second y T ≤ n ^ T * B)
    (hThird : ∀ y : X, Second y →
      ∀ T : Nat,
        costNumerator next Third y T ≤ n ^ T * C)
    (hFourth : ∀ y : X, Third y →
      ∀ T : Nat,
        costNumerator next Final y T ≤ n ^ T * D) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next Final x ((((A + B) + C) + D : Nat) : Rat) := by
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next Final hn x (((A + B) + C) + D)).2
      (grantDrainComposeFourCosts next
        First Second Third Final x A B C D
        hFirst hSecond hThird hFourth)

/-- Arithmetic over opaque natural quantities. This is only a
SUFFICIENT allocation of the as-yet-unproved warm cost. -/
theorem grantDrainComposePaperBudget
    (n warmCap : Nat)
    (hWarmCap : 3 * warmCap ≤ 82 * n ^ 2) :
    3 * (4 * n ^ 2 + 4 * n ^ 2 +
      n * (n - 2) + warmCap) ≤ 109 * n ^ 2 := by
  have hSector : n * (n - 2) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 2)
  rw [Nat.pow_two] at *
  generalize hSquare : n * n = square at *
  omega

/-- The paper-compatible 109/3 bound is strictly below 37. -/
theorem grantDrainComposeBudgetBelowThirtySeven
    (n warmCap : Nat) (hn : 5 ≤ n)
    (hWarmCap : 3 * warmCap ≤ 82 * n ^ 2) :
    4 * n ^ 2 + 4 * n ^ 2 +
      n * (n - 2) + warmCap < 37 * n ^ 2 := by
  have hPaper :=
    grantDrainComposePaperBudget n warmCap hWarmCap
  have hPositive : 0 < n ^ 2 :=
    Nat.pow_pos (by omega : 0 < n)
  generalize hSquare : n ^ 2 = square at *
  omega

/-- Conditional producer of the real canonical model shared bound.
The four named stages are all bounds on the ACTUAL physical step.
The first physical NoBadLive stage is stronger than the existing
ghost Done cost; no incorrect handoff is hidden in this theorem. -/
theorem grantDrainSharedBoundOfStageCosts
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (warmCap : Nat)
    (hZeta : ∀ s : GrantDrainState n Scratch,
      PPlus ring s.native →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (GrantDrainEntranceNoBadLive ring) s T ≤
            n ^ T * (4 * n ^ 2))
    (hDummy : ∀ s : GrantDrainState n Scratch,
      GrantDrainEntranceNoBadLive ring s →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (GrantDrainEntranceIntermediateZ ring) s T ≤
            n ^ T * (4 * n ^ 2))
    (hClean : ∀ s : GrantDrainState n Scratch,
      GrantDrainEntranceIntermediateZ ring s →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch =>
            C_native ring z.native) s T ≤
              n ^ T * (n * (n - 2)))
    (hWarm : ∀ s : GrantDrainState n Scratch,
      C_native ring s.native →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch => GrantFree z) s T ≤
            n ^ T * warmCap)
    (hWarmCap : 3 * warmCap ≤ 82 * n ^ 2) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) := by
  intro x hPB
  change PPlus ring x.native at hPB
  change UniformFirstHit.ExpectedHittingTimeAtMost
    (grantDrainStep ring fresh update)
    (fun z : GrantDrainState n Scratch => GrantFree z)
    x ((37 * n ^ 2 : Nat) : Rat)
  have hStages :=
    grantDrainComposeFourCosts
      (grantDrainStep ring fresh update)
      (GrantDrainEntranceNoBadLive ring)
      (GrantDrainEntranceIntermediateZ ring)
      (fun z : GrantDrainState n Scratch => C_native ring z.native)
      (fun z : GrantDrainState n Scratch => GrantFree z)
      x (4 * n ^ 2) (4 * n ^ 2) (n * (n - 2)) warmCap
      (hZeta x hPB) hDummy hClean hWarm
  have hBudget :=
    grantDrainComposeBudgetBelowThirtySeven
      n warmCap hn hWarmCap
  have hCost :
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch => GrantFree z) x T ≤
            n ^ T * (37 * n ^ 2) := by
    intro T
    exact Nat.le_trans (hStages T)
      (Nat.mul_le_mul_left (n ^ T) (Nat.le_of_lt hBudget))
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (grantDrainStep ring fresh update)
    (fun z : GrantDrainState n Scratch => GrantFree z)
    (by omega : 0 < n) x (37 * n ^ 2)).2 hCost

/-- The already proved sharp clean-sector cost discharges hClean.
The other genuine cut-handoffs and warm cost remain hypotheses. -/
theorem grantDrainSharedBoundOfKnownCleanStage
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (warmCap : Nat)
    (hZeta : ∀ s : GrantDrainState n Scratch,
      PPlus ring s.native →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (GrantDrainEntranceNoBadLive ring) s T ≤
            n ^ T * (4 * n ^ 2))
    (hDummy : ∀ s : GrantDrainState n Scratch,
      GrantDrainEntranceNoBadLive ring s →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (GrantDrainEntranceIntermediateZ ring) s T ≤
            n ^ T * (4 * n ^ 2))
    (hWarm : ∀ s : GrantDrainState n Scratch,
      C_native ring s.native →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch => GrantFree z) s T ≤
            n ^ T * warmCap)
    (hWarmCap : 3 * warmCap ≤ 82 * n ^ 2) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) := by
  apply grantDrainSharedBoundOfStageCosts
    ring hn fresh update warmCap hZeta hDummy
  · intro s hZ T
    change costNumerator
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun z : GrantDrainState n Scratch => C_native ring z.native)
      s T ≤ n ^ T * (n * (n - 2))
    exact grantDrainEntranceR8eCleanSectorCostSharp
      ring hn fresh update s hZ T
  · exact hWarm
  · exact hWarmCap

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainComposeIntermediateCost
#print axioms L3.GrantDrainEntrance.grantDrainComposeTwoCosts
#print axioms L3.GrantDrainEntrance.grantDrainComposeFourCosts
#print axioms L3.GrantDrainEntrance.grantDrainComposeFourExpected
#print axioms L3.GrantDrainEntrance.grantDrainComposePaperBudget
#print axioms L3.GrantDrainEntrance.grantDrainComposeBudgetBelowThirtySeven
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfStageCosts
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfKnownCleanStage
