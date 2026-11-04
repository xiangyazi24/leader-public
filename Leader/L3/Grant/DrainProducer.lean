import Leader.L3.Grant.DrainBranch
import Leader.L3.Grant.DrainWarm
import Leader.L3.Grant.DrainMarkedBranch

/-!
# Grant-drain shared bound from the all-marked and warm branch costs

`GrantDrainBranch` composes the grant drain at the zeta cut on the two
literal disjuncts of `GrantDrainEntranceDone`, with three named branch
costs: the all-marked branch at `4 n^2`, the D.5 dummy retirement and
the warm stage.  This module

* generalizes the all-marked cap to any `markedCap` no larger than the
  left branch's total `4 n^2 + n (n - 2) + warmCap`, so a union-over-labels
  tail bound (which costs more than `4 n^2`) can be used for that branch;
* discharges the dummy premise with the proved D.5 cost
  `grantDrainDummyNoBadToIntermediateCost` (`GrantDrainWarm`).

What remains are exactly two branch costs: the all-marked branch and
the warm stage.
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Budget of the branched composition when the all-marked branch is
no more expensive than the left branch. -/
theorem grantDrainProducerBudget
    (n warmCap markedCap : Nat) (hn : 5 ≤ n)
    (hWarmCap : warmCap ≤ 28 * n ^ 2)
    (hMarked : markedCap ≤ 4 * n ^ 2 + n * (n - 2) + warmCap) :
    4 * n ^ 2 +
      max (4 * n ^ 2 + n * (n - 2) + warmCap) markedCap <
      37 * n ^ 2 := by
  have hBase := grantDrainBranchBudgetBelowThirtySeven n warmCap hn hWarmCap
  have h1 : max (4 * n ^ 2 + n * (n - 2) + warmCap) markedCap =
      4 * n ^ 2 + n * (n - 2) + warmCap := Nat.max_eq_left hMarked
  have h2 : max (4 * n ^ 2 + n * (n - 2) + warmCap) (4 * n ^ 2) =
      4 * n ^ 2 + n * (n - 2) + warmCap :=
    Nat.max_eq_left (by omega)
  rw [h1]
  rw [h2] at hBase
  exact hBase

/-- `GrantDrainSharedBound` from the all-marked branch cost at any cap
`markedCap` bounded by the left branch, the proved D.5 dummy cost and
the warm-stage cost `warmCap ≤ 28 n^2`. -/
theorem grantDrainSharedBoundOfMarkedAndWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (warmCap markedCap : Nat)
    (hAllMarked :
      ∀ s : GrantDrainState n Scratch,
        PPlus ring s.native →
        ∀ word : List (Fin n),
          GrantDrainBranchMarkedCut
            (grantDrainEntranceRun ring fresh update
              (grantDrainEntranceInitial ring s) word) →
          ∀ T : Nat,
            costNumerator (grantDrainStep ring fresh update)
              (fun z : GrantDrainState n Scratch => GrantFree z)
              (grantDrainEntrancePhysicalWord
                ring fresh update s word) T ≤
              n ^ T * markedCap)
    (hWarm :
      ∀ y : GrantDrainState n Scratch,
        C_native ring y.native →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch => GrantFree z)
            y T ≤ n ^ T * warmCap)
    (hWarmCap : warmCap ≤ 28 * n ^ 2)
    (hMarkedCap : markedCap ≤ 4 * n ^ 2 + n * (n - 2) + warmCap) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) := by
  have hDummy :
      ∀ y : GrantDrainState n Scratch,
        PPlus ring y.native →
        GrantDrainEntranceNoBadLive ring y →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (GrantDrainEntranceIntermediateZ ring) y T ≤
              n ^ T * (4 * n ^ 2) :=
    fun y hP hN T =>
      grantDrainDummyNoBadToIntermediateCost ring hn fresh update y hP hN T
  intro s hPB
  change PPlus ring s.native at hPB
  change UniformFirstHit.ExpectedHittingTimeAtMost
    (grantDrainStep ring fresh update)
    (fun z : GrantDrainState n Scratch => GrantFree z)
    s ((37 * n ^ 2 : Nat) : Rat)
  have hZeta :
      ∀ T : Nat,
        costNumerator
          (grantDrainEntranceNext ring fresh update)
          (fun z : GrantDrainEntranceState n Scratch =>
            GrantDrainBranchNoBadCut z ∨
              GrantDrainBranchMarkedCut z)
          (grantDrainEntranceInitial ring s) T ≤
            n ^ T * (4 * n ^ 2) := by
    intro T
    change costNumerator
      (grantDrainEntranceNext ring fresh update)
      GrantDrainEntranceDone
      (grantDrainEntranceInitial ring s) T ≤
        n ^ T * (4 * n ^ 2)
    exact grantDrainEntranceFirstStageCost
      ring hn fresh update s hPB T
  have hLeft :
      ∀ word : List (Fin n),
        GrantDrainBranchNoBadCut
          (word.foldl
            (grantDrainEntranceNext ring fresh update)
            (grantDrainEntranceInitial ring s)) →
        ∀ T : Nat,
          costNumerator
            (grantDrainEntranceNext ring fresh update)
            (fun z : GrantDrainEntranceState n Scratch =>
              GrantFree z.physical)
            (word.foldl
              (grantDrainEntranceNext ring fresh update)
              (grantDrainEntranceInitial ring s)) T ≤
            n ^ T * (4 * n ^ 2 + n * (n - 2) + warmCap) := by
    intro word hCut T
    have hPhysical :=
      grantDrainBranchLeftPhysicalCost
        ring hn fresh update s hPB word hCut
        warmCap hDummy hWarm T
    have hEq :=
      grantDrainBranchGhostGrantFreeCostEq
        ring fresh update T
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word)
    change costNumerator
      (grantDrainEntranceNext ring fresh update)
      (fun z : GrantDrainEntranceState n Scratch =>
        GrantFree z.physical)
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word) T ≤ _
    rw [hEq, grantDrainEntrancePhysicalWordProjection
      ring fresh update word (grantDrainEntranceInitial ring s)]
    exact hPhysical
  have hRight :
      ∀ word : List (Fin n),
        GrantDrainBranchMarkedCut
          (word.foldl
            (grantDrainEntranceNext ring fresh update)
            (grantDrainEntranceInitial ring s)) →
        ∀ T : Nat,
          costNumerator
            (grantDrainEntranceNext ring fresh update)
            (fun z : GrantDrainEntranceState n Scratch =>
              GrantFree z.physical)
            (word.foldl
              (grantDrainEntranceNext ring fresh update)
              (grantDrainEntranceInitial ring s)) T ≤
            n ^ T * markedCap := by
    intro word hCut T
    have hPhysical := hAllMarked s hPB word hCut T
    have hEq :=
      grantDrainBranchGhostGrantFreeCostEq
        ring fresh update T
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word)
    change costNumerator
      (grantDrainEntranceNext ring fresh update)
      (fun z : GrantDrainEntranceState n Scratch =>
        GrantFree z.physical)
      (grantDrainEntranceRun ring fresh update
        (grantDrainEntranceInitial ring s) word) T ≤ _
    rw [hEq, grantDrainEntrancePhysicalWordProjection
      ring fresh update word (grantDrainEntranceInitial ring s)]
    exact hPhysical
  have hBranched :=
    grantDrainBranchReachableTwoCosts
      (grantDrainEntranceNext ring fresh update)
      (GrantDrainBranchNoBadCut (Scratch := Scratch))
      (GrantDrainBranchMarkedCut (Scratch := Scratch))
      (fun z : GrantDrainEntranceState n Scratch =>
        GrantFree z.physical)
      (grantDrainEntranceInitial ring s)
      (4 * n ^ 2)
      (4 * n ^ 2 + n * (n - 2) + warmCap)
      markedCap
      hZeta hLeft hRight
  have hBudget :=
    grantDrainProducerBudget n warmCap markedCap hn hWarmCap hMarkedCap
  have hCost :
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch => GrantFree z)
          s T ≤ n ^ T * (37 * n ^ 2) := by
    intro T
    have hEq :=
      grantDrainBranchGhostGrantFreeCostEq
        ring fresh update T
        (grantDrainEntranceInitial ring s)
    have hGhost := hBranched T
    rw [hEq] at hGhost
    exact Nat.le_trans hGhost
      (Nat.mul_le_mul_left (n ^ T) (Nat.le_of_lt hBudget))
  exact
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (grantDrainStep ring fresh update)
      (fun z : GrantDrainState n Scratch => GrantFree z)
      (by omega : 0 < n) s (37 * n ^ 2)).2 hCost

/-- The 23 n^2 instance: an all-marked branch and a warm stage each at
`23 n^2` give `GrantDrainSharedBound`. -/
theorem grantDrainSharedBoundOfMarkedAndWarmTwentyThree
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hAllMarked :
      ∀ s : GrantDrainState n Scratch,
        PPlus ring s.native →
        ∀ word : List (Fin n),
          GrantDrainBranchMarkedCut
            (grantDrainEntranceRun ring fresh update
              (grantDrainEntranceInitial ring s) word) →
          ∀ T : Nat,
            costNumerator (grantDrainStep ring fresh update)
              (fun z : GrantDrainState n Scratch => GrantFree z)
              (grantDrainEntrancePhysicalWord
                ring fresh update s word) T ≤
              n ^ T * (23 * n ^ 2))
    (hWarm :
      ∀ y : GrantDrainState n Scratch,
        C_native ring y.native →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch => GrantFree z)
            y T ≤ n ^ T * (23 * n ^ 2)) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) :=
  grantDrainSharedBoundOfMarkedAndWarm ring hn fresh update
    (23 * n ^ 2) (23 * n ^ 2) hAllMarked hWarm
    (by omega) (by omega)

/-- `GrantDrainSharedBound` from the warm stage alone: the all-marked
branch is paid by `grantDrainMarkedBranchCost` (23 n^2, weak marks
included). -/
theorem grantDrainSharedBoundOfWarm
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hWarm :
      ∀ y : GrantDrainState n Scratch,
        C_native ring y.native →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch => GrantFree z)
            y T ≤ n ^ T * (23 * n ^ 2)) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) :=
  grantDrainSharedBoundOfMarkedAndWarmTwentyThree ring hn fresh update
    (fun s hPB word hMarked T =>
      grantDrainMarkedBranchCost ring hn fresh update s hPB word hMarked T)
    hWarm

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainProducerBudget
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfMarkedAndWarm
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfMarkedAndWarmTwentyThree
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfWarm
