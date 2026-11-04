import Leader.L3.Grant.DrainCompose

/-!
# Branched finite-word grant-drain composition

The entrance cut is a genuine
disjunction on a ghost-extended physical chain.  Only ghost states
reachable from the original physical entrance may be used for the
post-cut estimates.  The all-marked and dummy-stage cost laws are
explicitly named hypotheses until their physical proofs are installed.

No protocol transition, grant producer, or scheduler is changed.
-/

namespace L3.GrantDrainEntrance

open L3.GrantDrainShared
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Two-branch extension of the existing literal Bellman recursion
grantDrainComposeTwoCosts.  No independent branch clocks. -/
theorem grantDrainBranchTwoCosts
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (Left Right Final : X → Prop)
    (x : X) (firstCap leftCap rightCap : Nat)
    (hFirst : ∀ T : Nat,
      costNumerator next (fun z => Left z ∨ Right z) x T ≤
        n ^ T * firstCap)
    (hLeft : ∀ y : X, Left y →
      ∀ T : Nat,
        costNumerator next Final y T ≤ n ^ T * leftCap)
    (hRight : ∀ y : X, Right y →
      ∀ T : Nat,
        costNumerator next Final y T ≤ n ^ T * rightCap) :
    ∀ T : Nat,
      costNumerator next Final x T ≤
        n ^ T * (firstCap + max leftCap rightCap) := by
  have hAfter :
      ∀ y : X, (Left y ∨ Right y) →
        ∀ T : Nat,
          costNumerator next Final y T ≤
            n ^ T * max leftCap rightCap := by
    intro y hCase T
    rcases hCase with hL | hR
    · exact Nat.le_trans (hLeft y hL T)
        (Nat.mul_le_mul_left (n ^ T)
          (Nat.le_max_left leftCap rightCap))
    · exact Nat.le_trans (hRight y hR T)
        (Nat.mul_le_mul_left (n ^ T)
          (Nat.le_max_right leftCap rightCap))
  exact grantDrainComposeTwoCosts
    next (fun z => Left z ∨ Right z) Final x
      firstCap (max leftCap rightCap) hFirst hAfter

/-- Genuine scheduler prefixes only: arbitrary forged ghost states
are excluded from the post-zeta branch continuation. -/
def GrantDrainBranchReachable
    {n : Nat} {X : Type}
    (next : X → Fin n → X) (start current : X) : Prop :=
  ∃ word : List (Fin n), current = word.foldl next start

theorem grantDrainBranchReachableInitial
    {n : Nat} {X : Type}
    (next : X → Fin n → X) (start : X) :
    GrantDrainBranchReachable next start start := by
  exact ⟨[], rfl⟩

theorem grantDrainBranchReachableStep
    {n : Nat} {X : Type}
    (next : X → Fin n → X) (start current : X)
    (e : Fin n)
    (h : GrantDrainBranchReachable next start current) :
    GrantDrainBranchReachable next start (next current e) := by
  obtain ⟨word, hWord⟩ := h
  refine ⟨word ++ [e], ?_⟩
  rw [hWord, List.foldl_append]
  rfl

/-- Intersecting a first-hit predicate with a forward invariant
does not change its finite-horizon cost from invariant states. -/
theorem grantDrainBranchInvariantHitCost
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (Invariant Target : X → Prop)
    (hClosed : ∀ y : X, ∀ e : Fin n,
      Invariant y → Invariant (next y e)) :
    ∀ T : Nat, ∀ y : X, Invariant y →
      costNumerator next
        (fun z => Invariant z ∧ Target z) y T =
      costNumerator next Target y T := by
  classical
  intro T
  induction T with
  | zero =>
      intro y _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro y hy
      by_cases hTarget : Target y
      · have hBoth : Invariant y ∧ Target y := ⟨hy, hTarget⟩
        rw [costNumerator_terminal next
          (fun z => Invariant z ∧ Target z) y hBoth (T + 1),
          costNumerator_terminal next Target y hTarget (T + 1)]
      · have hBoth : ¬ (Invariant y ∧ Target y) :=
          fun h => hTarget h.2
        rw [costNumerator_succ next
          (fun z => Invariant z ∧ Target z) y hBoth T,
          costNumerator_succ next Target y hTarget T]
        have hChildren :
            (fun e : Fin n =>
              costNumerator next
                (fun z => Invariant z ∧ Target z)
                (next y e) T) =
            (fun e : Fin n =>
              costNumerator next Target (next y e) T) := by
          funext e
          exact ih (next y e) (hClosed y e hy)
        rw [hChildren]

/-- Reachability-restricted branch composition.  Continuation
bounds are required ONLY at actual prefixes of start.  This
prevents a false projection from an arbitrary ghost with zero
bulletHosts but a physical bad-LIVE bullet. -/
theorem grantDrainBranchReachableTwoCosts
    {n : Nat} {X : Type}
    (next : X → Fin n → X)
    (Left Right Final : X → Prop)
    (start : X) (firstCap leftCap rightCap : Nat)
    (hFirst : ∀ T : Nat,
      costNumerator next
        (fun z => Left z ∨ Right z) start T ≤
          n ^ T * firstCap)
    (hLeft : ∀ word : List (Fin n),
      Left (word.foldl next start) →
      ∀ T : Nat,
        costNumerator next Final
          (word.foldl next start) T ≤ n ^ T * leftCap)
    (hRight : ∀ word : List (Fin n),
      Right (word.foldl next start) →
      ∀ T : Nat,
        costNumerator next Final
          (word.foldl next start) T ≤ n ^ T * rightCap) :
    ∀ T : Nat,
      costNumerator next Final start T ≤
        n ^ T * (firstCap + max leftCap rightCap) := by
  have hCutCost :
      ∀ T : Nat,
        costNumerator next
          (fun z =>
            GrantDrainBranchReachable next start z ∧
              (Left z ∨ Right z)) start T ≤
          n ^ T * firstCap := by
    intro T
    have hEq := grantDrainBranchInvariantHitCost
      next (GrantDrainBranchReachable next start)
      (fun z => Left z ∨ Right z)
      (fun y e hy =>
        grantDrainBranchReachableStep next start y e hy)
      T start (grantDrainBranchReachableInitial next start)
    rw [hEq]
    exact hFirst T
  have hAfter :
      ∀ y : X,
        (GrantDrainBranchReachable next start y ∧
          (Left y ∨ Right y)) →
        ∀ T : Nat,
          costNumerator next Final y T ≤
            n ^ T * max leftCap rightCap := by
    intro y hy T
    obtain ⟨⟨word, hWord⟩, hCase⟩ := hy
    have hCaseWord :
        Left (word.foldl next start) ∨
          Right (word.foldl next start) := by
      rw [← hWord]
      exact hCase
    have hCostWord :
        costNumerator next Final
            (word.foldl next start) T ≤
          n ^ T * max leftCap rightCap := by
      rcases hCaseWord with hL | hR
      · exact Nat.le_trans (hLeft word hL T)
          (Nat.mul_le_mul_left (n ^ T)
            (Nat.le_max_left leftCap rightCap))
      · exact Nat.le_trans (hRight word hR T)
          (Nat.mul_le_mul_left (n ^ T)
            (Nat.le_max_right leftCap rightCap))
    rw [hWord]
    exact hCostWord
  exact grantDrainComposeTwoCosts
    next
    (fun z =>
      GrantDrainBranchReachable next start z ∧
        (Left z ∨ Right z))
    Final start firstCap (max leftCap rightCap)
    hCutCost hAfter

/-- Literal two disjuncts of GrantDrainEntranceDone.
A marked label can be weak, so the right branch is NOT made
equivalent to a strong/terminal-only native observer. -/
def GrantDrainBranchNoBadCut
    {n : Nat} {Scratch : Type}
    (x : GrantDrainEntranceState n Scratch) : Prop :=
  ∀ i : Fin n, x.bulletHosts i = none

def GrantDrainBranchMarkedCut
    {n : Nat} {Scratch : Type}
    (x : GrantDrainEntranceState n Scratch) : Prop :=
  ∀ i : Fin n, (x.grantLabels i).host ≠ none →
    (x.grantLabels i).mark ≠ .unmarked

/-- Ghost extension projects exactly to the original physical
GrantFree cost at EVERY horizon and EVERY ghost state. -/
theorem grantDrainBranchGhostGrantFreeCostEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ T : Nat, ∀ x : GrantDrainEntranceState n Scratch,
      costNumerator
        (grantDrainEntranceNext ring fresh update)
        (fun z : GrantDrainEntranceState n Scratch =>
          GrantFree z.physical) x T =
      costNumerator (grantDrainStep ring fresh update)
        (fun z : GrantDrainState n Scratch => GrantFree z)
        x.physical T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      simp only [costNumerator_zero]
  | succ T ih =>
      intro x
      by_cases hFree : GrantFree x.physical
      · rw [costNumerator_terminal
          (grantDrainEntranceNext ring fresh update)
          (fun z : GrantDrainEntranceState n Scratch =>
            GrantFree z.physical) x hFree (T + 1),
          costNumerator_terminal (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch => GrantFree z)
            x.physical hFree (T + 1)]
      · rw [costNumerator_succ
          (grantDrainEntranceNext ring fresh update)
          (fun z : GrantDrainEntranceState n Scratch =>
            GrantFree z.physical) x hFree T,
          costNumerator_succ
          (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch => GrantFree z)
          x.physical hFree T]
        have hChildren :
            (fun e : Fin n =>
              costNumerator
                (grantDrainEntranceNext ring fresh update)
                (fun z : GrantDrainEntranceState n Scratch =>
                  GrantFree z.physical)
                (grantDrainEntranceNext ring fresh update x e) T) =
            (fun e : Fin n =>
              costNumerator (grantDrainStep ring fresh update)
                (fun z : GrantDrainState n Scratch => GrantFree z)
                (grantDrainStep ring fresh update x.physical e) T) := by
          funext e
          exact ih (grantDrainEntranceNext ring fresh update x e)
        rw [hChildren]

/-- Source PPlus is retained on the exact physical scheduler word. -/
theorem grantDrainBranchProtectedWord
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ word : List (Fin n), ∀ s : GrantDrainState n Scratch,
      PPlus ring s.native →
      PPlus ring
        (grantDrainEntrancePhysicalWord ring fresh update
          s word).native := by
  intro word
  induction word with
  | nil =>
      intro s hPB
      exact hPB
  | cons e rest ih =>
      intro s hPB
      change PPlus ring
        (grantDrainEntrancePhysicalWord ring fresh update
          (grantDrainStep ring fresh update s e) rest).native
      exact ih (grantDrainStep ring fresh update s e)
        (sharedSourceProtectedClosed ring hn
          fresh update s e hPB)

/-- The LEFT zeta branch is the only branch that projects to
physical NoBadLive.  The physical dummy clock is deliberately
a named hypothesis until its incoming standalone code is merged. -/
theorem grantDrainBranchLeftPhysicalCost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hPB : PPlus ring s.native)
    (word : List (Fin n))
    (hLeft :
      GrantDrainBranchNoBadCut
        (grantDrainEntranceRun ring fresh update
          (grantDrainEntranceInitial ring s) word))
    (warmCap : Nat)
    (hDummy : ∀ y : GrantDrainState n Scratch,
      PPlus ring y.native →
      GrantDrainEntranceNoBadLive ring y →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (GrantDrainEntranceIntermediateZ ring) y T ≤
            n ^ T * (4 * n ^ 2))
    (hWarm : ∀ y : GrantDrainState n Scratch,
      C_native ring y.native →
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (fun z : GrantDrainState n Scratch => GrantFree z)
          y T ≤ n ^ T * warmCap) :
    ∀ T : Nat,
      costNumerator (grantDrainStep ring fresh update)
        (fun z : GrantDrainState n Scratch => GrantFree z)
        (grantDrainEntrancePhysicalWord ring fresh update s word) T ≤
        n ^ T * (4 * n ^ 2 + n * (n - 2) + warmCap) := by
  have hNoBad :
      GrantDrainEntranceNoBadLive ring
        (grantDrainEntrancePhysicalWord
          ring fresh update s word) :=
    grantDrainR8FirstDoneLeftPhysicalNoBad
      ring hn fresh update s word hPB hLeft
  have hPBWord :=
    grantDrainBranchProtectedWord
      ring hn fresh update word s hPB
  have hDummyCost :
      ∀ T : Nat,
        costNumerator (grantDrainStep ring fresh update)
          (GrantDrainEntranceIntermediateZ ring)
          (grantDrainEntrancePhysicalWord
            ring fresh update s word) T ≤
            n ^ T * (4 * n ^ 2) :=
    hDummy (grantDrainEntrancePhysicalWord
      ring fresh update s word) hPBWord hNoBad
  have hCleanCost :
      ∀ y : GrantDrainState n Scratch,
        GrantDrainEntranceIntermediateZ ring y →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch =>
              C_native ring z.native) y T ≤
              n ^ T * (n * (n - 2)) := by
    intro y hy T
    change costNumerator
      (grantDrainCanonicalModel ring hn fresh update).step
      (fun z : GrantDrainState n Scratch =>
        C_native ring z.native) y T ≤
        n ^ T * (n * (n - 2))
    exact grantDrainEntranceR8eCleanSectorCostSharp
      ring hn fresh update y hy T
  have hTwo :=
    grantDrainComposeTwoCosts
      (grantDrainStep ring fresh update)
      (GrantDrainEntranceIntermediateZ ring)
      (fun z : GrantDrainState n Scratch =>
        C_native ring z.native)
      (grantDrainEntrancePhysicalWord ring fresh update s word)
      (4 * n ^ 2) (n * (n - 2))
      hDummyCost hCleanCost
  exact grantDrainComposeTwoCosts
    (grantDrainStep ring fresh update)
    (fun z : GrantDrainState n Scratch =>
      C_native ring z.native)
    (fun z : GrantDrainState n Scratch => GrantFree z)
    (grantDrainEntrancePhysicalWord ring fresh update s word)
    (4 * n ^ 2 + n * (n - 2)) warmCap hTwo hWarm

/-- Nat arithmetic isolated from every symbolic scheduler power. -/
private theorem grantDrainBranchBudgetOpaque
    (square sector warmCap : Nat)
    (hSector : sector < square)
    (hWarmCap : warmCap ≤ 28 * square) :
    4 * square +
      max (4 * square + sector + warmCap) (4 * square) <
        37 * square := by
  have hBig : 4 * square ≤
      4 * square + sector + warmCap := by omega
  rw [Nat.max_eq_left hBig]
  omega

/-- 4n² + max(4n²,4n²+n(n-2)+warmCap) < 37n².
The maximum uniform INTEGER warm coefficient is 28, since the
strict n(n-2) < n² saving is retained rather than rounded away. -/
theorem grantDrainBranchBudgetBelowThirtySeven
    (n warmCap : Nat) (hn : 5 ≤ n)
    (hWarmCap : warmCap ≤ 28 * n ^ 2) :
    4 * n ^ 2 +
      max (4 * n ^ 2 + n * (n - 2) + warmCap)
        (4 * n ^ 2) < 37 * n ^ 2 := by
  have hSub : n - 2 + 2 = n := by omega
  have hSectorEq : n * (n - 2) + 2 * n = n ^ 2 := by
    calc
      n * (n - 2) + 2 * n =
          n * (n - 2) + n * 2 := by rw [Nat.mul_comm 2 n]
      _ = n * ((n - 2) + 2) :=
        (Nat.mul_add n (n - 2) 2).symm
      _ = n * n := by rw [hSub]
      _ = n ^ 2 := by rw [Nat.pow_two]
  have hPositive : 0 < 2 * n := by omega
  have hSector : n * (n - 2) < n ^ 2 := by omega
  exact grantDrainBranchBudgetOpaque
    (n ^ 2) (n * (n - 2)) warmCap hSector hWarmCap

theorem grantDrainBranchTwentyThreeFits
    (n : Nat) :
    23 * n ^ 2 ≤ 28 * n ^ 2 :=
  Nat.mul_le_mul_right (n ^ 2) (by omega : 23 ≤ 28)

private theorem grantDrainBranchAboveOpaque
    (square sector : Nat)
    (hSector : 0 < sector) :
    37 * square <
      4 * square +
        max (4 * square + sector + 29 * square)
          (4 * square) := by
  have hBig : 4 * square ≤
      4 * square + sector + 29 * square := by omega
  rw [Nat.max_eq_left hBig]
  omega

/-- A uniform integer warm coefficient 29 fails this composition
budget, independently of whether its physical cost is provable. -/
theorem grantDrainBranchTwentyNineTooLarge
    (n : Nat) (hn : 5 ≤ n) :
    37 * n ^ 2 <
      4 * n ^ 2 +
        max (4 * n ^ 2 + n * (n - 2) + 29 * n ^ 2)
          (4 * n ^ 2) := by
  have hSector : 0 < n * (n - 2) :=
    Nat.mul_pos (by omega : 0 < n)
      (by omega : 0 < n - 2)
  exact grantDrainBranchAboveOpaque
    (n ^ 2) (n * (n - 2)) hSector

/-- CONDITIONAL producer with the ACTUAL proved ghost zeta cost.
hAllMarked is required ONLY on genuine initial-state prefixes;
hDummy and hWarm are explicit physical first-hit-cost inputs.
This result does not pretend those unmerged stage laws are proved. -/
theorem grantDrainSharedBoundOfBranchedCosts
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (warmCap : Nat)
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
              n ^ T * (4 * n ^ 2))
    (hDummy :
      ∀ y : GrantDrainState n Scratch,
        PPlus ring y.native →
        GrantDrainEntranceNoBadLive ring y →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (GrantDrainEntranceIntermediateZ ring) y T ≤
              n ^ T * (4 * n ^ 2))
    (hWarm :
      ∀ y : GrantDrainState n Scratch,
        C_native ring y.native →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch => GrantFree z)
            y T ≤ n ^ T * warmCap)
    (hWarmCap : warmCap ≤ 28 * n ^ 2) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) := by
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
            n ^ T * (4 * n ^ 2) := by
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
      (4 * n ^ 2)
      hZeta hLeft hRight
  have hBudget :=
    grantDrainBranchBudgetBelowThirtySeven
      n warmCap hn hWarmCap
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

/-- Specialization to 23n². Both genuinely unproved branch costs
remain named hypotheses rather than silently assumed leaves. -/
theorem grantDrainSharedBoundOfBranchedTwentyThree
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
              n ^ T * (4 * n ^ 2))
    (hDummy :
      ∀ y : GrantDrainState n Scratch,
        PPlus ring y.native →
        GrantDrainEntranceNoBadLive ring y →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (GrantDrainEntranceIntermediateZ ring) y T ≤
              n ^ T * (4 * n ^ 2))
    (hWarm :
      ∀ y : GrantDrainState n Scratch,
        C_native ring y.native →
        ∀ T : Nat,
          costNumerator (grantDrainStep ring fresh update)
            (fun z : GrantDrainState n Scratch => GrantFree z)
            y T ≤ n ^ T * (23 * n ^ 2)) :
    GrantDrainSharedBound
      (grantDrainCanonicalModel ring hn fresh update) := by
  exact grantDrainSharedBoundOfBranchedCosts
    ring hn fresh update (23 * n ^ 2)
    hAllMarked hDummy hWarm
    (grantDrainBranchTwentyThreeFits n)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainBranchTwoCosts
#print axioms L3.GrantDrainEntrance.grantDrainBranchReachableTwoCosts
#print axioms L3.GrantDrainEntrance.grantDrainBranchGhostGrantFreeCostEq
#print axioms L3.GrantDrainEntrance.grantDrainBranchBudgetBelowThirtySeven
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfBranchedCosts
#print axioms L3.GrantDrainEntrance.grantDrainSharedBoundOfBranchedTwentyThree
