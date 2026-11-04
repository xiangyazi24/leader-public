import Leader.PPL.Elim.TransferClosed
import Leader.PPL.Probability.RestartCost
import Leader.PPL.Predicates
import Init.Omega

/-!
# Literal Algorithm-5 elimination interface for P_PL Lemma 17

The frozen R10 interface is a finite-word cost statement on the literal
four-field Algorithm-5 quotient.  The parameter psi is quantified explicitly
because the headline architecture quantifies C17 before n and psi, even
though the quotient itself erases psi.

The full P_PL-prime process is not identified with Algorithm 5.  It still
runs DetermineMode and the forced-Construct Algorithms 2 and 3.  The exact
remaining full-state seam is the projection bridge stated below.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

abbrev LiteralElimConfig (n : Nat) :=
  PPL.Convergence.LDLocal.Config n

/-- Literal Algorithm-5 dynamics on the four-field quotient. -/
def literalElim {n : Nat} (ring : DirectedRing n) :
    LiteralElimConfig n -> Fin n -> LiteralElimConfig n :=
  PPL.Convergence.LDLocal.stepE ring

/-- Lemma-17 target: exactly one remaining leader. -/
def LiteralL1 {n : Nat} (C : LiteralElimConfig n) : Prop :=
  PPL.Elim.leaderCount C = 1

/--
Frozen R10 cost-numerator interface.

C17 is outside n and psi.  For every literal four-field PB state and every
finite raw horizon T, the truncated first-hit cost to one leader is at most
C17*n^2 normalized interactions.
-/
def LiteralElimExpected (C17 : Nat) : Prop :=
  forall {n psi : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n) (C : LiteralElimConfig n),
    PPL.Elim.PB ring C ->
    forall T : Nat,
      costNumerator (literalElim ring) LiteralL1 C T <=
        n ^ T * (C17 * n * n)

/--
The proved LD(736) transfer closes the frozen interface with
1172*736 = 862592.
-/
theorem literalElimExpected_of_producers
    (hAttempt :
      PPL.Convergence.LDLocal.ModerateAttemptProducerSpec)
    (hPhysical :
      PPL.Convergence.LDLocal.LongBoundaryPhysicalSpec) :
    LiteralElimExpected 862592 := by
  unfold LiteralElimExpected
  intro n psi hn2 ring C hPB T
  exact
    PPL.Convergence.LDTransfer.one_leader_costNumerator_of_producers
      hAttempt hPhysical hn2 ring C hPB T


/-! ## Exact full-state seam still needed by P_PL-prime -/

/--
The CPB part of the frozen CPBView bridge.

Predicates.lean already has a tuple-valued four-field view; the LD repair uses
Elim.Cell4.  This proposition states the exact equivalence needed to move a
full P_PL state into the literal row-E PB domain.
-/
def CPBViewBridge : Prop :=
  forall {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPL.Config n psi kappa),
    PPL.CPB ring C <->
      PPL.Elim.PB ring (PPL.Elim.viewConfig C)

/--
The exact transition commuting square needed once the real P_PL-prime step
is installed.

P_PL-prime is not Algorithm 5 alone.  The intended proof expands one prime
step, proves that DetermineMode plus the forced-Construct Algorithms 2 and 3
leave view4 unchanged, and then uses step_view4_commutes for Algorithm 5.
-/
def PPrimeProjectionBridge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (primeStep :
      PPL.Config n psi kappa -> Fin n -> PPL.Config n psi kappa) :
    Prop :=
  forall C e,
    PPL.Elim.viewConfig (primeStep C e) =
      literalElim ring (PPL.Elim.viewConfig C) e

/--
The already-compiled Algorithm-5-only commuting square is exactly the
last stage of the future P_PL-prime projection proof.
-/
theorem eliminateOnly_projects_to_literal
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    PPrimeProjectionBridge ring
      (fun C e =>
        PopulationProtocol.step
          (PPL.Elim.eliminateOnlyProtocol psi kappa)
          ring C e) := by
  intro C e
  simpa [literalElim, PPL.Convergence.LDLocal.stepE] using
    (PPL.Elim.step_view4_commutes ring C e)


/-! ## PB-restricted restart carrier -/

abbrev PBState {n : Nat} (ring : DirectedRing n) :=
  {C : LiteralElimConfig n // PPL.Elim.PB ring C}

/--
Literal row-E step restricted to PB.  Closure is the proved pbStepClosure.
-/
def literalPBStep {n : Nat} (ring : DirectedRing n) :
    PBState ring -> Fin n -> PBState ring :=
  PPL.Probability.restartRestrictStep
    (literalElim ring)
    (PPL.Elim.PB ring)
    (fun C e hC =>
      PPL.Convergence.LDLocal.pbStepClosure ring C e hC)

/-- Read the one-leader target on the PB subtype. -/
def literalPBTarget {n : Nat} (ring : DirectedRing n) :
    PBState ring -> Prop :=
  PPL.Probability.restartRestrictTarget
    LiteralL1 (PPL.Elim.PB ring)

/--
Inside PB, one leader is closed.  This is exactly LastLeaderSurvival.
-/
theorem literalPBTarget_closed
    {n : Nat} (ring : DirectedRing n) :
    forall x : PBState ring, forall e : Fin n,
      literalPBTarget ring x ->
        literalPBTarget ring (literalPBStep ring x e) := by
  intro x e hx
  change PPL.Elim.leaderCount x.1 = 1 at hx
  change
    PPL.Elim.leaderCount (literalElim ring x.1 e) = 1
  exact
    PPL.Convergence.LDLocal.lastLeaderSurvival
      ring x.1 e x.2 hx

/-- PB restriction preserves the exact first-hit cost numerator. -/
theorem literalPB_costNumerator_eq
    {n : Nat} (ring : DirectedRing n)
    (C : LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C)
    (T : Nat) :
    costNumerator
        (literalPBStep ring)
        (literalPBTarget ring)
        (⟨C, hPB⟩ : PBState ring) T =
      costNumerator
        (literalElim ring) LiteralL1 C T := by
  simpa [literalPBStep, literalPBTarget] using
    (PPL.Probability.restartRestrict_costNumerator
      (literalElim ring)
      LiteralL1
      (PPL.Elim.PB ring)
      (fun D e hD =>
        PPL.Convergence.LDLocal.pbStepClosure ring D e hD)
      T C hPB)

/-- PB restriction also preserves the exact endpoint-miss numerator. -/
theorem literalPB_missWordSum_eq
    {n : Nat} (ring : DirectedRing n)
    (C : LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C)
    (T : Nat) :
    wordSum
        (literalPBStep ring)
        (miss (literalPBTarget ring))
        (⟨C, hPB⟩ : PBState ring) T =
      wordSum
        (literalElim ring)
        (miss LiteralL1) C T := by
  simpa [literalPBStep, literalPBTarget] using
    (PPL.Probability.restartRestrict_missWordSum
      (literalElim ring)
      LiteralL1
      (PPL.Elim.PB ring)
      (fun D e hD =>
        PPL.Convergence.LDLocal.pbStepClosure ring D e hD)
      T C hPB)

/--
Degenerate C17=0 case: the all-horizon expected-cost interface itself
forces every PB start to be already in L1.
-/
theorem literalElimExpected_zero_implies_L1
    (hExpected : LiteralElimExpected 0)
    {n psi : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n)
    (C : LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C) :
    LiteralL1 C := by
  by_cases hL1 : LiteralL1 C
  · exact hL1
  · have hcost :=
      hExpected (n := n) (psi := psi)
        hn2 ring C hPB 1
    have hsucc :
        costNumerator
            (literalElim ring) LiteralL1 C 1 = n := by
      have hz : ∀ m : Nat,
          (List.ofFn fun (_ : Fin m) => (0 : Nat)).sum = 0 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [List.ofFn_succ, List.sum_cons, ih]
      rw [costNumerator_succ
          (literalElim ring) LiteralL1 C hL1 0]
      simp only [costNumerator_zero, hz, Nat.add_zero, Nat.zero_add, Nat.pow_one]
    rw [hsucc] at hcost
    have hnzero : n <= 0 := by
      simpa using hcost
    omega

/--
Nat Markov conversion on the PB subtype.

The block is exactly 2*C17*n^2.  Target closure is supplied by
literalPBTarget_closed, while the cost envelope is transported from the raw
row by literalPB_costNumerator_eq.
-/
theorem literalPB_half_block_of_expected
    {C17 : Nat}
    (hExpected : LiteralElimExpected C17)
    (hC17 : 0 < C17)
    {n psi : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n)
    (x : PBState ring) :
    2 *
        wordSum
          (literalPBStep ring)
          (miss (literalPBTarget ring))
          x
          (2 * (C17 * n * n)) <=
      n ^ (2 * (C17 * n * n)) := by
  let M := C17 * n * n
  have hnpos : 0 < n := by
    omega
  have hM : 0 < M := by
    dsimp [M]
    exact
      Nat.mul_pos
        (Nat.mul_pos hC17 hnpos)
        hnpos
  have hcost :
      forall y : PBState ring,
        True ->
        Not (literalPBTarget ring y) ->
        forall T : Nat,
          costNumerator
              (literalPBStep ring)
              (literalPBTarget ring)
              y T <=
            n ^ T * M := by
    intro y _ _ T
    calc
      costNumerator
          (literalPBStep ring)
          (literalPBTarget ring)
          y T =
        costNumerator
          (literalElim ring) LiteralL1 y.1 T :=
        literalPB_costNumerator_eq ring y.1 y.2 T
      _ <= n ^ T * (C17 * n * n) :=
        hExpected (n := n) (psi := psi)
          hn2 ring y.1 y.2 T
      _ = n ^ T * M := by
        rfl
  have h :=
    PPL.Probability.markov_to_half_block
      (literalPBStep ring)
      (literalPBTarget ring)
      (fun _ : PBState ring => True)
      (literalPBTarget_closed ring)
      M hM hcost x True.intro
  simpa [M] using h

/--
Raw-row form of the same half-block estimate.  No probability independence is
used; restartRestrict_missWordSum is an exact finite-word identity.
-/
theorem literalElim_half_block_of_expected
    {C17 : Nat}
    (hExpected : LiteralElimExpected C17)
    (hC17 : 0 < C17)
    {n psi : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n)
    (C : LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C) :
    2 *
        wordSum
          (literalElim ring)
          (miss LiteralL1) C
          (2 * (C17 * n * n)) <=
      n ^ (2 * (C17 * n * n)) := by
  have h :=
    @literalPB_half_block_of_expected C17
      (@hExpected) hC17 n psi hn2 ring
      (⟨C, hPB⟩ : PBState ring)
  rw [literalPB_missWordSum_eq ring C hPB] at h
  exact h

end PPL

#print axioms PPL.literalElimExpected_of_producers
#print axioms PPL.eliminateOnly_projects_to_literal
#print axioms PPL.literalPBTarget_closed
#print axioms PPL.literalPB_costNumerator_eq
#print axioms PPL.literalPB_missWordSum_eq
#print axioms PPL.literalElimExpected_zero_implies_L1
#print axioms PPL.literalPB_half_block_of_expected
#print axioms PPL.literalElim_half_block_of_expected
