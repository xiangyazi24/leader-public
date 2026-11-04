import Leader.PPL.SequentialClock.CostSmallN
import Leader.PPL.MainTheorem.LocalStepProtocolStep

/-!
# Superseded: the small-n producer and amplification

Part of the second (sequential five-event) generation of the P_PL Theorem 1
statement, stated at the superseded clock `Superseded.theorem1Kappa` and
horizon `Superseded.theorem1Horizon`.  Not imported by the proved headline
`PPL.theorem1Statement_proved`.  Replaced by `Leader/PPL/MainTheorem/LocalStepProtocolStep.lean`; the reason for the
replacement is recorded in `Leader/PPL/SequentialClock/Statement.lean`.
Kept, under `PPL.Superseded`, so the recorded history stays checkable.
-/


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol


private def Superseded.theorem1SmallNSPLTest
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (SPL ring C)


private theorem Superseded.theorem1SmallNSPLTest_spec
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Superseded.theorem1SmallNSPLTest ring C = true ↔
      SPL ring C := by
  simp [Superseded.theorem1SmallNSPLTest]


private theorem Superseded.theorem1SmallNSPL_localStepClosed
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    LocalStepClosed
      ring
      (PPL.protocol psi kappa).transition
      (SPL ring) := by
  intro C hC e
  show
    SPL ring
      (localStep ring
        (PPL.protocol psi kappa).transition
        (C : Config n psi kappa) e)
  have heq :=
    theorem1SmallN_localStep_eq_protocolStep
      ring (C : Config n psi kappa) e
  unfold SPL at hC ⊢
  rcases hC with ⟨root, hroot⟩
  have hstep :=
    PPL.Safety.SPL.splAt_closed
      hlocal hn3 hpsi ring root C e hroot
  refine ⟨root, ?_⟩
  first
    | exact hstep
    | (rw [heq]; exact hstep)
    | (simp only [heq]; exact hstep)


private theorem Superseded.theorem1SmallNLocalMiss_zero_of_safe
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hC : SPL ring C)
    (T : Nat) :
    localMissCount
        ring
        (PPL.protocol psi kappa).transition
        (Superseded.theorem1SmallNSPLTest ring)
        C T =
      0 := by
  unfold localMissCount
  apply List.countP_eq_zero.mpr
  intro word _hword hbad
  have hstart :
      Superseded.theorem1SmallNSPLTest ring C = true :=
    (Superseded.theorem1SmallNSPLTest_spec ring C).2 hC
  have hhit :
      hitsWithinLocal
          ring
          (PPL.protocol psi kappa).transition
          (Superseded.theorem1SmallNSPLTest ring)
          C word =
        true :=
    hitsWithinLocal_of_initial
      ring
      (PPL.protocol psi kappa).transition
      (Superseded.theorem1SmallNSPLTest ring)
      C word hstart
  change
    (!hitsWithinLocal
        ring
        (PPL.protocol psi kappa).transition
        (Superseded.theorem1SmallNSPLTest ring)
        C word) =
      true at hbad
  rw [hhit] at hbad
  contradiction


/--
For a closed SPL target, the generic prefix-miss counter is exactly the
endpoint miss numerator used by Theorem1CostSmallN.
-/
private theorem Superseded.theorem1SmallN_endpointMiss_eq_localMiss
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) :
    wordSum
        (localStep ring
          (PPL.protocol psi kappa).transition)
        (miss (SPL ring))
        C T =
      localMissCount
        ring
        (PPL.protocol psi kappa).transition
        (Superseded.theorem1SmallNSPLTest ring)
        C T := by
  classical

  have hclosed :
      LocalStepClosed
        ring
        (PPL.protocol psi kappa).transition
        (SPL ring) :=
    Superseded.theorem1SmallNSPL_localStepClosed
      hlocal hn3 hpsi ring

  have hclosed' :
      ∀ D e,
        SPL ring D →
          SPL ring
            (localStep ring
              (PPL.protocol psi kappa).transition
              D e) := by
    intro D e hD
    exact hclosed D hD e

  induction T generalizing C with
  | zero =>
      by_cases hC : SPL ring C
      · have ht :
            Superseded.theorem1SmallNSPLTest ring C = true :=
          (Superseded.theorem1SmallNSPLTest_spec ring C).2 hC
        simp [
          wordSum,
          localMissCount,
          allSchedules,
          hitsWithinLocal,
          Superseded.theorem1SmallNSPLTest,
          miss,
          FiniteUniformStoppingTree.treeWeight,
          LeaderCountDyadicTail.rawWeight,
          hC,
          ht
        ]
      · have ht :
            Superseded.theorem1SmallNSPLTest ring C = false := by
          cases hs :
              Superseded.theorem1SmallNSPLTest ring C with
          | false =>
              rfl
          | true =>
              exact
                False.elim
                  (hC
                    ((Superseded.theorem1SmallNSPLTest_spec
                      ring C).1 hs))
        simp [
          wordSum,
          localMissCount,
          allSchedules,
          hitsWithinLocal,
          Superseded.theorem1SmallNSPLTest,
          miss,
          FiniteUniformStoppingTree.treeWeight,
          LeaderCountDyadicTail.rawWeight,
          hC,
          ht
        ]

  | succ T ih =>
      by_cases hC : SPL ring C
      · have hz :
            wordSum
                (localStep ring
                  (PPL.protocol psi kappa).transition)
                (miss (SPL ring))
                C (T + 1) =
              0 :=
          miss_zero
            (localStep ring
              (PPL.protocol psi kappa).transition)
            (SPL ring)
            hclosed'
            C hC (T + 1)
        rw [hz]
        symm
        exact
          Superseded.theorem1SmallNLocalMiss_zero_of_safe
            ring C hC (T + 1)

      · have hCtest :
            Superseded.theorem1SmallNSPLTest ring C = false := by
          cases hs :
              Superseded.theorem1SmallNSPLTest ring C with
          | false =>
              rfl
          | true =>
              exact
                False.elim
                  (hC
                    ((Superseded.theorem1SmallNSPLTest_spec
                      ring C).1 hs))

        change
          wordSum
              (localStep ring
                  (PPL.protocol psi kappa).transition :
                Config n psi kappa → Fin n → Config n psi kappa)
              (miss (SPL ring))
              C (T + 1) =
            localMissCount
              ring
              (PPL.protocol psi kappa).transition
              (Superseded.theorem1SmallNSPLTest ring)
              C (T + 1)
        first
          | rw [LeaderCountDyadicTail.wordSum_succ]
          | erw [LeaderCountDyadicTail.wordSum_succ]
        rw [show T + 1 = 1 + T by omega]
        first
          | rw [PPLLSchedulerBlocks.localMissCount_add_eq_sum]
          | erw [PPLLSchedulerBlocks.localMissCount_add_eq_sum]

        have hone :
            allSchedules n 1 =
              List.ofFn
                (fun e : Fin n => [e]) := by
          simp [allSchedules]
        rw [hone, List.map_ofFn]

        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e

        let C' : Config n psi kappa :=
          localStep ring
            (PPL.protocol psi kappa).transition C e

        by_cases hC' : SPL ring C'
        · have hC'test :
              Superseded.theorem1SmallNSPLTest ring C' = true :=
            (Superseded.theorem1SmallNSPLTest_spec ring C').2 hC'
          have hhit :
              hitsWithinLocal
                  ring
                  (PPL.protocol psi kappa).transition
                  (Superseded.theorem1SmallNSPLTest ring)
                  C [e] =
                true := by
            simp [
              hitsWithinLocal,
              hCtest,
              C',
              hC'test
            ]
          have hzero :
              localMissCount
                  ring
                  (PPL.protocol psi kappa).transition
                  (Superseded.theorem1SmallNSPLTest ring)
                  C' T =
                0 :=
            Superseded.theorem1SmallNLocalMiss_zero_of_safe
              ring C' hC' T
          rw [ih C', hzero]
          simp [hhit, runLocalSchedule, C']

        · have hC'test :
              Superseded.theorem1SmallNSPLTest ring C' = false := by
            cases hs :
                Superseded.theorem1SmallNSPLTest ring C' with
            | false =>
                rfl
            | true =>
                exact
                  False.elim
                    (hC'
                      ((Superseded.theorem1SmallNSPLTest_spec
                        ring C').1 hs))
          have hhit :
              hitsWithinLocal
                  ring
                  (PPL.protocol psi kappa).transition
                  (Superseded.theorem1SmallNSPLTest ring)
                  C [e] =
                false := by
            simp [
              hitsWithinLocal,
              hCtest,
              C',
              hC'test
            ]
          rw [ih C']
          simp [hhit, runLocalSchedule, C']


/--
Uniform arbitrary-start SPL producer for the admissible small parameter pairs.

The same absolute cAmp controls both the raw producer length and, crucially,
the amplified horizon
  ((n-1)*(n^L-1)+1)*L.
The second bound is what makes the later expected-cost algebra close.
-/
def Superseded.Theorem1SmallNProducer : Prop :=
  ∃ cAmp : Nat,
    And
      (1 ≤ cAmp)
      (∀ {n psi : Nat},
        3 ≤ n →
        n < 52 →
        2 ≤ psi →
        n ≤ 2 ^ psi →
        psi ≤ theorem1K n →
        ∃ L : Nat,
          And
            (0 < L)
            (And
              (L ≤
                cAmp * Superseded.theorem1Horizon n psi)
              (And
                (((n - 1) * (n ^ L - 1) + 1) * L ≤
                  cAmp * Superseded.theorem1Horizon n psi)
                (∀ ring : DirectedRing n,
                  BoundedSafeScheduleProducer
                    ring
                    (PPL.protocol
                      psi
                      (Superseded.theorem1Kappa psi)).transition
                    (fun _ => True)
                    (SPL ring)
                    L))))


/--
The bounded arbitrary-start producer supplies the small-n half-failure
contract consumed by Theorem1CostSmallN.
-/
theorem Superseded.theorem1SmallNAmplification_of_producer
    (h : Superseded.Theorem1SmallNProducer)
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp) :
    Superseded.Theorem1SmallNAmplification := by
  rcases h with
    ⟨cAmp, hcAmp, hproducer⟩

  refine
    ⟨2 * cAmp, by omega, ?_⟩

  intro n psi
  intro hn3 hn52 hpsi hnpow hpsiK

  rcases
      hproducer
        hn3 hn52 hpsi hnpow hpsiK with
    ⟨L, hL, hLbasic, hamp, hproducerRing⟩

  let k : Nat :=
    (n - 1) * (n ^ L - 1) + 1
  let B : Nat :=
    k * L

  have hk : 0 < k := by
    simp [k]
  have hB : 0 < B :=
    Nat.mul_pos hk hL

  refine
    ⟨B, hB, ?_, ?_⟩

  · have hamp' :
        B ≤
          cAmp * Superseded.theorem1Horizon n psi := by
      simpa [B, k] using hamp
    calc
      2 * B ≤
          2 *
            (cAmp * Superseded.theorem1Horizon n psi) :=
        Nat.mul_le_mul_left 2 hamp'
      _ =
          (2 * cAmp) *
            Superseded.theorem1Horizon n psi := by
        ac_rfl

  · intro ring C

    have hDomainClosed :
        LocalStepClosed
          ring
          (PPL.protocol
            psi
            (Superseded.theorem1Kappa psi)).transition
          (fun _ => True) := by
      intro D _hD e
      exact True.intro

    have hphase0 :=
      boundedSafeProducer_explicitOneOverNPhase
        ring
        (PPL.protocol
          psi
          (Superseded.theorem1Kappa psi)).transition
        (fun _ => True)
        (SPL ring)
        (Superseded.theorem1SmallNSPLTest ring)
        (Superseded.theorem1SmallNSPLTest_spec ring)
        hDomainClosed
        (by omega : 1 < n)
        L hL
        (hproducerRing ring)

    dsimp only at hphase0

    have hphase :
        UniformFinitePhase
          ring
          (PPL.protocol
            psi
            (Superseded.theorem1Kappa psi)).transition
          (fun _ => True)
          (SPL ring)
          (Superseded.theorem1SmallNSPLTest ring)
          B
          (n ^ (B - 1)) := by
      simpa [B, k] using hphase0.2

    have hcount :=
      hphase.2 C True.intro

    have hpartition :=
      localMissCount_add_localHitCount
        ring
        (PPL.protocol
          psi
          (Superseded.theorem1Kappa psi)).transition
        (Superseded.theorem1SmallNSPLTest ring)
        C B

    rw [allSchedules_length] at hcount hpartition

    have hmiss :
        localMissCount
            ring
            (PPL.protocol
              psi
              (Superseded.theorem1Kappa psi)).transition
            (Superseded.theorem1SmallNSPLTest ring)
            C B ≤
          n ^ (B - 1) := by
      omega

    have hBsucc :
        B = (B - 1) + 1 := by
      omega

    have hpow :
        2 * n ^ (B - 1) ≤
          n ^ B := by
      calc
        2 * n ^ (B - 1) =
            n ^ (B - 1) * 2 := by
          ac_rfl
        _ ≤
            n ^ (B - 1) * n :=
          Nat.mul_le_mul_left
            (n ^ (B - 1)) (by omega)
        _ =
            n ^ ((B - 1) + 1) := by
          rw [Nat.pow_succ]
        _ =
            n ^ B := by
          rw [← hBsucc]

    change
      2 *
          wordSum
            (fun
              (D : Config n psi (Superseded.theorem1Kappa psi))
              (e : Fin n) =>
                localStep
                  ring
                  (PPL.protocol
                    psi
                    (Superseded.theorem1Kappa psi)).transition
                  D e)
            (miss (SPL ring))
            C B ≤
        n ^ B

    have hmissEq :=
      Superseded.theorem1SmallN_endpointMiss_eq_localMiss
        hlocal hn3 hpsi ring C B

    change
      wordSum
          (fun
            (D : Config n psi (Superseded.theorem1Kappa psi))
            (e : Fin n) =>
              localStep
                ring
                (PPL.protocol
                  psi
                  (Superseded.theorem1Kappa psi)).transition
                D e)
          (miss (SPL ring))
          C B =
        localMissCount
          ring
          (PPL.protocol
            psi
            (Superseded.theorem1Kappa psi)).transition
          (Superseded.theorem1SmallNSPLTest ring)
          C B at hmissEq

    rw [hmissEq]

    exact
      Nat.le_trans
        (Nat.mul_le_mul_left 2 hmiss)
        hpow


end PPL


#print axioms PPL.Superseded.theorem1SmallNAmplification_of_producer
