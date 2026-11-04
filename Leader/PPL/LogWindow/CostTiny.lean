import Leader.PPL.MainTheorem.LocalStepProtocolStep
import Leader.PPL.MainTheorem.MissAmplification
import Leader.Wu.Scheduler.ClosedDomainAmplification
import Leader.PPL.LogWindow.CostMid

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/LocalStepProtocolStep.lean`

Moved out of `Leader/PPL/MainTheorem/LocalStepProtocolStep.lean` by the P_PL Theorem 1 cleanup, phase 2.
These declarations served only the original psi <= log2 n + 1 route to
`PPL.theorem1Statement_proved`, which now goes through
`PPL.theorem1Statement_proved_via_slack` (`Leader/PPL/MainTheorem/PsiWindowSlack.lean`).
Nothing in the live Theorem 1 closure uses them; they are kept, and still build,
as the record of that route.  Every name `PPL.X` became `PPL.Superseded.LogWindow.X`;
see `research-map/RENAME_MAP_PPL.md` (phase 2).
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol
namespace PPL.Superseded.LogWindow

/--
For every admissible tiny parameter pair, one bounded arbitrary-start
producer length exists.  The length is uniform over the directed ring, but
may depend on the pair (n, psi).
-/
def Theorem1TinyProducer : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    n <= 64 ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    exists L : Nat,
      forall ring : DirectedRing n,
        BoundedSafeScheduleProducer
          ring
          (PPL.protocol
            psi
            (theorem1Kappa psi)).transition
          (fun _ => True)
          (SPL ring)
          L

/--
The finite-pair strengthening used internally by the cost proof: one positive
length works for every admissible tiny pair.
-/
def Theorem1TinyUniformProducer : Prop :=
  exists L : Nat,
    0 < L /\
    forall {n psi : Nat},
      3 <= n ->
      n <= 64 ->
      2 <= psi ->
      n <= 2 ^ psi ->
      psi <= theorem1K n ->
      forall ring : DirectedRing n,
        BoundedSafeScheduleProducer
          ring
          (PPL.protocol
            psi
            (theorem1Kappa psi)).transition
          (fun _ => True)
          (SPL ring)
          L

private theorem theorem1TinyProducer_mono
    {Q : Type}
    {n L M : Nat}
    (ring : DirectedRing n)
    (T : Q -> Q -> Q × Q)
    (Domain Safe : (Fin n -> Q) -> Prop)
    (hLM : L <= M)
    (h :
      BoundedSafeScheduleProducer
        ring T Domain Safe L) :
    BoundedSafeScheduleProducer
      ring T Domain Safe M := by
  intro C hC hnot
  rcases h C hC hnot with
    ⟨word, hword, hsafe⟩
  exact
    ⟨word,
      Nat.le_trans hword hLM,
      hsafe⟩

/--
For one fixed n, finitely many psi <= theorem1K n can be absorbed into one
positive producer length.  No enumeration, Fintype, Finset, or computation of
Nat powers is used.
-/
private theorem theorem1Tiny_uniformPsiBound
    (h : Theorem1TinyProducer)
    {n : Nat}
    (hn3 : 3 <= n)
    (hn64 : n <= 64) :
    exists M : Nat,
      0 < M /\
      forall {psi : Nat},
        2 <= psi ->
        n <= 2 ^ psi ->
        psi <= theorem1K n ->
        forall ring : DirectedRing n,
          BoundedSafeScheduleProducer
            ring
            (PPL.protocol
              psi
              (theorem1Kappa psi)).transition
            (fun _ => True)
            (SPL ring)
            M := by
  unfold Theorem1TinyProducer at h

  have haux :
      forall K : Nat,
        exists M : Nat,
          0 < M /\
          forall {psi : Nat},
            psi <= K ->
            2 <= psi ->
            n <= 2 ^ psi ->
            psi <= theorem1K n ->
            forall ring : DirectedRing n,
              BoundedSafeScheduleProducer
                ring
                (PPL.protocol
                  psi
                  (theorem1Kappa psi)).transition
                (fun _ => True)
                (SPL ring)
                M := by
    intro K
    induction K with
    | zero =>
        refine ⟨1, by omega, ?_⟩
        intro psi hpsi0 hpsi2
        omega

    | succ K ih =>
        rcases ih with
          ⟨M, hMpos, hprev⟩

        by_cases hadm :
            2 <= K + 1 /\
            n <= 2 ^ (K + 1) /\
            K + 1 <= theorem1K n

        · rcases hadm with
            ⟨hnew2, hnewPow, hnewK⟩

          rcases
              h
                (n := n)
                (psi := K + 1)
                hn3 hn64
                hnew2 hnewPow hnewK with
            ⟨L, hLproducer⟩

          let M' : Nat :=
            M + L + 1

          refine
            ⟨M', by
              dsimp [M']
              omega, ?_⟩

          intro psi
          intro hpsiSucc hpsi2 hpsiPow hpsiK
          intro ring

          by_cases hle : psi <= K
          · exact
              theorem1TinyProducer_mono
                ring
                (PPL.protocol
                  psi
                  (theorem1Kappa psi)).transition
                (fun _ => True)
                (SPL ring)
                (by
                  dsimp [M']
                  omega)
                (hprev
                  hle
                  hpsi2
                  hpsiPow
                  hpsiK
                  ring)

          · have heq :
                psi = K + 1 := by
              omega
            subst psi
            exact
              theorem1TinyProducer_mono
                ring
                (PPL.protocol
                  (K + 1)
                  (theorem1Kappa (K + 1))).transition
                (fun _ => True)
                (SPL ring)
                (by
                  dsimp [M']
                  omega)
                (hLproducer ring)

        · refine
            ⟨M, hMpos, ?_⟩

          intro psi
          intro hpsiSucc hpsi2 hpsiPow hpsiK
          intro ring

          have hle :
              psi <= K := by
            refine Nat.le_of_not_lt ?_
            intro hnot
            have heq :
                psi = K + 1 := by
              omega
            subst psi
            exact
              hadm
                ⟨hpsi2,
                  hpsiPow,
                  hpsiK⟩

          exact
            hprev
              hle
              hpsi2
              hpsiPow
              hpsiK
              ring

  rcases
      haux (theorem1K n) with
    ⟨M, hMpos, hMproducer⟩

  refine
    ⟨M, hMpos, ?_⟩

  intro psi
  intro hpsi2 hpsiPow hpsiK
  intro ring

  exact
    hMproducer
      hpsiK
      hpsi2
      hpsiPow
      hpsiK
      ring

/--
The finite parameter window turns the pairwise producer into one absolute
positive producer length.
-/
theorem theorem1TinyUniformProducer_of_producer
    (h : Theorem1TinyProducer) :
    Theorem1TinyUniformProducer := by
  unfold Theorem1TinyUniformProducer

  have haux :
      forall N : Nat,
        N <= 64 ->
        exists M : Nat,
          0 < M /\
          forall {n psi : Nat},
            3 <= n ->
            n <= N ->
            2 <= psi ->
            n <= 2 ^ psi ->
            psi <= theorem1K n ->
            forall ring : DirectedRing n,
              BoundedSafeScheduleProducer
                ring
                (PPL.protocol
                  psi
                  (theorem1Kappa psi)).transition
                (fun _ => True)
                (SPL ring)
                M := by
    intro N
    induction N with
    | zero =>
        intro _h064
        refine
          ⟨1, by omega, ?_⟩
        intro n psi hn3 hn0
        omega

    | succ N ih =>
        intro hN64

        have hN64' :
            N <= 64 := by
          omega

        rcases
            ih hN64' with
          ⟨M, hMpos, hprev⟩

        by_cases hnew3 :
            3 <= N + 1

        · have hnew64 :
              N + 1 <= 64 := by
            omega

          rcases
              theorem1Tiny_uniformPsiBound
                h
                hnew3
                hnew64 with
            ⟨Mnew, hMnewPos, hnew⟩

          let M' : Nat :=
            M + Mnew

          refine
            ⟨M', by
              dsimp [M']
              omega, ?_⟩

          intro n psi
          intro hn3 hnSucc
          intro hpsi2 hpsiPow hpsiK
          intro ring

          by_cases hle :
              n <= N

          · exact
              theorem1TinyProducer_mono
                ring
                (PPL.protocol
                  psi
                  (theorem1Kappa psi)).transition
                (fun _ => True)
                (SPL ring)
                (by
                  dsimp [M']
                  omega)
                (hprev
                  hn3
                  hle
                  hpsi2
                  hpsiPow
                  hpsiK
                  ring)

          · have heq :
                n = N + 1 := by
              omega
            subst n

            exact
              theorem1TinyProducer_mono
                ring
                (PPL.protocol
                  psi
                  (theorem1Kappa psi)).transition
                (fun _ => True)
                (SPL ring)
                (by
                  dsimp [M']
                  omega)
                (hnew
                  hpsi2
                  hpsiPow
                  hpsiK
                  ring)

        · refine
            ⟨M, hMpos, ?_⟩

          intro n psi
          intro hn3 hnSucc
          intro hpsi2 hpsiPow hpsiK
          intro ring

          have hle :
              n <= N := by
            refine Nat.le_of_not_lt ?_
            intro hnot
            have heq :
                n = N + 1 := by
              omega
            subst n
            exact
              hnew3 hn3

          exact
            hprev
              hn3
              hle
              hpsi2
              hpsiPow
              hpsiK
              ring

  rcases
      haux 64 (by omega) with
    ⟨L, hL, hproducer⟩

  refine
    ⟨L, hL, ?_⟩

  intro n psi
  intro hn3 hn64
  intro hpsi2 hpsiPow hpsiK
  intro ring

  exact
    hproducer
      hn3
      hn64
      hpsi2
      hpsiPow
      hpsiK
      ring

private def theorem1TinyBlock
    (n L : Nat) : Nat :=
  ((n - 1) * (n ^ L - 1) + 1) * L

private theorem theorem1TinyBlock_pos
    {n L : Nat}
    (hL : 0 < L) :
    0 < theorem1TinyBlock n L := by
  unfold theorem1TinyBlock
  apply Nat.mul_pos
  · omega
  · exact hL

private theorem theorem1TinyBlock_le_64
    {n L : Nat}
    (hn64 : n <= 64) :
    theorem1TinyBlock n L <=
      theorem1TinyBlock 64 L := by
  unfold theorem1TinyBlock

  have hsub :
      n - 1 <= 64 - 1 := by
    omega

  have hpow :
      n ^ L <= 64 ^ L :=
    Nat.pow_le_pow_left hn64 L

  have hpowSub :
      n ^ L - 1 <= 64 ^ L - 1 := by
    omega

  have hmul :
      (n - 1) * (n ^ L - 1) <=
        (64 - 1) * (64 ^ L - 1) := by
    calc
      (n - 1) * (n ^ L - 1) <=
          (64 - 1) * (n ^ L - 1) :=
        Nat.mul_le_mul_right
          (n ^ L - 1)
          hsub
      _ <=
          (64 - 1) * (64 ^ L - 1) :=
        Nat.mul_le_mul_left
          (64 - 1)
          hpowSub

  exact
    Nat.mul_le_mul_right
      L
      (Nat.add_le_add_right hmul 1)

private def theorem1TinySPLTest
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (SPL ring C)

private theorem theorem1TinySPLTest_spec
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    theorem1TinySPLTest ring C = true <->
      SPL ring C := by
  simp [theorem1TinySPLTest]

/--
The Theorem-1 prefix Boolean is exactly the generic local hitting Boolean.
The only adapter is theorem1SmallN_localStep_eq_protocolStep from
Leader/PPL/SequentialClock/CostSmallNProducer.lean.
-/
private theorem theorem1TinyReaches_eq_hits
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    theorem1ReachesSPL ring C word =
      hitsWithinLocal
        ring
        (PPL.protocol psi kappa).transition
        (theorem1TinySPLTest ring)
        C word := by
  induction word generalizing C with
  | nil =>
      rfl

  | cons e rest ih =>
      simp only
        [theorem1ReachesSPL,
          hitsWithinLocal]

      rw [
        theorem1SmallN_localStep_eq_protocolStep
          ring C e
      ]

      change
        (decide (SPL ring C) ||
            theorem1ReachesSPL
              ring
              (PopulationProtocol.step
                (PPL.protocol psi kappa)
                ring C e)
              rest) =
          (decide (SPL ring C) ||
            hitsWithinLocal
              ring
              (PPL.protocol psi kappa).transition
              (theorem1TinySPLTest ring)
              (PopulationProtocol.step
                (PPL.protocol psi kappa)
                ring C e)
              rest)

      rw [ih]

private theorem theorem1TinyFailure_eq_localMiss
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) :
    theorem1FailureNumerator ring C T =
      localMissCount
        ring
        (PPL.protocol psi kappa).transition
        (theorem1TinySPLTest ring)
        C T := by
  unfold
    theorem1FailureNumerator
    PPLLSchedulerBlocks.localMissCount

  apply
    congrArg
      (fun p : DetSchedule n -> Bool =>
        (allSchedules n T).countP p)

  funext word

  rw [
    theorem1TinyReaches_eq_hits
      ring C word
  ]

/--
Closure converts the prefix miss count to the endpoint miss wordSum consumed
by FiniteAccounting.cost_le_two_blocks.
-/
private theorem theorem1TinyEndpointMiss_eq_localMiss
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (T : Nat) :
    wordSum
        (fun D e =>
          PopulationProtocol.step
            (PPL.protocol
              psi
              (theorem1Kappa psi))
            ring D e)
        (miss (SPL ring))
        C T =
      localMissCount
        ring
        (PPL.protocol
          psi
          (theorem1Kappa psi)).transition
        (theorem1TinySPLTest ring)
        C T := by
  have hclosed :=
    theorem1SPL_closed_of_local
      hlocal
      hn3
      hpsi
      ring

  rw [
    <-
      theorem1FailureNumerator_eq_wordSum_miss
        ring
        hclosed
        C
        T
  ]

  exact
    theorem1TinyFailure_eq_localMiss
      ring C T

/--
One arbitrary-start producer of length L gives a half-failure block at
B(n,L) = ((n-1)(n^L-1)+1)L.

The amplification algebra is the same as
Superseded.theorem1SmallNAmplification_of_producer in
Leader/PPL/SequentialClock/CostSmallNProducer.lean.
-/
private theorem theorem1TinyHalfFailure_of_producer
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (L : Nat)
    (hL : 0 < L)
    (hproducer :
      forall ring : DirectedRing n,
        BoundedSafeScheduleProducer
          ring
          (PPL.protocol
            psi
            (theorem1Kappa psi)).transition
          (fun _ => True)
          (SPL ring)
          L)
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi)) :
    2 *
        wordSum
          (fun D e =>
            PopulationProtocol.step
              (PPL.protocol
                psi
                (theorem1Kappa psi))
              ring D e)
          (miss (SPL ring))
          C
          (theorem1TinyBlock n L) <=
      n ^ theorem1TinyBlock n L := by
  let k : Nat :=
    (n - 1) * (n ^ L - 1) + 1

  let B : Nat :=
    k * L

  have hk :
      0 < k := by
    simp [k]

  have hB :
      0 < B :=
    Nat.mul_pos hk hL

  have hDomainClosed :
      LocalStepClosed
        ring
        (PPL.protocol
          psi
          (theorem1Kappa psi)).transition
        (fun _ => True) := by
    intro D _hD e
    exact True.intro

  have hphase0 :=
    boundedSafeProducer_explicitOneOverNPhase
      ring
      (PPL.protocol
        psi
        (theorem1Kappa psi)).transition
      (fun _ => True)
      (SPL ring)
      (theorem1TinySPLTest ring)
      (theorem1TinySPLTest_spec ring)
      hDomainClosed
      (by omega : 1 < n)
      L
      hL
      (hproducer ring)

  dsimp only at hphase0

  have hphase :
      UniformFinitePhase
        ring
        (PPL.protocol
          psi
          (theorem1Kappa psi)).transition
        (fun _ => True)
        (SPL ring)
        (theorem1TinySPLTest ring)
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
        (theorem1Kappa psi)).transition
      (theorem1TinySPLTest ring)
      C B

  rw [allSchedules_length] at hcount hpartition

  have hmiss :
      localMissCount
          ring
          (PPL.protocol
            psi
            (theorem1Kappa psi)).transition
          (theorem1TinySPLTest ring)
          C B <=
        n ^ (B - 1) := by
    omega

  have hBsucc :
      B = (B - 1) + 1 := by
    omega

  have hpow :
      2 * n ^ (B - 1) <=
        n ^ B := by
    calc
      2 * n ^ (B - 1) =
          n ^ (B - 1) * 2 := by
        ac_rfl
      _ <=
          n ^ (B - 1) * n :=
        Nat.mul_le_mul_left
          (n ^ (B - 1))
          (by omega)
      _ =
          n ^ ((B - 1) + 1) := by
        rw [Nat.pow_succ]
      _ =
          n ^ B := by
        rw [<- hBsucc]

  have hmissEq :=
    theorem1TinyEndpointMiss_eq_localMiss
      hlocal
      hn3
      hpsi
      ring
      C
      B

  have hhalf :
      2 *
          wordSum
            (fun D e =>
              PopulationProtocol.step
                (PPL.protocol
                  psi
                  (theorem1Kappa psi))
                ring D e)
            (miss (SPL ring))
            C B <=
        n ^ B := by
    rw [hmissEq]

    exact
      Nat.le_trans
        (Nat.mul_le_mul_left 2 hmiss)
        hpow

  simpa
    [theorem1TinyBlock, B, k]
    using hhalf

/--
The finite tiny producer implies the absolute tiny-n expected-cost leaf.
-/
theorem theorem1TinyNCost_of_producer
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (h : Theorem1TinyProducer) :
    Theorem1TinyNCost := by
  have huniform :=
    theorem1TinyUniformProducer_of_producer h

  unfold Theorem1TinyUniformProducer at huniform

  rcases huniform with
    ⟨L, hL, hproducer⟩

  let Bmax : Nat :=
    theorem1TinyBlock 64 L

  let cTiny : Nat :=
    2 * Bmax

  have hBmaxPos :
      0 < Bmax := by
    dsimp [Bmax]
    exact
      theorem1TinyBlock_pos hL

  refine
    ⟨cTiny, ?_, ?_⟩

  · dsimp [cTiny]
    omega

  · intro n psi
    intro hn3 hn64 hpsi hnpow hpsiK
    intro ring C0 T

    have hproducerRing :
        forall r : DirectedRing n,
          BoundedSafeScheduleProducer
            r
            (PPL.protocol
              psi
              (theorem1Kappa psi)).transition
            (fun _ => True)
            (SPL r)
            L :=
      hproducer
        (n := n)
        (psi := psi)
        hn3
        hn64
        hpsi
        hnpow
        hpsiK

    let B : Nat :=
      theorem1TinyBlock n L

    have hB :
        0 < B := by
      dsimp [B]
      exact
        theorem1TinyBlock_pos hL

    have hblock :
        forall
          D :
            Config
              n
              psi
              (theorem1Kappa psi),
          2 *
              wordSum
                (fun E e =>
                  PopulationProtocol.step
                    (PPL.protocol
                      psi
                      (theorem1Kappa psi))
                    ring E e)
                (miss (SPL ring))
                D B <=
            n ^ B := by
      intro D

      simpa [B] using
        theorem1TinyHalfFailure_of_producer
          hlocal
          hn3
          hpsi
          L
          hL
          hproducerRing
          ring
          D

    have hclosed :=
      theorem1SPL_closed_of_local
        hlocal
        hn3
        hpsi
        ring

    have hcost :=
      cost_le_two_blocks
        (fun D e =>
          PopulationProtocol.step
            (PPL.protocol
              psi
              (theorem1Kappa psi))
            ring D e)
        (SPL ring)
        hclosed
        B
        hB
        hblock

    have hraw :
        theorem1CostNumerator
            ring C0 T <=
          n ^ T * (2 * B) := by
      simpa [theorem1CostNumerator]
        using hcost T C0

    have hB_le :
        B <= Bmax := by
      dsimp [B, Bmax]
      exact
        theorem1TinyBlock_le_64 hn64

    have hnpos :
        0 < n := by
      omega

    have h15 :
        0 <
          PPL.Convergence.ReachCPB.lemma16H15
            n := by
      unfold
        PPL.Convergence.ReachCPB.lemma16H15
      exact
        Nat.mul_pos
          (Nat.mul_pos
            (by omega)
            hnpos)
          (by omega)

    have h16 :
        0 <
          PPL.Convergence.ReachCPB.lemma16Horizon
            n
            psi
            (theorem1Kappa psi) := by
      unfold
        PPL.Convergence.ReachCPB.lemma16Horizon
      omega

    have hH :
        0 <
          theorem1Horizon
            n psi := by
      unfold theorem1Horizon
      omega

    have hH1 :
        1 <=
          theorem1Horizon
            n psi := by
      omega

    have hcTinyH :
        cTiny <=
          cTiny *
            theorem1Horizon
              n psi := by
      have hmul :=
        Nat.mul_le_mul_left
          cTiny
          hH1
      simpa using hmul

    have hcoef :
        2 * B <=
          cTiny *
            theorem1Horizon
              n psi := by
      calc
        2 * B <=
            2 * Bmax :=
          Nat.mul_le_mul_left
            2
            hB_le
        _ = cTiny := by
          rfl
        _ <=
            cTiny *
              theorem1Horizon
                n psi :=
          hcTinyH

    exact
      Nat.le_trans
        hraw
        (Nat.mul_le_mul_left
          (n ^ T)
          hcoef)

end PPL.Superseded.LogWindow
end
