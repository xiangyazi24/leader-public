import Leader.PPL.Modes.MidEntryTraversalPaperEventsCorrected
import Leader.Wu.Scheduler.OrderedWordScheduler


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/-!
# Lemma 5(i): historical-stop traversal invariant


isolated the non-inductive part of
q19792TraversalPrefixInvariant: its reset-frontier escape used the current
stop bit, which can revive after a leader re-arms signalR.


The corrected invariant below uses the monotone historical latch
stopReached stop pre.  Its reset-frontier monitor is the ordinary greedy
matched-prefix length of the rotated word seqR ring start n.
-/


/--
How many letters of the rotated reset word have been greedily matched so far.


The pending suffix is the public fixed-word matcher state.  Subtracting its
length from n gives a monotone value in [0,n] and stays n after completion.
-/
def q19844TraversalMatchedPrefixLength
    {n : Nat}
    (ring : DirectedRing n)
    (start : Fin n)
    (pre : DetSchedule n) : Nat :=
  n -
    (PPLLOrderedWordScheduler.greedyWordRun
      start
      (PPL.seqR ring start n)
      pre).pending.length


/--
A concrete certificate that the j-th selected rotated edge was consumed at a
genuine Algorithm-4 reset interaction.


The prefix condition says that the earlier j selected letters had already
appeared before this occurrence.
-/
def q19844TraversalResetWitness
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (pre : DetSchedule n)
    (j : Nat) : Prop :=
  ∃ before after : DetSchedule n,
    pre =
        before ++
          (shiftRight ring start j :: after) ∧
      (PPL.seqR ring start j).Sublist before ∧
      clockResetAt
          ring
          (runPPL ring D before)
          (shiftRight ring start j)
          (shiftRight ring start j) =
        true


/--
Historical rotated reset frontier.


Before the first historical stop, every greedily matched selected letter has a
real reset witness.  Once all n selected letters have been matched this
frontier also records the exact allClockResetsSeenB consequence used by the
sweep consumer.  If historical stop has already occurred, the frontier is
permanently discharged.
-/
def q19844TraversalResetFrontier
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (pre : DetSchedule n) : Prop :=
  let stop := q19765TraversalStopB ring D
  let hist := stopReached stop pre
  let r :=
    q19844TraversalMatchedPrefixLength
      ring start pre
  r ≤ n ∧
    (hist = true ∨
      ((∀ j : Nat,
          j < r →
            q19844TraversalResetWitness
              ring D start pre j) ∧
        (r = n →
          allClockResetsSeenB
              ring D pre =
            true)))


/--
Corrected traversal invariant.


The four clauses are exactly the historical-stop repair from the audit:


1. before historical stop, the live current maximum is positive;
2. the historical rotated reset frontier;
3. before historical stop, lottery wins plus live max TTL cover kappa;
4. after historical stop, the frozen stopped stream alone already has at
   least kappa wins.
-/
def q19844TraversalHistInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (h : Nat)
    (pre : DetSchedule n) : Prop :=
  let host := q19765TraversalHost ring D
  let stop := q19765TraversalStopB ring D
  let Cpre := runPPL ring D pre
  let x := host pre
  let bits :=
    stoppedEncounterBits ring host stop pre
  let hist := stopReached stop pre
  let W :=
    lotteryRun psi
      (lotteryOffset h) bits
  (hist = false →
      0 < (Cpre x).signalR.val) ∧
    q19844TraversalResetFrontier
      ring D start pre ∧
    (hist = false →
      kappa ≤ W.wins +
        (Cpre x).signalR.val) ∧
    (hist = true →
      kappa ≤ W.wins)


/--
The exact remaining one-letter physical obligation.


Its binders agree with Lemma5iRetimedTraversalABCOneStepInvariant; only the
invariant being preserved has been replaced by the historical-stop version.
No proof of this Prop is supplied in this round.
-/
def Lemma5iRetimedTraversalHistOneStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    maxResetSignalB D = true →
    let start := q19765MaxSignalSite ring D
    let h := (D start).hits.val
    ∀ (pre : DetSchedule n) (e : Fin n),
      q19844TraversalHistInvariant
          ring D start h pre →
        q19844TraversalHistInvariant
          ring D start h (pre ++ [e])


/-! ## Greedy-frontier bookkeeping used by the consumer -/


private theorem q19844TraversalMatchedPrefixLength_nil
    {n : Nat}
    (ring : DirectedRing n)
    (start : Fin n) :
    q19844TraversalMatchedPrefixLength
        ring start [] =
      0 := by
  simp [
    q19844TraversalMatchedPrefixLength,
    PPLLOrderedWordScheduler.greedyWordRun,
    PPLLOrderedWordScheduler.greedyWordRunFrom,
    PPL.seqR
  ]


private theorem
    q19844TraversalMatchedPrefixLength_eq_n_of_sublist
    {n : Nat}
    (ring : DirectedRing n)
    (start : Fin n)
    (pre : DetSchedule n)
    (hsub :
      (PPL.seqR ring start n).Sublist pre) :
    q19844TraversalMatchedPrefixLength
        ring start pre =
      n := by
  have hdone :
      (PPLLOrderedWordScheduler.greedyWordRun
        start
        (PPL.seqR ring start n)
        pre).pending = [] :=
    (PPLLOrderedWordScheduler.greedyWordRun_done_iff_sublist
      start
      (PPL.seqR ring start n)
      pre).2 hsub
  unfold q19844TraversalMatchedPrefixLength
  rw [hdone]
  simp


private theorem q19844TraversalResetFrontier_complete
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (pre : DetSchedule n)
    (hfront :
      q19844TraversalResetFrontier
        ring D start pre)
    (hsub :
      (PPL.seqR ring start n).Sublist pre) :
    allClockResetsSeenB ring D pre = true ∨
      stopReached
          (q19765TraversalStopB ring D)
          pre =
        true := by
  have hr :
      q19844TraversalMatchedPrefixLength
          ring start pre =
        n :=
    q19844TraversalMatchedPrefixLength_eq_n_of_sublist
      ring start pre hsub
  unfold q19844TraversalResetFrontier at hfront
  dsimp only at hfront
  rcases hfront.2 with hhist | hlive
  · exact Or.inr hhist
  · exact Or.inl (hlive.2 hr)


/-! ## Empty prefix -/


private theorem q19844TraversalHistInvariant_nil
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    q19844TraversalHistInvariant
      ring D
      (q19765MaxSignalSite ring D)
      (D
        (q19765MaxSignalSite ring D)).hits.val
      [] := by
  have hsig :=
    lemma5iRetimedTraversalABC_startSignal_eq_kappa
      ring D hmax
  have hkpos : 0 < kappa := by
    omega
  have hk0 : kappa ≠ 0 := by
    omega
  have hstop0 :
      q19765TraversalStopB ring D [] =
        false := by
    simp [
      q19765TraversalStopB,
      q19765TraversalHost,
      runPPL,
      runPopulationSchedule,
      hsig, hk0
    ]
  have hhist0 :
      stopReached
          (q19765TraversalStopB ring D)
          [] =
        false := by
    simpa [stopReached, stopReachedAux]
      using hstop0
  have hfront :
      q19844TraversalResetFrontier
        ring D
        (q19765MaxSignalSite ring D)
        [] := by
    unfold q19844TraversalResetFrontier
    dsimp only
    rw [
      q19844TraversalMatchedPrefixLength_nil
        ring
        (q19765MaxSignalSite ring D)
    ]
    refine ⟨by omega, Or.inr ?_⟩
    constructor
    · intro j hj
      omega
    · intro hr
      have hf : False := by
        omega
      exact False.elim hf


  unfold q19844TraversalHistInvariant
  dsimp only
  refine ⟨?_, hfront, ?_, ?_⟩
  · intro _hhist
    have hp :
        0 <
          (D
            (q19765MaxSignalSite ring D)).signalR.val := by
      rw [hsig]
      exact hkpos
    simpa [
      q19765TraversalHost,
      runPPL,
      runPopulationSchedule
    ] using hp
  · intro _hhist
    have hp :
        kappa ≤ 0 + kappa := by
      omega
    simpa [
      q19765TraversalHost,
      runPPL,
      runPopulationSchedule,
      stoppedEncounterBits,
      stoppedEncounterBitsAux,
      lotteryRun,
      lotteryOffset,
      hsig
    ] using hp
  · intro hhist
    rw [hhist0] at hhist
    cases hhist


/-! ## Closure from the one-letter Prop -/


private theorem q19844TraversalHistInvariant_append
    (hstep :
      Lemma5iRetimedTraversalHistOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (hmax : maxResetSignalB D = true)
    (pre rest : DetSchedule n)
    (hinv :
      q19844TraversalHistInvariant
        ring D
        (q19765MaxSignalSite ring D)
        (D
          (q19765MaxSignalSite ring D)).hits.val
        pre) :
    q19844TraversalHistInvariant
      ring D
      (q19765MaxSignalSite ring D)
      (D
        (q19765MaxSignalSite ring D)).hits.val
      (pre ++ rest) := by
  induction rest generalizing pre with
  | nil =>
      simpa using hinv
  | cons e tail ih =>
      have hlocal :=
        hstep
          hn3 hpsi hkappa hnpow
          ring D hlineage hmax
      dsimp only at hlocal
      have hnext :
          q19844TraversalHistInvariant
            ring D
            (q19765MaxSignalSite ring D)
            (D
              (q19765MaxSignalSite ring D)).hits.val
            (pre ++ [e]) :=
        hlocal pre e hinv
      have htail :=
        ih (pre := pre ++ [e]) hnext
      simpa [List.append_assoc] using htail


/-! ## Stopped-stream bookkeeping -/


private theorem q19844StoppedBitsAux_length_eq_hits
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (pre word : DetSchedule n) :
    (stoppedEncounterBitsAux
      ring host stop pre word).length =
      stoppedPredictableHostHitsAux
        ring host stop pre word := by
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hs : stop pre with
      | true =>
          simp [
            stoppedEncounterBitsAux,
            stoppedPredictableHostHitsAux,
            hs
          ]
      | false =>
          let x := host pre
          by_cases hH :
              e = ring.leftNeighbor x
          · have hi :
                incidentBit ring x e =
                  some true := by
              unfold incidentBit
              rw [if_pos hH]
            have hil :
                incidentLetter ring x e =
                  true := by
              simp [
                incidentLetter,
                twoEdgeLetter,
                hH
              ]
            simp [
              stoppedEncounterBitsAux,
              stoppedPredictableHostHitsAux,
              hs, x, hi, hil,
              ih (pre := pre ++ [e])
            ]
            <;> omega
          · by_cases hT : e = x
            · have hi :
                  incidentBit ring x e =
                    some false := by
                unfold incidentBit
                rw [if_neg hH, if_pos hT]
              have hil :
                  incidentLetter ring x e =
                    true := by
                simp [
                  incidentLetter,
                  twoEdgeLetter,
                  hT
                ]
              simp [
                stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                hs, x, hi, hil,
                ih (pre := pre ++ [e])
              ]
              <;> omega
            · have hi :
                  incidentBit ring x e =
                    none := by
                simp [incidentBit, hH, hT]
              have hil :
                  incidentLetter ring x e =
                    false := by
                simp [
                  incidentLetter,
                  twoEdgeLetter,
                  hH, hT
                ]
              simp [
                stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                hs, x, hi, hil,
                ih (pre := pre ++ [e])
              ]


private theorem q19844StoppedBits_length_eq_hits
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (word : DetSchedule n) :
    (stoppedEncounterBits
      ring host stop word).length =
      stoppedPredictableHostHits
        ring host stop word := by
  exact
    q19844StoppedBitsAux_length_eq_hits
      ring host stop [] word


private theorem q19844EncounterEnvelope_le_l7_5
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi) :
    24 * n ≤ lotteryL7Horizon psi 5 := by
  have hcoef :
      24 ≤ 4 * 5 * psi := by
    omega
  calc
    24 * n ≤
        24 * 2 ^ psi :=
      Nat.mul_le_mul_left 24 hnpow
    _ ≤
        (4 * 5 * psi) * 2 ^ psi :=
      Nat.mul_le_mul_right
        (2 ^ psi) hcoef
    _ = lotteryL7Horizon psi 5 := by
      rfl


/-! ## Corrected consumer -/


/--
The corrected ABC sweep residual follows from the historical one-letter
invariant.


The stop branch differs from the old consumer in one essential place:
clause 4 gives kappa ≤ wins directly.  No claim that the current max TTL is
still zero is made after historical stop.
-/
theorem
    lemma5iRetimedTraversalABCSweepResidualCorrected_of_histOneStep
    (hstep :
      Lemma5iRetimedTraversalHistOneStep) :
    Lemma5iRetimedTraversalABCSweepResidualCorrected := by
  unfold
    Lemma5iRetimedTraversalABCSweepResidualCorrected
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage hmax


  let start :=
    q19765MaxSignalSite ring D
  let host :=
    q19765TraversalHost ring D
  let stop :=
    q19765TraversalStopB ring D
  let h :=
    (D start).hits.val


  change
    (D start).signalR.val = kappa ∧
      h ≤ psi ∧
      ∀ sweep : DetSchedule n,
        sweep ∈
            allSchedules n
              (lemma5PaperSweepHorizon n) →
        !allClockResetsSeenB ring D sweep =
            true →
        ((q19765RotatedMiss
              ring start sweep ||
            q19765EncounterBad
              ring host stop sweep) ||
          q19765TTLBad
            psi h ring host stop sweep) =
          true


  have hsig :
      (D start).signalR.val = kappa := by
    simpa [start] using
      lemma5iRetimedTraversalABC_startSignal_eq_kappa
        ring D hmax


  have hh :
      h ≤ psi := by
    simpa [h, start] using
      lemma5iRetimedTraversalABC_initialHits_le_psi
        ring D


  refine ⟨hsig, hh, ?_⟩
  intro sweep _hsweep hbad


  have hbase :
      q19844TraversalHistInvariant
        ring D start h [] := by
    simpa [start, h] using
      q19844TraversalHistInvariant_nil
        hn3 hpsi hkappa ring D hmax


  have hinv0 :=
    q19844TraversalHistInvariant_append
      hstep
      hn3 hpsi hkappa hnpow
      ring D hlineage hmax
      [] sweep hbase


  have hinv :
      q19844TraversalHistInvariant
        ring D start h sweep := by
    simpa using hinv0


  cases hA :
      q19765RotatedMiss
        ring start sweep with
  | true =>
      simp [hA]
  | false =>
      have hsub :
          (PPL.seqR ring start n).Sublist
            sweep := by
        by_cases hs :
            (PPL.seqR ring start n).Sublist
              sweep
        · exact hs
        · have hAt :
              q19765RotatedMiss
                  ring start sweep =
                true := by
            unfold q19765RotatedMiss
            simp [hs]
          rw [hAt] at hA
          contradiction


      have hfront :
          q19844TraversalResetFrontier
            ring D start sweep :=
        hinv.2.1


      have hdone :=
        q19844TraversalResetFrontier_complete
          ring D start sweep hfront hsub


      rcases hdone with hall | hhist
      · have hf : False := by
          have hb := hbad
          simp [hall] at hb
        exact False.elim hf


      · cases hB :
          q19765EncounterBad
            ring host stop sweep with
        | true =>
            simp [hA, hB]
        | false =>
            have hnotB :
                ¬
                  24 * n <
                    stoppedPredictableHostHits
                      ring host stop sweep := by
              apply of_decide_eq_false
              simpa [q19765EncounterBad]
                using hB


            have hhits :
                stoppedPredictableHostHits
                    ring host stop sweep ≤
                  24 * n := by
              omega


            let bits :=
              stoppedEncounterBits
                ring host stop sweep


            have hbitsEq :
                bits.length =
                  stoppedPredictableHostHits
                    ring host stop sweep := by
              dsimp [bits]
              exact
                q19844StoppedBits_length_eq_hits
                  ring host stop sweep


            have hbits24 :
                bits.length ≤ 24 * n := by
              rw [hbitsEq]
              exact hhits


            have hpad :
                24 * n ≤
                  lotteryL7Horizon psi 5 :=
              q19844EncounterEnvelope_le_l7_5
                hpsi hnpow


            have hlen :
                bits.length ≤
                  lotteryL7Horizon psi 5 :=
              Nat.le_trans hbits24 hpad


            have hcert0 :=
              hinv.2.2.2 hhist


            have hcert :
                kappa ≤
                  (lotteryRun psi
                    (lotteryOffset h) bits).wins := by
              simpa [
                q19844TraversalHistInvariant,
                host, stop, bits
              ] using hcert0


            have hwin :
                lotteryTarget psi 6 ≤
                  (lotteryRun psi
                    (lotteryOffset h) bits).wins := by
              unfold lotteryTarget
              omega


            have hC :
                q19765TTLBad
                    psi h ring host stop sweep =
                  true := by
              unfold q19765TTLBad
              dsimp only
              simp only [decide_eq_true_eq]
              exact ⟨hlen, hwin⟩


            simp [hA, hB, hC]


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABCSweepResidualCorrected_of_histOneStep
