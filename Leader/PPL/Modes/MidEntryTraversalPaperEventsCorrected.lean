import Leader.PPL.Modes.MidEntryTraversalPaperEvents


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/-! -------------------------------------------------------------------------
    Part 1.  The two initial conjuncts
------------------------------------------------------------------------- -/


private def q19792MaxStep
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (best i : Fin n) : Fin n :=
  if (C best).signalR.val < (C i).signalR.val then i else best


private theorem q19792MaxStep_ge_left
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (best i : Fin n) :
    (C best).signalR.val ≤
      (C (q19792MaxStep C best i)).signalR.val := by
  unfold q19792MaxStep
  by_cases hlt :
      (C best).signalR.val < (C i).signalR.val
  · rw [if_pos hlt]
    exact Nat.le_of_lt hlt
  · rw [if_neg hlt]
    exact Nat.le_refl _


private theorem q19792MaxStep_ge_right
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (best i : Fin n) :
    (C i).signalR.val ≤
      (C (q19792MaxStep C best i)).signalR.val := by
  unfold q19792MaxStep
  by_cases hlt :
      (C best).signalR.val < (C i).signalR.val
  · rw [if_pos hlt]
    exact Nat.le_refl _
  · rw [if_neg hlt]
    omega


private theorem q19792FoldMax_ge_seed
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    ∀ (xs : List (Fin n)) (seed : Fin n),
      (C seed).signalR.val ≤
        (C (xs.foldl
          (q19792MaxStep C) seed)).signalR.val := by
  intro xs
  induction xs with
  | nil =>
      intro seed
      exact Nat.le_refl _
  | cons a rest ih =>
      intro seed
      simp only [List.foldl_cons]
      exact
        Nat.le_trans
          (q19792MaxStep_ge_left C seed a)
          (ih (q19792MaxStep C seed a))


private theorem q19792FoldMax_ge_mem
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    ∀ (xs : List (Fin n)) (seed i : Fin n),
      i ∈ xs →
      (C i).signalR.val ≤
        (C (xs.foldl
          (q19792MaxStep C) seed)).signalR.val := by
  intro xs
  induction xs with
  | nil =>
      intro seed i hi
      simp at hi
  | cons a rest ih =>
      intro seed i hi
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hia | hir
      · subst i
        exact
          Nat.le_trans
            (q19792MaxStep_ge_right C seed a)
            (q19792FoldMax_ge_seed
              C rest (q19792MaxStep C seed a))
      · exact
          ih (q19792MaxStep C seed a) i hir


private theorem q19792True_mem_foldl_or
    (xs : List Bool)
    (h :
      xs.foldl (fun acc b => acc || b) false = true) :
    true ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons b rest ih =>
      cases b with
      | false =>
          have ht :
              rest.foldl
                  (fun acc b => acc || b) false =
                true := by
            simpa only
              [List.foldl_cons, Bool.false_or]
              using h
          exact
            List.mem_cons.mpr
              (Or.inr (ih ht))
      | true =>
          exact
            List.mem_cons.mpr
              (Or.inl rfl)


private theorem q19792MaxReset_exists
    {n psi kappa : Nat}
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    ∃ i : Fin n,
      (D i).signalR.val = kappa := by
  unfold maxResetSignalB at hmax
  have hm :
      true ∈
        List.ofFn
          (fun i : Fin n =>
            decide ((D i).signalR.val = kappa)) :=
    q19792True_mem_foldl_or
      (List.ofFn
        (fun i : Fin n =>
          decide ((D i).signalR.val = kappa)))
      hmax
  rw [List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact
    ⟨i, of_decide_eq_true hi⟩


/--
The site chosen by `q19765MaxSignalSite` really is a max-TTL holder when
`maxResetSignalB D` is true.
-/
theorem lemma5iRetimedTraversalABC_startSignal_eq_kappa
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    (D (q19765MaxSignalSite ring D)).signalR.val =
      kappa := by
  obtain ⟨i, hi⟩ :=
    q19792MaxReset_exists D hmax
  have himem :
      i ∈ List.ofFn (fun j : Fin n => j) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  have hle0 :=
    q19792FoldMax_ge_mem
      D
      (List.ofFn (fun j : Fin n => j))
      ⟨0, ring.hn⟩ i himem
  have hle :
      (D i).signalR.val ≤
        (D (q19765MaxSignalSite ring D)).signalR.val := by
    unfold q19765MaxSignalSite
    exact hle0
  have hlo :
      kappa ≤
        (D (q19765MaxSignalSite ring D)).signalR.val := by
    simpa [hi] using hle
  have hup :=
    (D (q19765MaxSignalSite ring D)).signalR.isLt
  omega


/--
The initial head offset is automatically in `[0, psi]`, because `hits`
has type `Fin (psi + 1)`.
-/
theorem lemma5iRetimedTraversalABC_initialHits_le_psi
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa) :
    (D (q19765MaxSignalSite ring D)).hits.val ≤
      psi := by
  have hlt :=
    (D (q19765MaxSignalSite ring D)).hits.isLt
  omega


/-! -------------------------------------------------------------------------
    Part 2.  Small-instance audit of the old witness
------------------------------------------------------------------------- -/


private def q19792Ring : DirectedRing 3 :=
  ⟨by omega⟩


private def q19792State
    (i : Fin 3) : PPL.State 2 96 :=
  { leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := true
    tokenB := none
    tokenW := none
    mode := false
    clock := 0
    signalR :=
      if i = (2 : Fin 3) then
        ⟨96, by omega⟩
      else
        0
    hits := 0
    bullet := 0
    shield := false
    signalB := false }


private def q19792D : Config 3 2 96 :=
  q19792State


private def q19792OldSweep : DetSchedule 3 :=
  List.replicate 50 (0 : Fin 3) ++
    [(0 : Fin 3), (2 : Fin 3),
      (1 : Fin 3), (2 : Fin 3)]


theorem q19792_oldWitness_start_is_two :
    q19765MaxSignalSite q19792Ring q19792D =
      (2 : Fin 3) := by
  decide


/--
The old counterexample is not a counterexample to the corrected
residual: corrected A fires, because the required rotated word is [2,0,1].
-/
theorem q19792_oldWitness_caught_by_rotated_A :
    q19765RotatedMiss
        q19792Ring
        (q19765MaxSignalSite q19792Ring q19792D)
        q19792OldSweep =
      true := by
  decide


theorem q19792_oldWitness_still_misses_a_reset :
    !allClockResetsSeenB
        q19792Ring q19792D q19792OldSweep =
      true := by
  decide


theorem q19792_rotated_word_itself_resets_all :
    allClockResetsSeenB
        q19792Ring q19792D
        [(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)] =
      true := by
  decide


/-! -------------------------------------------------------------------------
    Part 3.  Exact remaining one-step invariant
------------------------------------------------------------------------- -/


/-
Pure stopped-stream bookkeeping.  This does not use a physical/headRun
synchronization and remains valid when the predictable host changes.
-/
private theorem q19792StoppedBitsAux_length_eq_hits
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


private theorem q19792StoppedBits_length_eq_hits
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
    q19792StoppedBitsAux_length_eq_hits
      ring host stop [] word


private theorem q19792EncounterEnvelope_le_l7_5
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


/--
Prefix invariant used by the reduction.


* `Cpre` and `x` are definitionally the requested
  `runPPL ring D pre` and predictable current-max host.
* Before stop, the current host still carries positive signal.
* The second conjunct is the proposition-level form of the monotone rotated
  reset frontier: once the whole rotated sweep has been matched, either every
  clock has reset or the tracked signal process has stopped.
* The last conjunct is the TTL potential.  It deliberately does not identify
  the parser headRun with physical hits after a max-holder switch.
-/
def q19792TraversalPrefixInvariant
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
  (stop pre = false →
      0 < (Cpre x).signalR.val) ∧
    ((PPL.seqR ring start n).Sublist pre →
      allClockResetsSeenB ring D pre = true ∨
        stop pre = true) ∧
    kappa ≤
      (lotteryRun psi
        (lotteryOffset h) bits).wins +
        (Cpre x).signalR.val


private theorem q19792TraversalPrefixInvariant_nil
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    q19792TraversalPrefixInvariant
      ring D
      (q19765MaxSignalSite ring D)
      (D (q19765MaxSignalSite ring D)).hits.val
      [] := by
  have hsig :=
    lemma5iRetimedTraversalABC_startSignal_eq_kappa
      ring D hmax
  have hkpos : 0 < kappa := by
    omega
  unfold q19792TraversalPrefixInvariant
  dsimp only
  constructor
  · intro _hstop
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
  · constructor
    · intro hsub
      have hlen := hsub.length_le
      have hnle : n ≤ 0 := by
        simpa [PPL.seqR] using hlen
      have hf : False := by
        omega
      exact False.elim hf
    · have hp : kappa ≤ 0 + kappa := by
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


/--
This is the exact remaining one-letter physical obligation.


Its proof is the cold/H/T split advertised in
`Lemma5iRetimedTraversalABC.lean`: use
`determineModeSignalProjection`,
`postDetermineModeSignalStable`, and
`step_signal_projection_of_stable postDetermineModeSignalStable` to show
that one scheduler letter preserves the live-current-max fact, advances the
rotated reset frontier, and preserves the TTL potential.  No equality between
parser `headRun` and physical `hits` is assumed across a holder switch.
-/
def Lemma5iRetimedTraversalABCOneStepInvariant : Prop :=
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
      q19792TraversalPrefixInvariant
          ring D start h pre →
        q19792TraversalPrefixInvariant
          ring D start h (pre ++ [e])


private theorem q19792TraversalPrefixInvariant_append
    (hstep :
      Lemma5iRetimedTraversalABCOneStepInvariant)
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
      q19792TraversalPrefixInvariant
        ring D
        (q19765MaxSignalSite ring D)
        (D (q19765MaxSignalSite ring D)).hits.val
        pre) :
    q19792TraversalPrefixInvariant
      ring D
      (q19765MaxSignalSite ring D)
      (D (q19765MaxSignalSite ring D)).hits.val
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
          q19792TraversalPrefixInvariant
            ring D
            (q19765MaxSignalSite ring D)
            (D
              (q19765MaxSignalSite ring D)).hits.val
            (pre ++ [e]) :=
        hlocal pre e hinv
      have htail :=
        ih (pre := pre ++ [e]) hnext
      simpa [List.append_assoc] using htail


/--
Full corrected ABC residual from the single one-letter invariant obligation.
-/
theorem
    lemma5iRetimedTraversalABCSweepResidualCorrected_of_oneStepInvariant
    (hstep :
      Lemma5iRetimedTraversalABCOneStepInvariant) :
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
      q19792TraversalPrefixInvariant
        ring D start h [] := by
    simpa [start, h] using
      q19792TraversalPrefixInvariant_nil
        hn3 hpsi hkappa ring D hmax


  have hinv0 :=
    q19792TraversalPrefixInvariant_append
      hstep
      hn3 hpsi hkappa hnpow
      ring D hlineage hmax
      [] sweep hbase


  have hinv :
      q19792TraversalPrefixInvariant
        ring D start h sweep := by
    simpa using hinv0


  cases hA :
      q19765RotatedMiss
        ring start sweep with
  | true =>
      simp [hA]
  | false =>
      have hsub :
          (PPL.seqR ring start n).Sublist sweep := by
        by_cases hs :
            (PPL.seqR ring start n).Sublist sweep
        · exact hs
        · have hAt :
              q19765RotatedMiss
                  ring start sweep =
                true := by
            unfold q19765RotatedMiss
            simp [hs]
          rw [hAt] at hA
          contradiction


      have hfront :=
        hinv.2.1 hsub
      rcases hfront with hall | hstop
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
                q19792StoppedBits_length_eq_hits
                  ring host stop sweep


            have hbits24 :
                bits.length ≤ 24 * n := by
              rw [hbitsEq]
              exact hhits


            have hpad :
                24 * n ≤
                  lotteryL7Horizon psi 5 :=
              q19792EncounterEnvelope_le_l7_5
                hpsi hnpow


            have hlen :
                bits.length ≤
                  lotteryL7Horizon psi 5 :=
              Nat.le_trans hbits24 hpad


            have hz :
                (runPPL ring D sweep
                  (host sweep)).signalR.val = 0 := by
              apply of_decide_eq_true
              simpa [
                stop,
                q19765TraversalStopB
              ] using hstop


            have hpot0 := hinv.2.2
            have hpot :
                kappa ≤
                  (lotteryRun psi
                    (lotteryOffset h) bits).wins +
                    (runPPL ring D sweep
                      (host sweep)).signalR.val := by
              simpa [
                q19792TraversalPrefixInvariant,
                host, stop, bits
              ] using hpot0


            rw [hz, Nat.add_zero] at hpot


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


#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABC_startSignal_eq_kappa
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABC_initialHits_le_psi
#print axioms PPL.Modes.Lemma5.q19792_oldWitness_caught_by_rotated_A
#print axioms PPL.Modes.Lemma5.q19792_rotated_word_itself_resets_all
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABCSweepResidualCorrected_of_oneStepInvariant
