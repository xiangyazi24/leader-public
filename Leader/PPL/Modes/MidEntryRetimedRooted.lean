import Leader.PPL.Modes.MidEntryRetimedCurrentMax

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

private def q19727FixedBits {n : Nat}
    (ring : DirectedRing n) (x : Fin n) :
    DetSchedule n -> List Bool
  | [] => []
  | e :: rest =>
      match incidentBit ring x e with
      | none => q19727FixedBits ring x rest
      | some b => b :: q19727FixedBits ring x rest




private def q19727StoppedBitsAux_eq_fixed
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    forall (pre word : DetSchedule n),
      stoppedEncounterBitsAux ring
          (fun _ => x) (fun _ => false) pre word =
        q19727FixedBits ring x word := by
  intro pre word
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          simpa [stoppedEncounterBitsAux,
            q19727FixedBits, hb] using
            ih (pre := pre ++ [e])
      | some b =>
          simp [stoppedEncounterBitsAux,
            q19727FixedBits, hb,
            ih (pre := pre ++ [e])]




private def q19727StoppedBits_eq_fixed
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (word : DetSchedule n) :
    stoppedEncounterBits ring
        (fun _ => x) (fun _ => false) word =
      q19727FixedBits ring x word := by
  unfold stoppedEncounterBits
  exact q19727StoppedBitsAux_eq_fixed
    ring x [] word




private def q19727IncidentLetter_eq_isSome
    {n : Nat} (ring : DirectedRing n)
    (x e : Fin n) :
    incidentLetter ring x e =
      (incidentBit ring x e).isSome := by
  by_cases hH : e = ring.leftNeighbor x
  · simp [incidentLetter, incidentBit,
      twoEdgeLetter, hH]
  · by_cases hT : e = x
    · subst e
      simp [incidentLetter, incidentBit,
        twoEdgeLetter, hH]
    · simp [incidentLetter, incidentBit,
        twoEdgeLetter, hH, hT]




private def q19727FixedBits_length_eq_hitsAux
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) :
    forall (pre word : DetSchedule n),
      (q19727FixedBits ring x word).length =
        predictableHostHitsAux ring
          (fun _ => x) pre word := by
  intro pre word
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          have hil : incidentLetter ring x e = false := by
            rw [q19727IncidentLetter_eq_isSome]
            simp [hb]
          simpa [q19727FixedBits,
            predictableHostHitsAux, hb, hil] using
            ih (pre := pre ++ [e])
      | some b =>
          have hil : incidentLetter ring x e = true := by
            rw [q19727IncidentLetter_eq_isSome]
            simp [hb]
          simp [q19727FixedBits,
            predictableHostHitsAux, hb, hil,
            ih (pre := pre ++ [e]), Nat.add_comm]




private def q19727FixedBits_length_eq_hits
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (word : DetSchedule n) :
    (q19727FixedBits ring x word).length =
      predictableHostHits ring
        (fun _ => x) word := by
  unfold predictableHostHits
  exact q19727FixedBits_length_eq_hitsAux
    ring x [] word




private def q19727FixedBits_append
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (u v : DetSchedule n) :
    q19727FixedBits ring x (u ++ v) =
      q19727FixedBits ring x u ++
        q19727FixedBits ring x v := by
  induction u with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          simp [q19727FixedBits, hb, ih]
      | some b =>
          simp [q19727FixedBits, hb, ih]




private def q19727FixedBits_length_le
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) :
    forall word : DetSchedule n,
      (q19727FixedBits ring x word).length <= word.length := by
  intro word
  induction word with
  | nil =>
      simp [q19727FixedBits]
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          simp [q19727FixedBits, hb]
          omega
      | some b =>
          simp [q19727FixedBits, hb]
          omega




private def q19727LotteryRun_append
    (k : Nat) (s : LotteryState)
    (u v : List Bool) :
    lotteryRun k s (u ++ v) =
      lotteryRun k (lotteryRun k s u) v := by
  induction u generalizing s with
  | nil =>
      rfl
  | cons b rest ih =>
      simp [lotteryRun, ih]




private def q19727LotteryStep_sameHead
    (k : Nat) (s t : LotteryState)
    (hh : s.headRun = t.headRun)
    (hw : s.wins <= t.wins)
    (b : Bool) :
    And
      ((lotteryStep k s b).headRun =
        (lotteryStep k t b).headRun)
      ((lotteryStep k s b).wins <=
        (lotteryStep k t b).wins) := by
  cases b with
  | false =>
      apply And.intro
      · simp [lotteryStep]
      · simpa [lotteryStep] using hw
  | true =>
      by_cases hs : k <= s.headRun + 1
      · have ht : k <= t.headRun + 1 := by
          simpa [hh] using hs
        apply And.intro
        · simp [lotteryStep, hs, ht]
        · simp [lotteryStep, hs, ht]
          omega
      · have ht : ¬ (k <= t.headRun + 1) := by
          intro h
          apply hs
          simpa [hh] using h
        apply And.intro
        · simp [lotteryStep, hs, ht, hh]
        · simpa [lotteryStep, hs, ht] using hw




private def q19727LotteryRun_sameHead
    (k : Nat) (s t : LotteryState)
    (bits : List Bool)
    (hh : s.headRun = t.headRun)
    (hw : s.wins <= t.wins) :
    And
      ((lotteryRun k s bits).headRun =
        (lotteryRun k t bits).headRun)
      ((lotteryRun k s bits).wins <=
        (lotteryRun k t bits).wins) := by
  induction bits generalizing s t with
  | nil =>
      exact And.intro hh hw
  | cons b rest ih =>
      have hs :=
        q19727LotteryStep_sameHead k s t hh hw b
      have ht :=
        ih
          (s := lotteryStep k s b)
          (t := lotteryStep k t b)
          hs.1 hs.2
      simpa [lotteryRun] using ht




private def q19727LotteryStep_budget
    (k : Nat) (s : LotteryState) (b : Bool) :
    k * (lotteryStep k s b).wins +
          (lotteryStep k s b).headRun <=
      k * s.wins + s.headRun + 1 := by
  cases b with
  | false =>
      simp [lotteryStep]
      omega
  | true =>
      by_cases hwin : k <= s.headRun + 1
      · simp [lotteryStep, hwin, Nat.mul_add]
        omega
      · simp [lotteryStep, hwin]
        omega




private def q19727LotteryRun_budget
    (k : Nat) (s : LotteryState)
    (bits : List Bool) :
    k * (lotteryRun k s bits).wins +
          (lotteryRun k s bits).headRun <=
      k * s.wins + s.headRun + bits.length := by
  induction bits generalizing s with
  | nil =>
      simp [lotteryRun]
  | cons b rest ih =>
      have hs := q19727LotteryStep_budget k s b
      have ht := ih (s := lotteryStep k s b)
      simp only [lotteryRun, List.length_cons] at ht ⊢
      omega




private def q19727LotteryOffset_budget
    (k h : Nat) (bits : List Bool) :
    k *
        (lotteryRun k
          (lotteryOffset h) bits).wins <=
      h + bits.length := by
  have hb :=
    q19727LotteryRun_budget
      k (lotteryOffset h) bits
  have hb' :
      k *
          (lotteryRun k
            (lotteryOffset h) bits).wins +
            (lotteryRun k
              (lotteryOffset h) bits).headRun <=
        h + bits.length := by
    simpa [lotteryOffset] using hb
  omega




private def q19727SuffixWins_to_whole
    (k M hStart hSuffix : Nat)
    (preBits suffix : List Bool)
    (hbad :
      M <
        (lotteryRun k
          (lotteryOffset hSuffix) suffix).wins) :
    M <=
      (lotteryRun k
        (lotteryOffset hStart)
        (preBits ++ suffix)).wins := by
  have hoff :=
    lotteryHeadOffset_pointwise
      k hSuffix suffix
  have hupper := hoff.2
  have hfresh :
      M <=
        (lotteryRun k lotteryFresh suffix).wins := by
    omega




  let sp :=
    lotteryRun k
      (lotteryOffset hStart) preBits




  have hfreshOffset :
      (lotteryRun k lotteryFresh suffix).wins <=
        (lotteryRun k
          (lotteryOffset sp.headRun)
          suffix).wins :=
    (lotteryHeadOffset_pointwise
      k sp.headRun suffix).1




  have hstate :
      (lotteryRun k
          (lotteryOffset sp.headRun)
          suffix).wins <=
        (lotteryRun k sp suffix).wins := by
    have hh :
        (lotteryOffset sp.headRun).headRun =
          sp.headRun := by
      simp [lotteryOffset]
    have hw :
        (lotteryOffset sp.headRun).wins <=
          sp.wins := by
      simp [lotteryOffset]
    exact
      (q19727LotteryRun_sameHead
        k (lotteryOffset sp.headRun)
        sp suffix hh hw).2




  calc
    M <=
        (lotteryRun k lotteryFresh suffix).wins :=
      hfresh
    _ <=
        (lotteryRun k
          (lotteryOffset sp.headRun)
          suffix).wins :=
      hfreshOffset
    _ <=
        (lotteryRun k sp suffix).wins :=
      hstate
    _ =
        (lotteryRun k
          (lotteryOffset hStart)
          (preBits ++ suffix)).wins := by
      exact congrArg LotteryState.wins
        (q19727LotteryRun_append
          k (lotteryOffset hStart)
          preBits suffix).symm




private def q19727RunRel
    (hstep : Lemma5iiPostResetClockOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x : Fin n) (base : Nat)
    (s : LotteryState)
    (word : DetSchedule n)
    (hrel :
      PostResetClockLotteryRel
        kappa base (C x) s) :
    PostResetClockLotteryRel kappa base
      (runPPL ring C word x)
      (lotteryRun psi s
        (q19727FixedBits ring x word)) := by
  induction word generalizing C s with
  | nil =>
      simpa [runPPL, runPopulationSchedule,
        q19727FixedBits, lotteryRun] using hrel
  | cons e rest ih =>
      let C' := pplStep ring C e
      let s' :=
        postResetLotteryAdvance
          psi ring x e s
      have hnext :
          PostResetClockLotteryRel
            kappa base (C' x) s' := by
        dsimp [C', s']
        exact
          hstep hn3 hpsi
            ring C x e base s hrel
      have htail :=
        ih (C := C') (s := s') hnext
      cases hb : incidentBit ring x e with
      | none =>
          simpa [runPPL, runPopulationSchedule,
            q19727FixedBits,
            postResetLotteryAdvance,
            lotteryRun, hb, C', s', pplStep] using
            htail
      | some b =>
          simpa [runPPL, runPopulationSchedule,
            q19727FixedBits,
            postResetLotteryAdvance,
            lotteryRun, hb, C', s', pplStep] using
            htail




private def q19727FoldlAnd_gen :
    forall (xs : List Bool) (init : Bool),
      xs.foldl (fun a b => a && b) init = true ->
        And
          (init = true)
          (forall b, b ∈ xs -> b = true)
  | [], init, h => by
      refine And.intro (by simpa using h) ?_
      intro b hb
      simp at hb
  | a :: xs, init, h => by
      have htail :=
        q19727FoldlAnd_gen xs (init && a) h
      have hhead :
          And (init = true) (a = true) := by
        simpa using htail.1
      refine And.intro hhead.1 ?_
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb]
        exact hhead.2
      · exact htail.2 b hb




private def q19727AllAgentsTrueAt
    {n : Nat} (p : Fin n -> Bool)
    (h : allAgentsB p = true)
    (i : Fin n) :
    p i = true := by
  unfold allAgentsB at h
  have hall :=
    (q19727FoldlAnd_gen
      (List.ofFn p) true h).2
  apply hall (p i)
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩




private def q19727FoldlAndFalse_existsFalse
    (xs : List Bool)
    (h :
      xs.foldl (fun a b => a && b) true = false) :
    exists b, And (b ∈ xs) (b = false) := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | false =>
          exact
            ⟨false,
              And.intro (by simp) rfl⟩
      | true =>
          have ht :
              xs.foldl
                  (fun u v => u && v)
                  true = false := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hb⟩ := ih ht
          exact
            ⟨b,
              And.intro
                (by simp [hb.1])
                hb.2⟩




private def q19727AllAgentsFalseExists
    {n : Nat} (p : Fin n -> Bool)
    (h : allAgentsB p = false) :
    exists i : Fin n, p i = false := by
  unfold allAgentsB at h
  obtain ⟨b, hb⟩ :=
    q19727FoldlAndFalse_existsFalse
      (List.ofFn p) h
  have hm := hb.1
  rw [List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact ⟨i, hi.trans hb.2⟩




private def q19727FinalLocalBad
    {n psi kappa : Nat}
    (E : Config n psi kappa)
    (hleader : leaderPresent E = true)
    (hmid : midPhysicalB E = false) :
    exists x : Fin n,
      Or
        (kappa / 2 < (E x).clock.val)
        ((E x).mode = true) := by
  have hall :
      allAgentsB
        (fun i =>
          decide ((E i).clock.val <= kappa / 2) &&
            decide ((E i).mode = false)) = false := by
    unfold midPhysicalB at hmid
    rw [hleader] at hmid
    simpa using hmid
  obtain ⟨x, hx⟩ :=
    q19727AllAgentsFalseExists _ hall
  by_cases hc :
      (E x).clock.val <= kappa / 2
  · have hdc :
        decide
          ((E x).clock.val <= kappa / 2) = true :=
      decide_eq_true hc
    rw [hdc, Bool.true_and] at hx
    cases hm : (E x).mode with
    | false =>
        simp [hm] at hx
    | true =>
        exact ⟨x, Or.inr hm⟩
  · exact ⟨x, Or.inl (by omega)⟩




private def q19727Run_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    runPPL ring C (u ++ v) =
      runPPL ring (runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        runPPL, runPopulationSchedule]
      exact ih (C := pplStep ring C e)




private def q19727Run_reachable
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    PopulationProtocol.Reachable
      (PPL.protocol psi kappa) ring C
      (runPPL ring C word) := by
  induction word generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (PPL.protocol psi kappa) ring C
  | cons e rest ih =>
      have hone :
          PopulationProtocol.OneStep
            (PPL.protocol psi kappa) ring C
            (pplStep ring C e) := by
        exact ⟨e, rfl⟩
      have hfirst :=
        PopulationProtocol.OneStep.to_reachable hone
      have htail :=
        ih (C := pplStep ring C e)
      change
        PopulationProtocol.Reachable
          (PPL.protocol psi kappa) ring C
          (runPPL ring (pplStep ring C e) rest)
      exact
        PopulationProtocol.Reachable.trans
          hfirst htail




private def q19727ReachesFinalFalse
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool) :
    forall (C : Config n psi kappa)
      (word : DetSchedule n),
      reachesAux ring good C word = false ->
        good (runPPL ring C word) = false := by
  intro C word
  induction word generalizing C with
  | nil =>
      intro h
      simpa [reachesAux, runPPL,
        runPopulationSchedule] using h
  | cons e rest ih =>
      intro h
      cases hg : good C with
      | true =>
          simp [reachesAux, hg] at h
      | false =>
          have ht :
              reachesAux ring good
                (pplStep ring C e) rest = false := by
            simpa [reachesAux, hg] using h
          have hi :=
            ih (C := pplStep ring C e) ht
          simpa [runPPL, runPopulationSchedule,
            pplStep] using hi




private def q19727ResetSplit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (x : Fin n) :
    forall (C : Config n psi kappa)
      (word : DetSchedule n),
      clockResetSeenAux ring x C word = true ->
      exists u e v,
        And
          (word = u ++ e :: v)
          (clockResetAt ring
            (runPPL ring C u) x e = true) := by
  intro C word h
  induction word generalizing C with
  | nil =>
      simp [clockResetSeenAux] at h
  | cons a rest ih =>
      cases hr : clockResetAt ring C x a with
      | true =>
          refine ⟨[], a, rest,
            And.intro rfl ?_⟩
          simpa [runPPL,
            runPopulationSchedule] using hr
      | false =>
          have ht :
              clockResetSeenAux ring x
                (pplStep ring C a) rest = true := by
            simpa [clockResetSeenAux, hr] using h
          obtain ⟨u, e, v, hs⟩ :=
            ih (C := pplStep ring C a) ht
          refine ⟨a :: u, e, v,
            And.intro ?_ ?_⟩
          · simpa [hs.1]
          · simpa [runPPL,
              runPopulationSchedule, pplStep] using
              hs.2





/-- Current-rooted version of the latest-reset word extraction. -/
theorem lemma5iRetimedMidCurrentMaxWordProjection_proved :
    Lemma5iRetimedMidCurrentMaxWordProjection := by
  unfold Lemma5iRetimedMidCurrentMaxWordProjection
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D
  intro hcnz _hclock _hmax
  intro sweep hsweep hbad

  have hsweepLen :=
    allSchedules_schedule_length
      n (lemma5PaperSweepHorizon n)
      sweep hsweep

  change
    (allClockResetsSeenB ring D sweep &&
      !(reachesAux ring midPhysicalB D sweep)) = true at hbad

  have hfirst :=
    Bool.and_eq_true_iff.mp hbad

  have hresets :
      allClockResetsSeenB ring D sweep = true :=
    hfirst.1

  have hnomid :
      reachesAux ring midPhysicalB D sweep = false := by
    have hn := hfirst.2
    cases hm :
        reachesAux ring midPhysicalB D sweep with
    | false =>
        rfl
    | true =>
        simp [hm] at hn

  have hfullNoMid :
      midPhysicalB
        (runPPL ring D sweep) = false :=
    q19727ReachesFinalFalse
      ring midPhysicalB D sweep hnomid

  have hfullLeader :
      leaderPresent
        (runPPL ring D sweep) = true := by
    exact
      hcnz
        (runPPL ring D sweep)
        (q19727Run_reachable ring D sweep)

  let E : Config n psi kappa :=
    runPPL ring D sweep

  have hENoMid :
      midPhysicalB E = false := by
    simpa [E] using hfullNoMid

  have hELeader :
      leaderPresent E = true := by
    simpa [E] using hfullLeader

  obtain ⟨x, hlocal⟩ :=
    q19727FinalLocalBad E hELeader hENoMid

  have hxSeen :
      clockResetSeenAux ring x D sweep = true := by
    unfold allClockResetsSeenB at hresets
    exact
      q19727AllAgentsTrueAt
        (fun y =>
          clockResetSeenAux ring y D sweep)
        hresets x

  obtain ⟨u, e, v, hsplit⟩ :=
    q19727ResetSplit ring x D sweep hxSeen

  have hsched :
      sweep = (u ++ [e]) ++ v := by
    simpa [List.append_assoc] using hsplit.1

  let R : Config n psi kappa :=
    runPPL ring D u
  let R1 : Config n psi kappa :=
    pplStep ring R e

  have hresetR :
      clockResetAt ring R x e = true := by
    simpa [R] using hsplit.2

  have hzeroR1 :
      (R1 x).clock.val = 0 := by
    dsimp [R1]
    exact
      lemma5iMidResetClockZero
        hpsi ring R x e hresetR

  have hseed :
      PostResetClockLotteryRel
        kappa 0 (R1 x)
        (lotteryOffset (R1 x).hits.val) := by
    unfold PostResetClockLotteryRel
    apply And.intro
    · apply Or.inr
      apply And.intro
      · simpa [lotteryOffset] using hzeroR1
      · simp [lotteryOffset]
    · intro hm
      have hc :=
        lemma5iMidResetModeCapStep_proved
          hpsi ring R x e hresetR
      simpa [R1] using
        hc (by simpa [R1] using hm)

  have hu :
      runPPL ring D (u ++ [e]) = R1 := by
    calc
      runPPL ring D (u ++ [e]) =
          runPPL ring
            (runPPL ring D u) [e] :=
        q19727Run_append ring D u [e]
      _ = R1 := by
        first
          | rfl
          | simp [runPPL,
              runPopulationSchedule,
              pplStep, R, R1]

  have hErun :
      E = runPPL ring R1 v := by
    calc
      E = runPPL ring D sweep := rfl
      _ =
          runPPL ring D
            ((u ++ [e]) ++ v) := by
        rw [hsched]
      _ =
          runPPL ring
            (runPPL ring D (u ++ [e])) v :=
        q19727Run_append
          ring D (u ++ [e]) v
      _ = runPPL ring R1 v := by
        rw [hu]

  let suffixBits :=
    q19727FixedBits ring x v
  let suffixLottery :=
    lotteryRun psi
      (lotteryOffset (R1 x).hits.val)
      suffixBits

  have hrelV :=
    q19727RunRel
      lemma5iiPostResetClockOneStep_proved
      hn3 hpsi ring R1 x 0
      (lotteryOffset (R1 x).hits.val)
      v hseed

  have hrelE :
      PostResetClockLotteryRel
        kappa 0 (E x) suffixLottery := by
    rw [hErun]
    simpa [suffixBits, suffixLottery] using hrelV

  have hclockLeWins :
      (E x).clock.val <= suffixLottery.wins := by
    rcases hrelE.1 with hlt | heq
    · have hh :
          (E x).clock.val <
            suffixLottery.wins := by
        simpa using hlt
      exact Nat.le_of_lt hh
    · have hh :
          (E x).clock.val =
            suffixLottery.wins := by
        simpa using heq.1
      exact Nat.le_of_eq hh

  have hhalf :
      24 * psi <= kappa / 2 := by
    omega

  have hsuffixWins :
      24 * psi < suffixLottery.wins := by
    rcases hlocal with hclock | hmode
    · omega
    · have hcap :
          (E x).clock.val = kappa :=
        hrelE.2 hmode
      omega

  have hhitsR1 :
      (R1 x).hits.val <= psi := by
    have hi := (R1 x).hits.isLt
    omega

  have hwinInt :
      24 * psi + 1 <= suffixLottery.wins := by
    omega

  have hmul :
      psi * (24 * psi + 1) <=
        psi * suffixLottery.wins :=
    Nat.mul_le_mul_left psi hwinInt

  have hbudget :
      psi * suffixLottery.wins <=
        (R1 x).hits.val + suffixBits.length := by
    dsimp [suffixLottery, suffixBits]
    exact
      q19727LotteryOffset_budget
        psi (R1 x).hits.val
        (q19727FixedBits ring x v)

  have hcombo :
      psi * (24 * psi + 1) <=
        (R1 x).hits.val + suffixBits.length :=
    Nat.le_trans hmul hbudget

  have hexpand :
      psi * (24 * psi + 1) =
        24 * psi * psi + psi := by
    rw [Nat.mul_add]
    simp
    ac_rfl

  rw [hexpand] at hcombo

  have hquad :
      24 * psi * psi <= suffixBits.length := by
    omega

  have hvlen :
      v.length <
        lemma5PaperSweepHorizon n := by
    have hh := hsweepLen
    rw [hsplit.1] at hh
    simp only [List.length_append,
      List.length_cons] at hh
    omega

  have hstrict :
      24 * psi * psi < 6 * n * n := by
    calc
      24 * psi * psi <=
          suffixBits.length :=
        hquad
      _ <= v.length := by
        dsimp [suffixBits]
        exact q19727FixedBits_length_le
          ring x v
      _ <
          lemma5PaperSweepHorizon n :=
        hvlen
      _ = 6 * n * n := by
        rfl

  have hpsiN : psi <= n := by
    by_cases hle : psi <= n
    · exact hle
    · have hnpsi : n < psi := by
        omega
      have hnpos : 0 < n := by
        omega
      have h1 :
          n * n < n * psi :=
        (Nat.mul_lt_mul_left hnpos).2 hnpsi
      have h2 :
          n * psi <= psi * psi :=
        Nat.mul_le_mul_right
          psi (Nat.le_of_lt hnpsi)
      have hsq :
          n * n < psi * psi :=
        Nat.lt_of_lt_of_le h1 h2
      have h6 :
          6 * (n * n) <
            6 * (psi * psi) :=
        (Nat.mul_lt_mul_left
          (by omega : 0 < 6)).2 hsq
      have h624 :
          6 * (psi * psi) <=
            24 * (psi * psi) :=
        Nat.mul_le_mul_right
          (psi * psi) (by omega : 6 <= 24)
      have hopp :
          6 * n * n <
            24 * psi * psi := by
        calc
          6 * n * n =
              6 * (n * n) := by
            ac_rfl
          _ < 6 * (psi * psi) := h6
          _ <= 24 * (psi * psi) := h624
          _ = 24 * psi * psi := by
            ac_rfl
      exact False.elim
        ((Nat.not_lt_of_ge
          (Nat.le_of_lt hopp)) hstrict)

  have hpsi3 : 3 <= psi := by
    by_cases hp : 3 <= psi
    · exact hp
    · have hpsiEq : psi = 2 := by
        omega
      subst psi
      have hn4 : n <= 4 := by
        simpa using hnpow
      have hsq :
          n * n <= 4 * 4 :=
        Nat.mul_le_mul hn4 hn4
      have h96 :
          6 * n * n <= 96 := by
        calc
          6 * n * n =
              6 * (n * n) := by
            ac_rfl
          _ <= 6 * (4 * 4) :=
            Nat.mul_le_mul_left 6 hsq
          _ = 96 := by
            decide
      omega

  let prefixBits :=
    q19727FixedBits ring x (u ++ [e])

  have hbitsSplit :
      q19727FixedBits ring x sweep =
        prefixBits ++ suffixBits := by
    dsimp [prefixBits, suffixBits]
    rw [hsched]
    exact
      q19727FixedBits_append
        ring x (u ++ [e]) v

  have hwhole0 :
      24 * psi <=
        (lotteryRun psi
          (lotteryOffset (D x).hits.val)
          (prefixBits ++ suffixBits)).wins :=
    q19727SuffixWins_to_whole
      psi (24 * psi)
      (D x).hits.val
      (R1 x).hits.val
      prefixBits suffixBits
      hsuffixWins

  have hwholeWins :
      24 * psi <=
        (lotteryRun psi
          (lotteryOffset (D x).hits.val)
          (q19727FixedBits ring x sweep)).wins := by
    rw [hbitsSplit]
    exact hwhole0

  refine
    And.intro hpsi3
      (And.intro hpsiN ?_)

  by_cases henc :
      24 * n <
        predictableHostHits
          ring (fun _ => x) sweep
  · refine ⟨x, ?_⟩
    simp [
      lemma5iMidAgentBadB,
      lemma5iMidEncounterAgentBadB,
      henc]

  · have hhitsSweep :
        predictableHostHits
            ring (fun _ => x) sweep <=
          24 * n := by
      omega

    have hlenL7 :
        (q19727FixedBits ring x sweep).length <=
          lotteryL7Horizon psi 2 := by
      calc
        (q19727FixedBits ring x sweep).length =
            predictableHostHits
              ring (fun _ => x) sweep :=
          q19727FixedBits_length_eq_hits
            ring x sweep
        _ <= 24 * n := hhitsSweep
        _ <= 24 * 2 ^ psi :=
          Nat.mul_le_mul_left 24 hnpow
        _ <=
            (4 * 2 * psi) * 2 ^ psi := by
          apply Nat.mul_le_mul_right
          omega
        _ = lotteryL7Horizon psi 2 := by
          unfold lotteryL7Horizon
          ac_rfl

    have hlot :
        lemma5iMidLotteryAgentBadB
          ring D x sweep = true := by
      unfold lemma5iMidLotteryAgentBadB
      rw [q19727StoppedBits_eq_fixed
        ring x sweep]
      exact decide_eq_true
        (And.intro hlenL7 hwholeWins)

    refine ⟨x, ?_⟩
    simp [lemma5iMidAgentBadB, hlot]

theorem lemma5iRetimedMidCurrentMaxSuffixBound_closed :
    Lemma5iRetimedMidCurrentMaxSuffixBound :=
  lemma5iRetimedMidCurrentMaxSuffixBound_proved
    lemma5iRetimedMidCurrentMaxWordProjection_proved

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iRetimedMidCurrentMaxWordProjection_proved
#print axioms PPL.Modes.Lemma5.lemma5iRetimedMidCurrentMaxSuffixBound_closed

