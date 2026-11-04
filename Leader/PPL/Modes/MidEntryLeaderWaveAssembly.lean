import Leader.PPL.Modes.MidEntryLeaderWaveRows

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-! Initial max-wave facts
------------------------------------------------------------------------- -/

private def q20107MaxStep
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (best i : Fin n) : Fin n :=
  if (C best).signalR.val < (C i).signalR.val then
    i
  else
    best

private theorem q20107MaxStep_ge_left
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (best i : Fin n) :
    (C best).signalR.val ≤
      (C (q20107MaxStep C best i)).signalR.val := by
  unfold q20107MaxStep
  by_cases hlt :
      (C best).signalR.val < (C i).signalR.val
  · rw [if_pos hlt]
    exact Nat.le_of_lt hlt
  · rw [if_neg hlt]
    exact Nat.le_refl _

private theorem q20107MaxStep_ge_right
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (best i : Fin n) :
    (C i).signalR.val ≤
      (C (q20107MaxStep C best i)).signalR.val := by
  unfold q20107MaxStep
  by_cases hlt :
      (C best).signalR.val < (C i).signalR.val
  · rw [if_pos hlt]
    exact Nat.le_refl _
  · rw [if_neg hlt]
    omega

private theorem q20107FoldMax_ge_seed
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    ∀ (xs : List (Fin n)) (seed : Fin n),
      (C seed).signalR.val ≤
        (C (xs.foldl
          (q20107MaxStep C) seed)).signalR.val := by
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
          (q20107MaxStep_ge_left C seed a)
          (ih (q20107MaxStep C seed a))

private theorem q20107FoldMax_ge_mem
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    ∀ (xs : List (Fin n)) (seed i : Fin n),
      i ∈ xs →
      (C i).signalR.val ≤
        (C (xs.foldl
          (q20107MaxStep C) seed)).signalR.val := by
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
            (q20107MaxStep_ge_right C seed a)
            (q20107FoldMax_ge_seed
              C rest (q20107MaxStep C seed a))
      · exact
          ih (q20107MaxStep C seed a) i hir

private theorem q20107True_mem_foldl_or
    (xs : List Bool)
    (h :
      xs.foldl
          (fun acc b => acc || b) false =
        true) :
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

private theorem q20107MaxReset_exists
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
    q20107True_mem_foldl_or
      (List.ofFn
        (fun i : Fin n =>
          decide ((D i).signalR.val = kappa)))
      hmax
  rw [List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact
    ⟨i, of_decide_eq_true hi⟩

private theorem q20107LeaderWaveStartSignal_eq_kappa
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    (D (lemma5iLeaderWaveStart ring D)).signalR.val =
      kappa := by
  obtain ⟨i, hi⟩ :=
    q20107MaxReset_exists D hmax
  have himem :
      i ∈ List.ofFn (fun j : Fin n => j) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  have hle0 :=
    q20107FoldMax_ge_mem
      D
      (List.ofFn (fun j : Fin n => j))
      ⟨0, ring.hn⟩ i himem
  have hle :
      (D i).signalR.val ≤
        (D
          (lemma5iLeaderWaveStart
            ring D)).signalR.val := by
    unfold lemma5iLeaderWaveStart
    exact hle0
  have hlo :
      kappa ≤
        (D
          (lemma5iLeaderWaveStart
            ring D)).signalR.val := by
    simpa [hi] using hle
  have hup :=
    (D
      (lemma5iLeaderWaveStart
        ring D)).signalR.isLt
  omega

private theorem q20107LeaderWaveInitialHits_le_psi
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa) :
    (D
      (lemma5iLeaderWaveStart
        ring D)).hits.val ≤
      psi := by
  have hlt :=
    (D
      (lemma5iLeaderWaveStart
        ring D)).hits.isLt
  omega

/-! -------------------------------------------------------------------------
    Pure rotated-word and historical bookkeeping
------------------------------------------------------------------------- -/

private theorem q20107ShiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]

private theorem q20107SeqR_succ
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat) :
    PPL.seqR ring root (j + 1) =
      PPL.seqR ring root j ++
        [PPL.shiftRight ring root j] := by
  unfold PPL.seqR
  rw [List.ofFn_succ_last]
  rfl

private theorem q20107SeqR_sublist_of_le
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    {a b : Nat}
    (hab : a ≤ b) :
    (PPL.seqR ring root a).Sublist
      (PPL.seqR ring root b) := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [
        show a + Nat.succ d = (a + d) + 1 by omega,
        q20107SeqR_succ ring root (a + d)
      ]
      exact
        (ih (Nat.le_add_right a d)).trans
          (List.sublist_append_left _ _)

private theorem q20107ResetFrontier_not_full
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (hfront :
      Lemma5iLeaderWaveResetFrontierAt
        ring D pre) :
    ¬
      (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) n).Sublist
        pre := by
  unfold Lemma5iLeaderWaveResetFrontierAt at hfront
  dsimp only at hfront
  rcases hfront with
    ⟨q, hqn, _hhost, _hsub, hnext, _hwit⟩
  intro hfull
  have hpref :
      (PPL.seqR ring
          (lemma5iLeaderWaveStart ring D)
          (q + 1)).Sublist
        (PPL.seqR ring
          (lemma5iLeaderWaveStart ring D)
          n) :=
    q20107SeqR_sublist_of_le
      ring
      (lemma5iLeaderWaveStart ring D)
      (by omega)
  exact
    hnext
      (hpref.trans hfull)

private theorem q20107StopReachedAux_append_singleton_true
    {n : Nat}
    (stop : List (Fin n) → Bool)
    (base word : DetSchedule n)
    (e : Fin n)
    (h :
      stopReachedAux stop base word = true) :
    stopReachedAux stop base (word ++ [e]) =
      true := by
  induction word generalizing base with
  | nil =>
      have hb :
          stop base = true := by
        simpa [stopReachedAux] using h
      simp [stopReachedAux, hb]
  | cons a rest ih =>
      cases hb : stop base with
      | true =>
          simp [stopReachedAux, hb]
      | false =>
          have htail :
              stopReachedAux stop
                  (base ++ [a]) rest =
                true := by
            simpa [stopReachedAux, hb] using h
          have hnext :=
            ih (base := base ++ [a]) htail
          simpa [stopReachedAux, hb] using hnext

private theorem q20107StopReached_append_singleton_true
    {n : Nat}
    (stop : List (Fin n) → Bool)
    (word : DetSchedule n)
    (e : Fin n)
    (h : stopReached stop word = true) :
    stopReached stop (word ++ [e]) = true := by
  unfold stopReached at h ⊢
  exact
    q20107StopReachedAux_append_singleton_true
      stop [] word e h

private theorem q20107StopReachedAux_of_endpoint_true
    {n : Nat}
    (stop : List (Fin n) → Bool)
    (base word : DetSchedule n)
    (h : stop (base ++ word) = true) :
    stopReachedAux stop base word = true := by
  induction word generalizing base with
  | nil =>
      simpa [stopReachedAux] using h
  | cons a rest ih =>
      cases hb : stop base with
      | true =>
          simp [stopReachedAux, hb]
      | false =>
          have htail :
              stop ((base ++ [a]) ++ rest) =
                true := by
            simpa [List.append_assoc] using h
          have hih :=
            ih (base := base ++ [a]) htail
          simpa [stopReachedAux, hb] using hih

private theorem q20107StopReached_of_endpoint_true
    {n : Nat}
    (stop : List (Fin n) → Bool)
    (word : DetSchedule n)
    (h : stop word = true) :
    stopReached stop word = true := by
  unfold stopReached
  have h0 :
      stop ([] ++ word) = true := by
    simpa using h
  exact
    q20107StopReachedAux_of_endpoint_true
      stop [] word h0

private theorem q20107StoppedBitsAux_append_of_reached
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (base word : DetSchedule n)
    (e : Fin n)
    (hreach :
      stopReachedAux stop base word = true) :
    stoppedEncounterBitsAux
        ring host stop base (word ++ [e]) =
      stoppedEncounterBitsAux
        ring host stop base word := by
  induction word generalizing base with
  | nil =>
      have hb :
          stop base = true := by
        simpa [stopReachedAux] using hreach
      simp [stoppedEncounterBitsAux, hb]
  | cons a rest ih =>
      cases hb : stop base with
      | true =>
          simp [stoppedEncounterBitsAux, hb]
      | false =>
          have htail :
              stopReachedAux stop
                  (base ++ [a]) rest =
                true := by
            simpa [stopReachedAux, hb] using hreach
          have hih :=
            ih (base := base ++ [a]) htail
          cases hbit :
              incidentBit ring (host base) a with
          | none =>
              simpa
                [stoppedEncounterBitsAux, hb, hbit]
                using hih
          | some b =>
              simp
                [stoppedEncounterBitsAux, hb, hbit, hih]

private theorem q20107StoppedBits_append_of_reached
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (word : DetSchedule n)
    (e : Fin n)
    (hreach : stopReached stop word = true) :
    stoppedEncounterBits
        ring host stop (word ++ [e]) =
      stoppedEncounterBits
        ring host stop word := by
  unfold stoppedEncounterBits
  unfold stopReached at hreach
  exact
    q20107StoppedBitsAux_append_of_reached
      ring host stop [] word e hreach

/-! -------------------------------------------------------------------------
    Monotonicity of allClockResetsSeenB
------------------------------------------------------------------------- -/

private theorem q20107ClockResetSeenAux_append_singleton
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (x : Fin n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (e : Fin n)
    (h :
      clockResetSeenAux ring x C word = true) :
    clockResetSeenAux ring x C (word ++ [e]) =
      true := by
  induction word generalizing C with
  | nil =>
      simp [clockResetSeenAux] at h
  | cons a rest ih =>
      cases hr : clockResetAt ring C x a with
      | true =>
          simp [clockResetSeenAux, hr]
      | false =>
          have htail :
              clockResetSeenAux ring x
                  (pplStep ring C a) rest =
                true := by
            simpa [clockResetSeenAux, hr] using h
          have hnext :=
            ih (C := pplStep ring C a) htail
          simpa [clockResetSeenAux, hr] using hnext

private theorem q20107FoldlAnd_gen
    (xs : List Bool)
    (init : Bool)
    (h :
      xs.foldl
          (fun a b => a && b) init =
        true) :
    And
      (init = true)
      (∀ b, b ∈ xs → b = true) := by
  induction xs generalizing init with
  | nil =>
      refine
        And.intro
          (by simpa using h) ?_
      intro b hb
      simp at hb
  | cons a rest ih =>
      have hrest :
          rest.foldl
              (fun u v => u && v)
              (init && a) =
            true := by
        simpa [List.foldl_cons] using h
      have htail :=
        ih (init := init && a) hrest
      have hhead :
          And (init = true) (a = true) := by
        simpa using htail.1
      refine And.intro hhead.1 ?_
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb]
        exact hhead.2
      · exact htail.2 b hb

private theorem q20107AllAgentsTrueAt
    {n : Nat}
    (p : Fin n → Bool)
    (h : allAgentsB p = true)
    (i : Fin n) :
    p i = true := by
  unfold allAgentsB at h
  have hall :=
    (q20107FoldlAnd_gen
      (List.ofFn p) true h).2
  apply hall (p i)
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩

private theorem q20107FoldlAnd_true_of_all_true
    (xs : List Bool)
    (h : ∀ b, b ∈ xs → b = true) :
    xs.foldl
        (fun a b => a && b) true =
      true := by
  induction xs with
  | nil =>
      rfl
  | cons a rest ih =>
      have ha :
          a = true :=
        h a (by simp)
      have hrest :
          ∀ b, b ∈ rest → b = true := by
        intro b hb
        exact h b (by simp [hb])
      simp [List.foldl_cons, ha]
      exact ih hrest

private theorem q20107AllAgentsTrue_of_pointwise
    {n : Nat}
    (p : Fin n → Bool)
    (h : ∀ i, p i = true) :
    allAgentsB p = true := by
  unfold allAgentsB
  apply q20107FoldlAnd_true_of_all_true
  intro b hb
  rw [List.mem_ofFn] at hb
  rcases hb with ⟨i, hi⟩
  rw [← hi]
  exact h i

private theorem q20107AllClockResetsSeen_append_singleton
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (e : Fin n)
    (h :
      allClockResetsSeenB ring C word = true) :
    allClockResetsSeenB ring C (word ++ [e]) =
      true := by
  unfold allClockResetsSeenB at h ⊢
  apply q20107AllAgentsTrue_of_pointwise
  intro i
  have hi :=
    q20107AllAgentsTrueAt
      (fun x =>
        clockResetSeenAux ring x C word)
      h i
  exact
    q20107ClockResetSeenAux_append_singleton
      ring i C word e hi

/-! -------------------------------------------------------------------------
    Encounter-bit length and L7 envelope
------------------------------------------------------------------------- -/

private theorem q20107StoppedBitsAux_length_eq_hits
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
          · by_cases hT :
              e = x
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

private theorem q20107StoppedBits_length_eq_hits
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
    q20107StoppedBitsAux_length_eq_hits
      ring host stop [] word

private theorem q20107EncounterEnvelope_le_l7_5
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

/-! -------------------------------------------------------------------------
    Three-way prefix invariant and induction
------------------------------------------------------------------------- -/

private def q20107WavePrefixInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (h : Nat)
    (pre : DetSchedule n) : Prop :=
  let host :=
    lemma5iLeaderWaveHost ring D
  let stop :=
    lemma5iLeaderWaveStopB ring D
  let bits :=
    stoppedEncounterBits ring host stop pre
  (stopReached stop pre = true ∧
      kappa ≤
        (lotteryRun psi
          (lotteryOffset h) bits).wins) ∨
    ((PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) n).Sublist
          pre ∧
      allClockResetsSeenB ring D pre = true) ∨
    (Lemma5iLeaderWaveActivePrefix ring D pre ∧
      Lemma5iLeaderWaveResetFrontierAt ring D pre ∧
      Lemma5iLeaderWaveTTLPotentialAt
        ring D h pre)

private theorem q20107WavePrefixInvariant_nil
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    q20107WavePrefixInvariant
      ring D
      (D
        (lemma5iLeaderWaveStart
          ring D)).hits.val
      [] := by
  have hsig :=
    q20107LeaderWaveStartSignal_eq_kappa
      ring D hmax
  have hkpos :
      0 < kappa := by
    omega
  unfold q20107WavePrefixInvariant
  dsimp only
  right
  right
  refine ⟨?_, ?_, ?_⟩
  · unfold Lemma5iLeaderWaveActivePrefix
    refine ⟨?_, ?_⟩
    · unfold lemma5iLeaderWaveStopB
      dsimp only
      simp [
        lemma5iLeaderWaveHost,
        runPPL,
        runPopulationSchedule,
        hsig,
        Nat.ne_of_gt hkpos
      ]
    · intro hsub
      have hlen :=
        hsub.length_le
      have hnle :
          n ≤ 0 := by
        simpa [PPL.seqR] using hlen
      omega
  · unfold Lemma5iLeaderWaveResetFrontierAt
    dsimp only
    refine
      ⟨0, by omega, ?_, ?_, ?_, ?_⟩
    · simpa [lemma5iLeaderWaveHost] using
        (q20107ShiftRight_zero
          ring
          (lemma5iLeaderWaveStart
            ring D)).symm
    · simp [PPL.seqR]
    · intro hsub
      have hlen :=
        hsub.length_le
      have hbad :
          1 ≤ 0 := by
        simpa [PPL.seqR] using hlen
      omega
    · intro j hj
      omega
  · unfold Lemma5iLeaderWaveTTLPotentialAt
    dsimp only
    have hp :
        kappa ≤ 0 + kappa := by
      omega
    simpa [
      lemma5iLeaderWaveHost,
      runPPL,
      runPopulationSchedule,
      stoppedEncounterBits,
      stoppedEncounterBitsAux,
      lotteryRun,
      lotteryOffset,
      hsig
    ] using hp

private theorem q20107WavePrefixInvariant_append
    (hReset : Lemma5iLeaderWaveResetFrontierOneStep)
    (hTTL : Lemma5iLeaderWaveTTLPotentialOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (h : Nat)
    (pre rest : DetSchedule n)
    (hinv :
      q20107WavePrefixInvariant
        ring D h pre) :
    q20107WavePrefixInvariant
      ring D h (pre ++ rest) := by
  induction rest generalizing pre with
  | nil =>
      simpa using hinv
  | cons e tail ih =>
      have hnext :
          q20107WavePrefixInvariant
            ring D h (pre ++ [e]) := by
        unfold q20107WavePrefixInvariant at hinv ⊢
        dsimp only at hinv ⊢
        rcases hinv with hstopped | hrest
        · left
          have hreach :=
            q20107StopReached_append_singleton_true
              (lemma5iLeaderWaveStopB ring D)
              pre e hstopped.1
          have hbits :=
            q20107StoppedBits_append_of_reached
              ring
              (lemma5iLeaderWaveHost ring D)
              (lemma5iLeaderWaveStopB ring D)
              pre e hstopped.1
          refine ⟨hreach, ?_⟩
          rw [hbits]
          exact hstopped.2
        · rcases hrest with hdone | hlive
          · right
            left
            refine ⟨?_, ?_⟩
            · exact
                hdone.1.trans
                  (List.sublist_append_left
                    pre [e])
            · exact
                q20107AllClockResetsSeen_append_singleton
                  ring D pre e hdone.2
          · have hactive :=
              hlive.1
            have _hloc :=
              lemma5iLeaderWaveLocationOneStep_proved
                ring D pre e hactive
            have _hmerge :=
              lemma5iLeaderWaveTTLMergeOneStep_proved
                hn3 hpsi ring D pre e hactive
            have hreset :=
              hReset
                hn3 hpsi ring D pre e
                hactive hlive.2.1
            have httl :=
              hTTL
                hn3 hpsi ring D h pre e
                hactive hlive.2.2
            dsimp only at hreset httl
            rcases hreset with hstop | hreset'
            · left
              have hreach :=
                q20107StopReached_of_endpoint_true
                  (lemma5iLeaderWaveStopB ring D)
                  (pre ++ [e]) hstop
              exact
                ⟨hreach, httl.1 hstop⟩
            · rcases hreset' with hcomplete | hfront
              · right
                left
                exact hcomplete
              · cases hs :
                  lemma5iLeaderWaveStopB
                    ring D (pre ++ [e]) with
                | true =>
                    left
                    have hreach :=
                      q20107StopReached_of_endpoint_true
                        (lemma5iLeaderWaveStopB ring D)
                        (pre ++ [e]) hs
                    exact
                      ⟨hreach, httl.1 hs⟩
                | false =>
                    right
                    right
                    refine
                      ⟨?_, hfront, httl.2 hs⟩
                    exact
                      ⟨hs,
                        q20107ResetFrontier_not_full
                          ring D
                          (pre ++ [e])
                          hfront⟩
      have htail :=
        ih (pre := pre ++ [e]) hnext
      simpa [List.append_assoc] using htail

/-! -------------------------------------------------------------------------
    Requested residual assembly and budget composition
------------------------------------------------------------------------- -/

theorem lemma5iRetimedTraversalABCSweepResidualWave_of_oneStepRows
    (hReset : Lemma5iLeaderWaveResetFrontierOneStep)
    (hTTL : Lemma5iLeaderWaveTTLPotentialOneStep) :
    Lemma5iRetimedTraversalABCSweepResidualWave := by
  unfold Lemma5iRetimedTraversalABCSweepResidualWave
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D _hlineage hmax

  let start :=
    lemma5iLeaderWaveStart ring D
  let host :=
    lemma5iLeaderWaveHost ring D
  let stop :=
    lemma5iLeaderWaveStopB ring D
  let h :=
    (D start).hits.val

  change
    (D start).signalR.val = kappa ∧
      h ≤ psi ∧
      ∀ sweep : DetSchedule n,
        sweep ∈
            allSchedules n
              (lemma5PaperSweepHorizon n) →
        !allClockResetsSeenB
            ring D sweep =
          true →
        ((lemma5iLeaderWaveRotatedMiss
              ring start sweep ||
            lemma5iLeaderWaveEncounterBad
              ring host stop sweep) ||
          lemma5iLeaderWaveTTLBad
            psi h ring host stop sweep) =
          true

  have hsig :
      (D start).signalR.val = kappa := by
    simpa [start] using
      q20107LeaderWaveStartSignal_eq_kappa
        ring D hmax

  have hh :
      h ≤ psi := by
    simpa [h, start] using
      q20107LeaderWaveInitialHits_le_psi
        ring D

  refine ⟨hsig, hh, ?_⟩
  intro sweep _hsweep hbad

  have hbase :
      q20107WavePrefixInvariant
        ring D h [] := by
    simpa [h, start] using
      q20107WavePrefixInvariant_nil
        hn3 hpsi hkappa
        ring D hmax

  have hinv0 :=
    q20107WavePrefixInvariant_append
      hReset hTTL
      hn3 hpsi
      ring D h
      [] sweep hbase

  have hinv :
      q20107WavePrefixInvariant
        ring D h sweep := by
    simpa using hinv0

  unfold q20107WavePrefixInvariant at hinv
  dsimp only at hinv
  rcases hinv with hstopped | hrest
  · cases hB :
      lemma5iLeaderWaveEncounterBad
        ring host stop sweep with
    | true =>
        simp [hB]
    | false =>
        have hnotB :
            ¬
              24 * n <
                stoppedPredictableHostHits
                  ring host stop sweep := by
          apply of_decide_eq_false
          simpa [lemma5iLeaderWaveEncounterBad]
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
            q20107StoppedBits_length_eq_hits
              ring host stop sweep

        have hbits24 :
            bits.length ≤ 24 * n := by
          rw [hbitsEq]
          exact hhits

        have hpad :
            24 * n ≤
              lotteryL7Horizon psi 5 :=
          q20107EncounterEnvelope_le_l7_5
            hpsi hnpow

        have hlen :
            bits.length ≤
              lotteryL7Horizon psi 5 :=
          Nat.le_trans hbits24 hpad

        have hcert :
            kappa ≤
              (lotteryRun psi
                (lotteryOffset h) bits).wins := by
          simpa [bits, host, stop]
            using hstopped.2

        have hwin :
            lotteryTarget psi 6 ≤
              (lotteryRun psi
                (lotteryOffset h) bits).wins := by
          unfold lotteryTarget
          omega

        have hC :
            lemma5iLeaderWaveTTLBad
                psi h ring host stop sweep =
              true := by
          unfold lemma5iLeaderWaveTTLBad
          dsimp only
          simp only [decide_eq_true_eq]
          exact ⟨hlen, hwin⟩

        simp [hB, hC]

  · rcases hrest with hdone | hlive
    · have hf :
          False := by
        have hb := hbad
        simp [hdone.2] at hb
      exact False.elim hf

    · have hA :
          lemma5iLeaderWaveRotatedMiss
              ring start sweep =
            true := by
        unfold lemma5iLeaderWaveRotatedMiss
        simp [start, hlive.1.2]
      simp [hA]

theorem lemma5iTraversalBudget_of_oneStepRows
    (hReset : Lemma5iLeaderWaveResetFrontierOneStep)
    (hTTL : Lemma5iLeaderWaveTTLPotentialOneStep) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hkappa : 48 * psi ≤ kappa)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    ModeStoppedTreeTransfer →
    PredictableHostTails →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    maxResetSignalB D = true →
    n *
        (allSchedules n
          (lemma5SweepHorizon n)).countP
          (fun suffix =>
            !allClockResetsSeenB ring D
              (suffix.take
                (lemma5PaperSweepHorizon n))) ≤
      n ^ lemma5SweepHorizon n := by
  exact
    lemma5iTraversalBudget_of_residualWave
      (lemma5iRetimedTraversalABCSweepResidualWave_of_oneStepRows
        hReset hTTL)

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABCSweepResidualWave_of_oneStepRows
#print axioms PPL.Modes.Lemma5.lemma5iTraversalBudget_of_oneStepRows
