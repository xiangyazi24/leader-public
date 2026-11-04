import Leader.PPL.Modes.MidEntryLeaderWaveDebtAssembly


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


private theorem q20184RunPPL_append_local
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
      simp only [List.cons_append, runPPL, runPopulationSchedule]
      exact ih (C := pplStep ring C e)


private theorem q20184RunPPL_append_singleton
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n) :
    runPPL ring C (pre ++ [e]) =
      pplStep ring (runPPL ring C pre) e := by
  rw [q20184RunPPL_append_local]
  rfl


private theorem q20184StoppedBitsAux_append_singleton_of_not_reached
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (base word : DetSchedule n)
    (e : Fin n)
    (hreach : stopReachedAux stop base word = false) :
    stoppedEncounterBitsAux ring host stop base (word ++ [e]) =
      stoppedEncounterBitsAux ring host stop base word ++
        match incidentBit ring (host (base ++ word)) e with
        | none => []
        | some b => [b] := by
  induction word generalizing base with
  | nil =>
      have hs : stop base = false := by
        simpa [stopReachedAux] using hreach
      cases hb : incidentBit ring (host base) e <;>
        simp [stoppedEncounterBitsAux, hs, hb]
  | cons a rest ih =>
      cases hs : stop base with
      | true =>
          simp [stopReachedAux, hs] at hreach
      | false =>
          have htail :
              stopReachedAux stop (base ++ [a]) rest = false := by
            simpa [stopReachedAux, hs] using hreach
          have hih := ih (base := base ++ [a]) htail
          cases hb : incidentBit ring (host base) a with
          | none =>
              simpa [stoppedEncounterBitsAux, hs, hb,
                List.append_assoc] using hih
          | some b =>
              simpa [stoppedEncounterBitsAux, hs, hb,
                List.append_assoc] using
                  congrArg (fun xs => b :: xs) hih


theorem q20184StoppedBits_append_singleton_of_not_reached
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (word : DetSchedule n)
    (e : Fin n)
    (hreach : stopReached stop word = false) :
    stoppedEncounterBits ring host stop (word ++ [e]) =
      stoppedEncounterBits ring host stop word ++
        match incidentBit ring (host word) e with
        | none => []
        | some b => [b] := by
  unfold stoppedEncounterBits
  unfold stopReached at hreach
  simpa using
    q20184StoppedBitsAux_append_singleton_of_not_reached
      ring host stop [] word e hreach


private theorem q20184LotteryRun_append
    (k : Nat) (s : LotteryState) (u v : List Bool) :
    lotteryRun k s (u ++ v) =
      lotteryRun k (lotteryRun k s u) v := by
  induction u generalizing s with
  | nil =>
      rfl
  | cons b rest ih =>
      simp only [List.cons_append, lotteryRun]
      exact ih (s := lotteryStep k s b)


private theorem q20184DebtPotential_stop_discharge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (h : Nat)
    (pre : DetSchedule n)
    (hpot :
      Lemma5iLeaderWaveTTLDebtPotentialAt
        ring D h pre)
    (hstop :
      lemma5iLeaderWaveStopB ring D pre = true) :
    kappa ≤
      (lotteryRun psi
        (lotteryOffset h)
        (stoppedEncounterBits
          ring
          (lemma5iLeaderWaveHost ring D)
          (lemma5iLeaderWaveStopB ring D)
          pre)).wins := by
  unfold Lemma5iLeaderWaveTTLDebtPotentialAt at hpot
  dsimp only at hpot
  unfold lemma5iLeaderWaveStopB at hstop
  dsimp only at hstop
  have hsig :
      ((runPPL ring D pre)
        (lemma5iLeaderWaveHost ring D pre)).signalR.val = 0 := by
    exact of_decide_eq_true hstop
  by_cases hd :
      (lotteryRun psi
        (lotteryOffset h)
        (stoppedEncounterBits
          ring
          (lemma5iLeaderWaveHost ring D)
          (lemma5iLeaderWaveStopB ring D)
          pre)).headRun <
        ((runPPL ring D pre)
          (lemma5iLeaderWaveHost ring D pre)).hits.val
  · rw [if_pos hd] at hpot
    rw [hsig] at hpot
    simp only [Nat.add_zero] at hpot
    omega
  · rw [if_neg hd] at hpot
    rw [hsig] at hpot
    simp only [Nat.add_zero] at hpot
    omega


/-- Nonincident local arithmetic leaf.  The parser does not advance. -/
def Lemma5iWaveTTLDebtNonincidentRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x e : Fin n)
    (W : LotteryState),
    incidentBit ring x e = none →
    (C x).signalR.val ≤
      (pplStep ring C e
        (if e = x then ring.rightNeighbor x else x)).signalR.val +
        lemma5iLeaderWaveHitCharge ring x e →
    kappa +
        (if W.headRun < (C x).hits.val then 1 else 0) ≤
      W.wins + (C x).signalR.val →
    kappa +
        (if W.headRun <
            (pplStep ring C e
              (if e = x then
                ring.rightNeighbor x
              else x)).hits.val
          then 1 else 0) ≤
      W.wins +
        (pplStep ring C e
          (if e = x then
            ring.rightNeighbor x
          else x)).signalR.val


/-- T local arithmetic leaf.  The stopped parser appends false.
The tracked site must carry a live reset signal: with signalR = 0 a
zero/zero interaction leaves the responder with positive hits while the
parser resets its head run. -/
def Lemma5iWaveTTLDebtTRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x e : Fin n)
    (W : LotteryState),
    0 < (C x).signalR.val →
    incidentBit ring x e = some false →
    (C x).signalR.val ≤
      (pplStep ring C e
        (if e = x then ring.rightNeighbor x else x)).signalR.val +
        lemma5iLeaderWaveHitCharge ring x e →
    kappa +
        (if W.headRun < (C x).hits.val then 1 else 0) ≤
      W.wins + (C x).signalR.val →
    let W' := lotteryStep psi W false
    kappa +
        (if W'.headRun <
            (pplStep ring C e
              (if e = x then
                ring.rightNeighbor x
              else x)).hits.val
          then 1 else 0) ≤
      W'.wins +
        (pplStep ring C e
          (if e = x then
            ring.rightNeighbor x
          else x)).signalR.val


/-- H local arithmetic leaf.  The stopped parser appends true. -/
def Lemma5iWaveTTLDebtHRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x e : Fin n)
    (W : LotteryState),
    incidentBit ring x e = some true →
    (C x).signalR.val ≤
      (pplStep ring C e
        (if e = x then ring.rightNeighbor x else x)).signalR.val +
        lemma5iLeaderWaveHitCharge ring x e →
    kappa +
        (if W.headRun < (C x).hits.val then 1 else 0) ≤
      W.wins + (C x).signalR.val →
    let W' := lotteryStep psi W true
    kappa +
        (if W'.headRun <
            (pplStep ring C e
              (if e = x then
                ring.rightNeighbor x
              else x)).hits.val
          then 1 else 0) ≤
      W'.wins +
        (pplStep ring C e
          (if e = x then
            ring.rightNeighbor x
          else x)).signalR.val


theorem lemma5iLeaderWaveTTLDebtOneStep_of_caseRows
    (hNonincident : Lemma5iWaveTTLDebtNonincidentRow)
    (hT : Lemma5iWaveTTLDebtTRow)
    (hH : Lemma5iWaveTTLDebtHRow) :
    Lemma5iLeaderWaveTTLDebtOneStep := by
  unfold Lemma5iWaveTTLDebtNonincidentRow at hNonincident
  unfold Lemma5iWaveTTLDebtTRow at hT
  unfold Lemma5iWaveTTLDebtHRow at hH
  unfold Lemma5iLeaderWaveTTLDebtOneStep
  intro n psi kappa
  intro hn3 hpsi ring D h pre e
  intro hactive hhistoricallyLive hpot


  have hloc :=
    lemma5iLeaderWaveLocationOneStep_proved
      ring D pre e hactive
  have hmerge :=
    lemma5iLeaderWaveTTLMergeOneStep_proved
      hn3 hpsi ring D pre e hactive
  rw [q20184RunPPL_append_singleton] at hmerge
  rw [hloc] at hmerge


  let W0 :=
    lotteryRun psi
      (lotteryOffset h)
      (stoppedEncounterBits
        ring
        (lemma5iLeaderWaveHost ring D)
        (lemma5iLeaderWaveStopB ring D)
        pre)


  have hpot0 :
      kappa +
          (if W0.headRun <
              ((runPPL ring D pre)
                (lemma5iLeaderWaveHost ring D pre)).hits.val
            then 1 else 0) ≤
        W0.wins +
          ((runPPL ring D pre)
            (lemma5iLeaderWaveHost ring D pre)).signalR.val := by
    unfold Lemma5iLeaderWaveTTLDebtPotentialAt at hpot
    dsimp only at hpot
    simpa only [W0] using hpot


  have hbits :=
    q20184StoppedBits_append_singleton_of_not_reached
      ring
      (lemma5iLeaderWaveHost ring D)
      (lemma5iLeaderWaveStopB ring D)
      pre e hhistoricallyLive


  dsimp only
  cases hb :
      incidentBit ring
        (lemma5iLeaderWaveHost ring D pre) e with
  | none =>
      have hlocal :=
        hNonincident
          hn3 hpsi ring
          (runPPL ring D pre)
          (lemma5iLeaderWaveHost ring D pre)
          e W0 hb hmerge hpot0
      have hpostpot :
          Lemma5iLeaderWaveTTLDebtPotentialAt
            ring D h (pre ++ [e]) := by
        unfold Lemma5iLeaderWaveTTLDebtPotentialAt
        dsimp only
        rw [q20184RunPPL_append_singleton]
        rw [hloc]
        rw [hbits]
        rw [q20184LotteryRun_append]
        simpa only [hb, lotteryRun, W0] using hlocal
      constructor
      · intro hstop
        exact
          q20184DebtPotential_stop_discharge
            ring D h (pre ++ [e]) hpostpot hstop
      · intro _hnostop
        exact hpostpot
  | some b =>
      cases b with
      | false =>
          have hlive :
              0 < ((runPPL ring D pre)
                (lemma5iLeaderWaveHost ring D pre)).signalR.val := by
            have hs := hactive.1
            unfold lemma5iLeaderWaveStopB at hs
            dsimp only at hs
            have hne := of_decide_eq_false hs
            omega
          have hlocal :=
            hT
              hn3 hpsi ring
              (runPPL ring D pre)
              (lemma5iLeaderWaveHost ring D pre)
              e W0 hlive hb hmerge hpot0
          have hpostpot :
              Lemma5iLeaderWaveTTLDebtPotentialAt
                ring D h (pre ++ [e]) := by
            unfold Lemma5iLeaderWaveTTLDebtPotentialAt
            dsimp only
            rw [q20184RunPPL_append_singleton]
            rw [hloc]
            rw [hbits]
            rw [q20184LotteryRun_append]
            simpa only [hb, lotteryRun, W0] using hlocal
          constructor
          · intro hstop
            exact
              q20184DebtPotential_stop_discharge
                ring D h (pre ++ [e]) hpostpot hstop
          · intro _hnostop
            exact hpostpot
      | true =>
          have hlocal :=
            hH
              hn3 hpsi ring
              (runPPL ring D pre)
              (lemma5iLeaderWaveHost ring D pre)
              e W0 hb hmerge hpot0
          have hpostpot :
              Lemma5iLeaderWaveTTLDebtPotentialAt
                ring D h (pre ++ [e]) := by
            unfold Lemma5iLeaderWaveTTLDebtPotentialAt
            dsimp only
            rw [q20184RunPPL_append_singleton]
            rw [hloc]
            rw [hbits]
            rw [q20184LotteryRun_append]
            simpa only [hb, lotteryRun, W0] using hlocal
          constructor
          · intro hstop
            exact
              q20184DebtPotential_stop_discharge
                ring D h (pre ++ [e]) hpostpot hstop
          · intro _hnostop
            exact hpostpot


#print axioms PPL.Modes.Lemma5.q20184StoppedBits_append_singleton_of_not_reached
#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveTTLDebtOneStep_of_caseRows


end PPL.Modes.Lemma5
