import Leader.PPL.Modes.MidEntryWaveTTLDebtHeadRow

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

private theorem q20194RightNeighborLeftNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by
      omega
    rw [hs, Nat.mod_self]
  · have heq :
        i.val + n - 1 =
          n + (i.val - 1) := by
      omega
    have hlt : i.val - 1 < n := by
      omega
    have hleft :
        (i.val + n - 1) % n =
          i.val - 1 := by
      rw [heq]
      simp
        [Nat.add_mod,
          Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs :
        i.val - 1 + 1 = i.val := by
      omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

private theorem q20194LeftNeighborRightNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq :
        i.val + 1 + n - 1 =
          n + i.val := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem q20194RightNeighborNeSelf
    {n : Nat}
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem q20194SignalLeArmed
    {psi kappa : Nat}
    (q : PPL.State psi kappa) :
    q.signalR.val ≤ armedSignalVal q := by
  unfold armedSignalVal
  by_cases hlead : q.leader = true
  · rw [if_pos hlead]
    have hlt := q.signalR.isLt
    omega
  · rw [if_neg hlead]
    exact Nat.le_refl _

private theorem q20194TDebtArithmetic
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (W : LotteryState)
    (hlive : 0 < l.signalR.val)
    (hresp :
      DetermineModeResponderCases l r)
    (hpot :
      kappa +
          (if W.headRun < l.hits.val
            then 1 else 0) ≤
        W.wins + l.signalR.val) :
    let q := PPL.determineMode l r
    let W' := lotteryStep psi W false
    kappa +
        (if W'.headRun < q.2.hits.val
          then 1 else 0) ≤
      W'.wins + q.2.signalR.val := by
  dsimp only at hresp ⊢

  have hbase :
      kappa ≤ W.wins + l.signalR.val := by
    by_cases hdebt :
        W.headRun < l.hits.val
    · rw [if_pos hdebt] at hpot
      omega
    · rw [if_neg hdebt] at hpot
      omega

  have hle :
      l.signalR.val ≤ armedSignalVal l :=
    q20194SignalLeArmed l

  have hapos :
      0 < armedSignalVal l := by
    omega

  rcases hresp with hz | hl | hr
  · rcases hz with
      ⟨ha0, _hrs0, _hqs0, _hqh⟩
    have hf : False := by
      omega
    exact False.elim hf

  · rcases hl with
      ⟨_haPos, _hOldLe, hqs, hqh⟩
    rw [hqs, hqh]
    simp [lotteryStep]
    omega

  · rcases hr with
      ⟨hStrong, hqs, hqh⟩
    by_cases hcap :
        r.hits.val + 1 < psi
    · have hbump :
          bumpedHitsVal r =
            r.hits.val + 1 := by
        unfold bumpedHitsVal
        exact
          Nat.min_eq_left
            (by omega)
      have hbumpNe :
          bumpedHitsVal r ≠ psi := by
        rw [hbump]
        omega
      rw [hqs, hqh,
        if_neg hbumpNe,
        if_neg hbumpNe,
        hbump]
      simp [lotteryStep]
      omega
    · have hbump :
          bumpedHitsVal r = psi := by
        unfold bumpedHitsVal
        exact
          Nat.min_eq_right
            (by omega)
      rw [hqs, hqh]
      simp only
        [hbump, if_pos rfl]
      simp [lotteryStep]
      omega

theorem lemma5iWaveTTLDebtNonincidentRow_proved :
    Lemma5iWaveTTLDebtNonincidentRow := by
  unfold Lemma5iWaveTTLDebtNonincidentRow
  intro n psi kappa
  intro hn3 _hpsi ring C x e W
  intro hnone _hmerge hpot

  have hleft :
      e ≠ ring.leftNeighbor x := by
    intro h
    subst e
    simp [incidentBit] at hnone

  have hxl :
      x ≠ ring.leftNeighbor x := by
    intro h
    apply
      q20194RightNeighborNeSelf
        (by omega) ring x
    calc
      ring.rightNeighbor x =
          ring.rightNeighbor
            (ring.leftNeighbor x) :=
        congrArg ring.rightNeighbor h
      _ = x :=
        q20194RightNeighborLeftNeighbor
          ring x

  have hex : e ≠ x := by
    intro h
    subst e
    simp [incidentBit, hxl] at hnone

  have hrx :
      ring.rightNeighbor e ≠ x := by
    intro h
    apply hleft
    have hh :=
      congrArg ring.leftNeighbor h
    rw [q20194LeftNeighborRightNeighbor] at hh
    exact hh

  have haway :=
    step_signal_hits_away
      ring C e x
      (Ne.symm hex)
      (Ne.symm hrx)

  have hpostSignal :
      (pplStep ring C e x).signalR.val =
        (C x).signalR.val := by
    simpa
      [PPL.Probability.pplStep,
        PPL.Modes.SignalLineage.step]
      using
        congrArg Fin.val haway.1

  have hpostHits :
      (pplStep ring C e x).hits.val =
        (C x).hits.val := by
    simpa
      [PPL.Probability.pplStep,
        PPL.Modes.SignalLineage.step]
      using
        congrArg Fin.val haway.2

  simpa
    [hex,
      lemma5iLeaderWaveHitCharge,
      hrx,
      hpostSignal,
      hpostHits]
    using hpot

theorem lemma5iWaveTTLDebtTRow_proved :
    Lemma5iWaveTTLDebtTRow := by
  unfold Lemma5iWaveTTLDebtTRow
  intro n psi kappa
  intro hn3 hpsi ring C x e W
  intro hlive hT _hmerge hpot

  have he : e = x := by
    by_cases hleft :
        e = ring.leftNeighbor x
    · simp [incidentBit, hleft] at hT
    · by_cases h : e = x
      · exact h
      · simp [incidentBit, hleft, h] at hT
  subst e

  have hself :
      ring.rightNeighbor x ≠ x :=
    q20194RightNeighborNeSelf
      (by omega) ring x

  have hd :=
    determineModeSignalProjection
      hpsi
      (C x)
      (C (ring.rightNeighbor x))
  dsimp only at hd
  have hresp :
      DetermineModeResponderCases
        (C x)
        (C (ring.rightNeighbor x)) :=
    hd.2.2

  have hs :=
    step_signal_projection_of_stable
      postDetermineModeSignalStable
      hpsi ring C x hself
  dsimp only at hs

  have hpostSignal :
      (pplStep ring C x
        (ring.rightNeighbor x)).signalR.val =
        (PPL.determineMode
          (C x)
          (C (ring.rightNeighbor x))).2.signalR.val := by
    have h :=
      congrArg Fin.val hs.2.2.1
    change
      (pplStep ring C x
        (ring.rightNeighbor x)).signalR.val =
        (PPL.determineMode
          (C x)
          (C (ring.rightNeighbor x))).2.signalR.val
      at h
    exact h

  have hpostHits :
      (pplStep ring C x
        (ring.rightNeighbor x)).hits.val =
        (PPL.determineMode
          (C x)
          (C (ring.rightNeighbor x))).2.hits.val := by
    have h :=
      congrArg Fin.val hs.2.2.2
    change
      (pplStep ring C x
        (ring.rightNeighbor x)).hits.val =
        (PPL.determineMode
          (C x)
          (C (ring.rightNeighbor x))).2.hits.val
      at h
    exact h

  have harith :=
    q20194TDebtArithmetic
      hpsi
      (C x)
      (C (ring.rightNeighbor x))
      W hlive hresp hpot

  dsimp only at harith ⊢
  rw [if_pos rfl]
  rw [hpostSignal, hpostHits]
  exact harith

theorem lemma5iLeaderWaveTTLDebtOneStep_proved :
    Lemma5iLeaderWaveTTLDebtOneStep :=
  lemma5iLeaderWaveTTLDebtOneStep_of_caseRows
    lemma5iWaveTTLDebtNonincidentRow_proved
    lemma5iWaveTTLDebtTRow_proved
    lemma5iWaveTTLDebtHRow_proved

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iWaveTTLDebtNonincidentRow_proved
#print axioms PPL.Modes.Lemma5.lemma5iWaveTTLDebtTRow_proved
#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveTTLDebtOneStep_proved
