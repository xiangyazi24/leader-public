import Leader.PPL.Modes.MidEntryWaveTTLDebtRoute

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

private theorem q20193RightNeighborLeftNeighbor
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

private theorem q20193RightNeighborNeSelf
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

private theorem q20193HDebtArithmetic
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (W : LotteryState)
    (hresp :
      DetermineModeResponderCases l r)
    (hpot :
      kappa +
          (if W.headRun < r.hits.val
            then 1 else 0) ≤
        W.wins + r.signalR.val) :
    let q := PPL.determineMode l r
    let W' := lotteryStep psi W true
    kappa +
        (if W'.headRun < q.2.hits.val
          then 1 else 0) ≤
      W'.wins + q.2.signalR.val := by
  dsimp only at hresp ⊢
  have hhits : r.hits.val ≤ psi := by
    have ht := r.hits.isLt
    omega

  rcases hresp with hz | hl | hr
  · rcases hz with
      ⟨_ha0, hrs0, hqs0, hqh⟩
    rw [hrs0] at hpot
    rw [hqs0]

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
      rw [hqh, if_neg hbumpNe, hbump]

      by_cases hwin :
          psi ≤ W.headRun + 1
      · by_cases hdebt :
            W.headRun < r.hits.val
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
      · by_cases hdebt :
            W.headRun < r.hits.val
        · have hpost :
              W.headRun + 1 <
                r.hits.val + 1 := by
            omega
          simp
            [lotteryStep, hwin,
              hdebt, hpost]
            at hpot ⊢
          omega
        · have hpost :
              ¬ (W.headRun + 1 <
                r.hits.val + 1) := by
            omega
          simp
            [lotteryStep, hwin,
              hdebt, hpost]
            at hpot ⊢
          omega
    · have hbump :
          bumpedHitsVal r = psi := by
        unfold bumpedHitsVal
        exact
          Nat.min_eq_right
            (by omega)
      rw [hqh]
      simp only [hbump, if_pos rfl]
      by_cases hwin :
          psi ≤ W.headRun + 1
      · by_cases hdebt :
            W.headRun < r.hits.val
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
      · by_cases hdebt :
            W.headRun < r.hits.val
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega

  · rcases hl with
      ⟨_haPos, hOldLe, hqs, hqh⟩
    rw [hqs, hqh]
    by_cases hwin :
        psi ≤ W.headRun + 1
    · by_cases hdebt :
          W.headRun < r.hits.val
      · simp
          [lotteryStep, hwin, hdebt]
          at hpot ⊢
        omega
      · simp
          [lotteryStep, hwin, hdebt]
          at hpot ⊢
        omega
    · by_cases hdebt :
          W.headRun < r.hits.val
      · simp
          [lotteryStep, hwin, hdebt]
          at hpot ⊢
        omega
      · simp
          [lotteryStep, hwin, hdebt]
          at hpot ⊢
        omega

  · rcases hr with
      ⟨hOldPos, hqs, hqh⟩
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

      by_cases hwin :
          psi ≤ W.headRun + 1
      · by_cases hdebt :
            W.headRun < r.hits.val
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
      · by_cases hdebt :
            W.headRun < r.hits.val
        · have hpost :
              W.headRun + 1 <
                r.hits.val + 1 := by
            omega
          simp
            [lotteryStep, hwin,
              hdebt, hpost]
            at hpot ⊢
          omega
        · have hpost :
              ¬ (W.headRun + 1 <
                r.hits.val + 1) := by
            omega
          simp
            [lotteryStep, hwin,
              hdebt, hpost]
            at hpot ⊢
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

      by_cases hwin :
          psi ≤ W.headRun + 1
      · by_cases hdebt :
            W.headRun < r.hits.val
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
      · by_cases hdebt :
            W.headRun < r.hits.val
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega
        · simp
            [lotteryStep, hwin, hdebt]
            at hpot ⊢
          omega

theorem lemma5iWaveTTLDebtHRow_proved :
    Lemma5iWaveTTLDebtHRow := by
  unfold Lemma5iWaveTTLDebtHRow
  intro n psi kappa
  intro hn3 hpsi ring C x e W
  intro hH _hmerge hpot

  have he :
      e = ring.leftNeighbor x := by
    by_cases h :
        e = ring.leftNeighbor x
    · exact h
    · simp [incidentBit, h] at hH

  have hrx :
      ring.rightNeighbor e = x := by
    rw [he]
    exact
      q20193RightNeighborLeftNeighbor
        ring x

  have hne :
      ring.rightNeighbor e ≠ e :=
    q20193RightNeighborNeSelf
      (by omega) ring e

  have hex : e ≠ x := by
    intro hx
    apply hne
    calc
      ring.rightNeighbor e = x := hrx
      _ = e := hx.symm

  have hd :=
    determineModeSignalProjection
      hpsi (C e) (C x)
  dsimp only at hd
  have hresp :
      DetermineModeResponderCases
        (C e) (C x) :=
    hd.2.2

  have hs :=
    step_signal_projection_of_stable
      postDetermineModeSignalStable
      hpsi ring C e hne
  dsimp only at hs
  rw [hrx] at hs

  have hpostSignal :
      (pplStep ring C e x).signalR.val =
        (PPL.determineMode
          (C e) (C x)).2.signalR.val := by
    have h :=
      congrArg Fin.val hs.2.2.1
    change
      (pplStep ring C e x).signalR.val =
        (PPL.determineMode
          (C e) (C x)).2.signalR.val
      at h
    exact h

  have hpostHits :
      (pplStep ring C e x).hits.val =
        (PPL.determineMode
          (C e) (C x)).2.hits.val := by
    have h :=
      congrArg Fin.val hs.2.2.2
    change
      (pplStep ring C e x).hits.val =
        (PPL.determineMode
          (C e) (C x)).2.hits.val
      at h
    exact h

  have harith :=
    q20193HDebtArithmetic
      hpsi (C e) (C x) W
      hresp hpot
  dsimp only at harith ⊢
  rw [if_neg hex]
  rw [hpostSignal, hpostHits]
  exact harith

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iWaveTTLDebtHRow_proved
