import Leader.PPL.ReachCPB.MismatchHistFreshLiteralRows


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL
open PPL.Probability


/-!
Transport proofs for the residual rows.

`Lemma16AgedOrdinaryOwnerRow` and `Lemma16AgedNegOneOwnerRow` are proved
here: both are pure transport of the ghost-level invariant through the
offset branch recorded in the owner-case data.
-/


/-! ## Ring arithmetic -/


private theorem lt20155_shiftRight_zero
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    shiftRight ring x 0 = x := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt x.isLt]


private theorem lt20155_shiftRight_succ
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (d : Nat) :
    shiftRight ring x (d + 1) =
      ring.rightNeighbor (shiftRight ring x d) := by
  apply Fin.ext
  change (x.val + (d + 1)) % n =
    ((x.val + d) % n + 1) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem lt20155_rightNeighbor_injective
    {n : Nat}
    (ring : DirectedRing n)
    (a b : Fin n)
    (hab : ring.rightNeighbor a = ring.rightNeighbor b) :
    a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha1 : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha1] at hv
    by_cases hb1 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb1] at hv
      omega
    · have hbeq : b.val + 1 = n := by
        omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by
      omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb1 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb1] at hv
      omega
    · omega


/-! ## First-zero-bit specification -/


private theorem lt20155_firstZeroAux_spec
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ (fuel j0 : Nat),
      j0 ≤ firstZeroAux ring C start fuel j0 ∧
      firstZeroAux ring C start fuel j0 ≤ j0 + fuel ∧
      (∀ x : Nat,
        j0 ≤ x →
        x < firstZeroAux ring C start fuel j0 →
        (C (shiftRight ring start x)).id = true) ∧
      (firstZeroAux ring C start fuel j0 < j0 + fuel →
        (C (shiftRight ring start
          (firstZeroAux ring C start fuel j0))).id = false)
  | 0, j0 => by
      have h0 : firstZeroAux ring C start 0 j0 = j0 := rfl
      rw [h0]
      refine ⟨Nat.le_refl _, by omega, ?_, ?_⟩
      · intro x h1 h2
        omega
      · intro h
        omega
  | fuel + 1, j0 => by
      have ih :=
        lt20155_firstZeroAux_spec ring C start fuel (j0 + 1)
      have hs :
          firstZeroAux ring C start (fuel + 1) j0 =
            if (C (shiftRight ring start j0)).id = false then j0
            else firstZeroAux ring C start fuel (j0 + 1) := rfl
      rw [hs]
      by_cases hz : (C (shiftRight ring start j0)).id = false
      · rw [if_pos hz]
        refine ⟨Nat.le_refl _, by omega, ?_, fun _ => hz⟩
        intro x h1 h2
        omega
      · rw [if_neg hz]
        rcases ih with ⟨h1, h2, h3, h4⟩
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro x hx1 hx2
          by_cases hx : x = j0
          · rw [hx]
            revert hz
            cases (C (shiftRight ring start j0)).id <;> simp
          · exact h3 x (by omega) hx2
        · intro h
          exact h4 (by omega)


private theorem lt20155_firstZeroBit_true
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (x : Nat)
    (hx : x < firstZeroBit ring C start) :
    (C (shiftRight ring start x)).id = true := by
  have h := lt20155_firstZeroAux_spec ring C start psi 0
  exact h.2.2.1 x (Nat.zero_le x) hx


private theorem lt20155_firstZeroBit_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (hlt : firstZeroBit ring C start < psi) :
    (C (shiftRight ring start
      (firstZeroBit ring C start))).id = false := by
  have h := lt20155_firstZeroAux_spec ring C start psi 0
  exact h.2.2.2 (by
    have : firstZeroBit ring C start =
        firstZeroAux ring C start psi 0 := rfl
    omega)


/-! ## Payload and completed-list transport -/


private theorem lt20155_payloadCorrect_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (s : Fin n)
    (x : Nat)
    (t t' : TokenData psi)
    (hb : tokenBitBool t' = tokenBitBool t)
    (hc : tokenCarryBool t' = tokenCarryBool t)
    (h : payloadCorrect ring C s x t) :
    payloadCorrect ring C s x t' := by
  unfold payloadCorrect at h ⊢
  dsimp only at h ⊢
  rw [hb, hc]
  exact h


private theorem lt20155_noPrior_pre
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (lid : LineageId n)
    (h :
      Lemma16NoPriorCompletionId
        (ghostStep hpsi ring step G e) lid) :
    Lemma16NoPriorCompletionId G lid := by
  intro m hm
  apply h m
  simp only [ghostStep, List.mem_append]
  exact .inl (.inl hm)


/-! ## Macro-stage transport -/


private theorem lt20155_stage_right
    {n psi : Nat}
    (ring : DirectedRing n)
    (k e : Fin n)
    (source z : GhostToken n psi)
    (q : Nat)
    (hstage :
      Lemma16FreshMacroStageAt ring k e source q)
    (hpos :
      (2 : Int) ≤
        decodeOffset psi (tokenCode source.value))
    (hoff :
      decodeOffset psi (tokenCode z.value) =
        decodeOffset psi (tokenCode source.value) - 1)
    (hmoves :
      z.lmeta.moves = source.lmeta.moves + 1) :
    Lemma16FreshMacroStageAt
      ring k (ring.rightNeighbor e) z q := by
  unfold Lemma16FreshMacroStageAt at hstage ⊢
  dsimp only at hstage ⊢
  rw [hoff, hmoves]
  rcases hstage with ⟨x, hx, hp | hn⟩
  · rcases hp with ⟨h1, h2, h3, h4⟩
    refine ⟨x + 1, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hx, lt20155_shiftRight_succ]
    · omega
    · omega
    · omega
    · omega
  · exfalso
    omega


private theorem lt20155_stage_left
    {n psi : Nat}
    (ring : DirectedRing n)
    (k e : Fin n)
    (source z : GhostToken n psi)
    (q : Nat)
    (hstage :
      Lemma16FreshMacroStageAt ring k
        (ring.rightNeighbor e) source q)
    (hneg :
      decodeOffset psi (tokenCode source.value) ≤
        (-2 : Int))
    (hoff :
      decodeOffset psi (tokenCode z.value) =
        decodeOffset psi (tokenCode source.value) + 1)
    (hmoves :
      z.lmeta.moves = source.lmeta.moves + 1) :
    Lemma16FreshMacroStageAt ring k e z q := by
  unfold Lemma16FreshMacroStageAt at hstage ⊢
  dsimp only at hstage ⊢
  rw [hoff, hmoves]
  rcases hstage with ⟨x, hx, hp | hn⟩
  · exfalso
    omega
  · rcases hn with ⟨h1, h2, h3, h4⟩
    refine ⟨x - 1, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · apply lt20155_rightNeighbor_injective ring
      rw [hx, ← lt20155_shiftRight_succ]
      congr 1
      omega
    · omega
    · omega
    · omega
    · omega


/-! ## Row 2: birth / stay / ordinary transport -/


theorem lemma16AgedOrdinaryOwnerRow_proved :
    Lemma16AgedOrdinaryOwnerRow := by
  unfold Lemma16AgedOrdinaryOwnerRow
  intro n psi kappa hpsi ring Cepoch epoch b k kind step G e
  intro hinv i z t hid hbs hepoch hprior hdata
  have hpre :
      Lemma16NoPriorCompletionId G z.lmeta.id :=
    lt20155_noPrior_pre hpsi ring step G e z.lmeta.id hprior
  unfold Lemma16AgedLiveGoal
  cases hdata with
  | birth d =>
      rcases d with
        ⟨hsite, _hidB, hbirthSite, _hbirthStep,
          hmoves, hoffset, hbit, hcarry⟩
      have hek : e = k := by
        rw [← hbirthSite, hbs]
      subst hek
      have hidE : (G.phys e).id = (Cepoch e).id :=
        hinv.1 e
      refine ⟨0, by omega, ?_, ?_, ?_, ?_⟩
      · unfold Lemma16FreshMacroStageAt
        dsimp only
        rw [hoffset, hmoves]
        refine ⟨1, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
        · rw [hsite]
          rfl
        · omega
        · omega
        · omega
        · omega
      · unfold payloadCorrect
        dsimp only
        rw [lt20155_shiftRight_zero]
        rw [if_pos (Nat.zero_le _)]
        rw [hbit, hcarry, hidE]
        refine ⟨rfl, ?_⟩
        by_cases h0 : 0 < firstZeroBit ring Cepoch e
        · rw [if_pos h0]
          have ht :=
            lt20155_firstZeroBit_true ring Cepoch e 0 h0
          rw [lt20155_shiftRight_zero] at ht
          exact ht
        · rw [if_neg h0]
          have hz : firstZeroBit ring Cepoch e = 0 := by
            omega
          have hf :=
            lt20155_firstZeroBit_false ring Cepoch e
              (by omega)
          rw [hz, lt20155_shiftRight_zero] at hf
          exact hf
      · intro x hx
        omega
      · intro hneg
        rw [hoffset] at hneg
        omega
  | stay d =>
      rcases d with
        ⟨site, source, _hpair, hsite, howner, hsame⟩
      subst hsame
      subst hsite
      exact hinv.2 i z t howner hid hbs hepoch hpre
  | right d =>
      rcases d with
        ⟨source, howner, hsite, hmeta, hbit, hcarry,
          hpositive, hoffset⟩
      subst hsite
      have hidEq : z.lmeta.id = source.lmeta.id := by
        rw [hmeta]
        rfl
      have hbsEq :
          z.lmeta.birthSite = source.lmeta.birthSite := by
        rw [hmeta]
        rfl
      have hmovesEq :
          z.lmeta.moves = source.lmeta.moves + 1 := by
        rw [hmeta]
        rfl
      have hidS : source.lmeta.id = .born kind t := by
        rw [← hidEq]
        exact hid
      have hbsS : source.lmeta.birthSite = k := by
        rw [← hbsEq]
        exact hbs
      have hpreS :
          Lemma16NoPriorCompletionId G source.lmeta.id := by
        rw [← hidEq]
        exact hpre
      rcases hinv.2 e source t howner hidS hbsS hepoch hpreS with
        ⟨q, hq, hstage, hpay, hprefix, _hlatch⟩
      refine ⟨q, hq, ?_, ?_, hprefix, ?_⟩
      · exact
          lt20155_stage_right ring k e source z q
            hstage hpositive hoffset hmovesEq
      · exact
          lt20155_payloadCorrect_congr ring Cepoch k q
            source.value z.value hbit hcarry hpay
      · intro hneg
        rw [hoffset] at hneg
        omega
  | left d =>
      rcases d with
        ⟨source, howner, hsite, hmeta, hbit, hcarry,
          hnegative, hoffset⟩
      subst hsite
      have hidEq : z.lmeta.id = source.lmeta.id := by
        rw [hmeta]
        rfl
      have hbsEq :
          z.lmeta.birthSite = source.lmeta.birthSite := by
        rw [hmeta]
        rfl
      have hmovesEq :
          z.lmeta.moves = source.lmeta.moves + 1 := by
        rw [hmeta]
        rfl
      have hidS : source.lmeta.id = .born kind t := by
        rw [← hidEq]
        exact hid
      have hbsS : source.lmeta.birthSite = k := by
        rw [← hbsEq]
        exact hbs
      have hpreS :
          Lemma16NoPriorCompletionId G source.lmeta.id := by
        rw [← hidEq]
        exact hpre
      rcases
          hinv.2 (ring.rightNeighbor i) source t
            howner hidS hbsS hepoch hpreS with
        ⟨q, hq, hstage, hpay, hprefix, hlatch⟩
      refine ⟨q, hq, ?_, ?_, hprefix, ?_⟩
      · exact
          lt20155_stage_left ring k i source z q
            hstage hnegative hoffset hmovesEq
      · exact
          lt20155_payloadCorrect_congr ring Cepoch k q
            source.value z.value hbit hcarry hpay
      · intro _hneg
        exact hlatch (by omega)


/-! ## Row 4: the c = -1 turn -/


private theorem lt20155_age_bound
    (psi q : Nat)
    (hpsi : 2 ≤ psi)
    (hq : q < psi)
    (moves : Nat)
    (hmoves :
      moves = q * (2 * psi - 1) + (2 * psi - 1 - 1))
    (hage : moves < tokenTrajectoryMoves psi) :
    q + 1 < psi := by
  refine Nat.lt_of_le_of_ne (by omega) ?_
  intro hq1
  unfold tokenTrajectoryMoves at hage
  have e1 : q * (2 * psi - 1) + q = 2 * (q * psi) := by
    calc
      q * (2 * psi - 1) + q = q * ((2 * psi - 1) + 1) :=
        (Nat.mul_succ q (2 * psi - 1)).symm
      _ = q * (2 * psi) := by
        congr 1
        omega
      _ = 2 * (q * psi) := Nat.mul_left_comm q 2 psi
  have e2 : psi * psi = q * psi + psi := by
    calc
      psi * psi = (q + 1) * psi := by
        rw [hq1]
      _ = q * psi + psi := Nat.succ_mul q psi
  have e3 : 2 * psi * psi = 2 * (psi * psi) :=
    Nat.mul_assoc 2 psi psi
  omega


theorem lemma16AgedNegOneOwnerRow_proved :
    Lemma16AgedNegOneOwnerRow := by
  unfold Lemma16AgedNegOneOwnerRow
  intro n psi kappa hpsi ring Cepoch epoch b k kind step G e
  intro hinv hage i z t hid hbs hepoch hprior hdata
  have hpre :
      Lemma16NoPriorCompletionId G z.lmeta.id :=
    lt20155_noPrior_pre hpsi ring step G e z.lmeta.id hprior
  unfold Lemma16AgedLiveGoal
  rcases hdata with
    ⟨source, howner, hsite, hmeta, hsrcOff, hpostOff, hpayload⟩
  subst hsite
  have hidEq : z.lmeta.id = source.lmeta.id := by
    rw [hmeta]
    rfl
  have hbsEq :
      z.lmeta.birthSite = source.lmeta.birthSite := by
    rw [hmeta]
    rfl
  have hmovesEq :
      z.lmeta.moves = source.lmeta.moves + 1 := by
    rw [hmeta]
    rfl
  have hidS : source.lmeta.id = .born kind t := by
    rw [← hidEq]
    exact hid
  have hbsS : source.lmeta.birthSite = k := by
    rw [← hbsEq]
    exact hbs
  have hpreS :
      Lemma16NoPriorCompletionId G source.lmeta.id := by
    rw [← hidEq]
    exact hpre
  have hageS :
      source.lmeta.moves < tokenTrajectoryMoves psi :=
    hage (ring.rightNeighbor i) source howner
      ⟨t, hidS, hbsS⟩ hpreS
  rcases
      hinv.2 (ring.rightNeighbor i) source t
        howner hidS hbsS hepoch hpreS with
    ⟨q, hq, hstage, hpay, hprefix, hlatch⟩
  unfold Lemma16FreshMacroStageAt at hstage
  dsimp only at hstage
  rw [hsrcOff] at hstage
  rcases hstage with ⟨x, hx, hp | hn⟩
  · exfalso
    omega
  rcases hn with ⟨_h1, _h2, h3, h4⟩
  have hx2 : x = q + 1 + 1 := by
    omega
  have hmS :
      source.lmeta.moves =
        q * (2 * psi - 1) + (2 * psi - 1 - 1) := by
    omega
  have hsiteI : i = shiftRight ring k (q + 1) := by
    apply lt20155_rightNeighbor_injective ring
    rw [hx, hx2, ← lt20155_shiftRight_succ]
  have hq1 : q + 1 < psi :=
    lt20155_age_bound psi q hpsi hq
      source.lmeta.moves hmS hageS
  refine ⟨q + 1, hq1, ?_, ?_, ?_, ?_⟩
  · -- macro stage q + 1 at c = +psi
    unfold Lemma16FreshMacroStageAt
    dsimp only
    rw [hpostOff, hmovesEq]
    have hm :
        (q + 1) * (2 * psi - 1) =
          q * (2 * psi - 1) + (2 * psi - 1) :=
      Nat.succ_mul q (2 * psi - 1)
    refine ⟨q + 1, hsiteI, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · omega
    · omega
    · omega
    · omega
  · -- add-one payload recurrence
    have hidE :
        (G.phys i).id =
          (Cepoch (shiftRight ring k (q + 1))).id := by
      rw [hinv.1 i, hsiteI]
    have hpc := hpay
    unfold payloadCorrect at hpc ⊢
    dsimp only at hpc ⊢
    rcases hpc with ⟨_hbs0, hcs⟩
    by_cases hqJ : q < firstZeroBit ring Cepoch k
    · rw [if_pos hqJ] at hcs
      rw [hcs, if_pos rfl] at hpayload
      rcases hpayload with ⟨hb', hc'⟩
      rw [hb', hc', hidE]
      rw [if_pos (by omega : q + 1 ≤ firstZeroBit ring Cepoch k)]
      refine ⟨rfl, ?_⟩
      by_cases h2 : q + 1 < firstZeroBit ring Cepoch k
      · rw [if_pos h2]
        exact lt20155_firstZeroBit_true ring Cepoch k (q + 1) h2
      · rw [if_neg h2]
        have hJ : firstZeroBit ring Cepoch k = q + 1 := by
          omega
        have hf :=
          lt20155_firstZeroBit_false ring Cepoch k
            (by omega)
        rw [hJ] at hf
        exact hf
    · rw [if_neg hqJ] at hcs
      rw [hcs] at hpayload
      rw [if_neg (by decide : ¬ (false = true))] at hpayload
      rcases hpayload with ⟨hb', hc'⟩
      rw [hb', hc', hidE]
      rw [if_neg (by omega : ¬ (q + 1 ≤ firstZeroBit ring Cepoch k))]
      rw [if_neg (by omega : ¬ (q + 1 < firstZeroBit ring Cepoch k))]
      exact ⟨rfl, rfl⟩
  · -- target prefix: old prefix plus the old negative latch
    intro y hy
    by_cases hyq : y < q
    · exact hprefix y hyq
    · have hyEq : y = q := by
        omega
      rw [hyEq]
      exact hlatch (by rw [hsrcOff]; omega)
  · intro hneg
    rw [hpostOff] at hneg
    omega


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16AgedOrdinaryOwnerRow_proved
#print axioms PPL.Convergence.ReachCPB.lemma16AgedNegOneOwnerRow_proved
