import Leader.PPL.ReachCPB.MismatchHistFreshTerminalCompareUnique
import Leader.PPL.ReachCPB.MismatchHistFreshBranchRow
import Leader.PPL.ReachCPB.MismatchHistFreshDistRow
import Init.Omega


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL
open PPL.Probability


/-!
Truth check: TRUE.

There is no legal-offset counterexample.  The terminal branch in the row has
decodeOffset = +1, and +1 lies in the positive valid-offset range [1, psi]
because psi >= 2.

Suppose the final responder bit matched the token bit.  The public
c=1/border-geometry lemma moves that comparison to shiftRight b q.  Since
q+1=psi, payloadCorrect supplies the missing x=q add-one bit and
Lemma16TargetPrefix supplies all x<q bits.  Thus every x<psi in the target
word at b is the binary add-one bit of the source word at k.  The private
word recursion below is the converse-direction mirror of the two-case
(source head false / source head true with carry) recursion used by
idRowWord_add_one_bit in SPLAlgorithm3IdRow.lean.  It turns those psi bit
equalities into the segmentIdFrom add-one equation.  DistReadyCapped makes
both bad-border word lengths psi, and the frozen-id hypothesis moves the two
words from G.phys to Cepoch, contradicting Lemma16BadBorderWitness.
-/


/-! -------------------------------------------------------------------------
    Minimal mirror of the private SPLAlgorithm3IdRow binary word
------------------------------------------------------------------------- -/


private def terminalWord
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    Nat → Nat → Nat
  | 0, _ => 0
  | len + 1, j =>
      (if
          (C (PPL.shiftRight ring start j)).id = true
        then 1
        else 0) +
        2 * terminalWord ring C start len (j + 1)


private theorem terminalWord_factor
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ len j : Nat,
      PPL.segmentIdAux ring C start len j =
        2 ^ j * terminalWord ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [PPL.segmentIdAux, terminalWord]
  | succ len ih =>
      intro j
      simp only [PPL.segmentIdAux, terminalWord]
      rw [ih (j + 1)]
      cases hb :
          (C (PPL.shiftRight ring start j)).id with
      | false =>
          simp [hb, Nat.pow_succ,
            Nat.mul_add, Nat.mul_assoc]
      | true =>
          simp [hb, Nat.pow_succ,
            Nat.mul_add, Nat.mul_assoc]


private theorem terminal_segmentIdFrom_word
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (len : Nat) :
    PPL.segmentIdFrom ring C start len =
      terminalWord ring C start len 0 := by
  unfold PPL.segmentIdFrom
  rw [terminalWord_factor]
  simp


private theorem terminalWord_lt_pow
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ len j : Nat,
      terminalWord ring C start len j <
        2 ^ len := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [terminalWord]
  | succ len ih =>
      intro j
      have ht := ih (j + 1)
      cases hb :
          (C (PPL.shiftRight ring start j)).id with
      | false =>
          simp [terminalWord, hb, Nat.pow_succ] <;>
            omega
      | true =>
          simp [terminalWord, hb, Nat.pow_succ] <;>
            omega


private theorem terminalWord_eq_of_bits
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (a b : Fin n) :
    ∀ fuel j : Nat,
      (∀ x : Nat,
        j ≤ x →
        x < j + fuel →
        (C (PPL.shiftRight ring a x)).id =
          (C (PPL.shiftRight ring b x)).id) →
      terminalWord ring C a fuel j =
        terminalWord ring C b fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j _hbits
      simp [terminalWord]
  | succ fuel ih =>
      intro j hbits
      have hhead :=
        hbits j (by omega) (by omega)
      have htail :
          terminalWord ring C a fuel (j + 1) =
            terminalWord ring C b fuel (j + 1) := by
        apply ih (j + 1)
        intro x hx hx'
        exact
          hbits x
            (by omega)
            (by omega)
      simp only [terminalWord]
      rw [hhead, htail]


private theorem terminal_firstZeroAux_ge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ fuel j : Nat,
      j ≤ PPL.firstZeroAux ring C start fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j
      simp [PPL.firstZeroAux]
  | succ fuel ih =>
      intro j
      cases hb :
          (C (PPL.shiftRight ring start j)).id with
      | false =>
          simp [PPL.firstZeroAux, hb]
      | true =>
          have ht := ih (j + 1)
          simp [PPL.firstZeroAux, hb]
          omega


/--
Converse-direction mirror of the private idRowWord_add_one_bit recursion:
if every target bit is the source add-one bit, then the whole finite word is
source+1 modulo 2^fuel.
-/
private theorem terminalWord_add_one_of_bits
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (source target : Fin n) :
    ∀ fuel j : Nat,
      (∀ x : Nat,
        j ≤ x →
        x < j + fuel →
        (C (PPL.shiftRight ring target x)).id =
          (if
              x ≤
                PPL.firstZeroAux
                  ring C source fuel j
            then
              !(C
                (PPL.shiftRight
                  ring source x)).id
            else
              (C
                (PPL.shiftRight
                  ring source x)).id)) →
      terminalWord ring C target fuel j =
        (terminalWord ring C source fuel j + 1) %
          (2 ^ fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j _hbits
      simp [terminalWord]
  | succ fuel ih =>
      intro j hbits
      have hsTailLt :=
        terminalWord_lt_pow
          ring C source fuel (j + 1)

      cases hs :
          (C (PPL.shiftRight ring source j)).id with
      | false =>
          have hfirst :
              PPL.firstZeroAux
                  ring C source (fuel + 1) j =
                j := by
            simp [PPL.firstZeroAux, hs]

          have ht :
              (C
                  (PPL.shiftRight
                    ring target j)).id =
                true := by
            have hb :=
              hbits j
                (by omega)
                (by omega)
            simpa [hfirst, hs] using hb

          have htail :
              terminalWord ring C target
                  fuel (j + 1) =
                terminalWord ring C source
                  fuel (j + 1) := by
            apply
              terminalWord_eq_of_bits
                ring C target source
                fuel (j + 1)
            intro x hx hx'
            have hb :=
              hbits x
                (by omega)
                (by omega)
            have hnot : Not (x ≤ j) := by
              omega
            simpa [hfirst, hnot] using hb

          have hsumlt :
              terminalWord ring C source
                    (fuel + 1) j + 1 <
                2 ^ (fuel + 1) := by
            simp [terminalWord, hs, Nat.pow_succ]
            omega

          rw [Nat.mod_eq_of_lt hsumlt]
          simp [terminalWord, hs, ht, htail] <;>
            omega

      | true =>
          have hfirst :
              PPL.firstZeroAux
                  ring C source (fuel + 1) j =
                PPL.firstZeroAux
                  ring C source fuel (j + 1) := by
            simp [PPL.firstZeroAux, hs]

          have hge :=
            terminal_firstZeroAux_ge
              ring C source fuel (j + 1)

          have ht :
              (C
                  (PPL.shiftRight
                    ring target j)).id =
                false := by
            have hb :=
              hbits j
                (by omega)
                (by omega)
            have hjle :
                j ≤
                  PPL.firstZeroAux
                    ring C source fuel (j + 1) := by
              omega
            simpa [hfirst, hs, hjle] using hb

          have htailBits :
              ∀ x : Nat,
                j + 1 ≤ x →
                x < j + 1 + fuel →
                (C
                    (PPL.shiftRight
                      ring target x)).id =
                  (if
                      x ≤
                        PPL.firstZeroAux
                          ring C source fuel (j + 1)
                    then
                      !(C
                        (PPL.shiftRight
                          ring source x)).id
                    else
                      (C
                        (PPL.shiftRight
                          ring source x)).id) := by
            intro x hx hx'
            have hb :=
              hbits x
                (by omega)
                (by omega)
            simpa [hfirst] using hb

          have htail :=
            ih (j + 1) htailBits

          by_cases hsmall :
              terminalWord ring C source
                    fuel (j + 1) + 1 <
                2 ^ fuel
          · have htail0 := htail
            rw [Nat.mod_eq_of_lt hsmall] at htail0

            have hsumlt :
                terminalWord ring C source
                      (fuel + 1) j + 1 <
                  2 ^ (fuel + 1) := by
              simp [terminalWord, hs, Nat.pow_succ]
              omega

            rw [Nat.mod_eq_of_lt hsumlt]
            simp [terminalWord, hs, ht, htail0] <;>
              omega

          · have hover :
                terminalWord ring C source
                      fuel (j + 1) + 1 =
                  2 ^ fuel := by
              omega

            have htail0 :
                terminalWord ring C target
                    fuel (j + 1) = 0 := by
              calc
                terminalWord ring C target
                    fuel (j + 1) =
                    (terminalWord ring C source
                          fuel (j + 1) + 1) %
                      (2 ^ fuel) :=
                  htail
                _ = 0 := by
                  rw [hover, Nat.mod_self]

            have hsum :
                terminalWord ring C source
                      (fuel + 1) j + 1 =
                  2 ^ (fuel + 1) := by
              simp [terminalWord, hs, Nat.pow_succ]
              omega

            rw [hsum, Nat.mod_self]
            simp [terminalWord, ht, htail0]


private theorem terminalSegmentIdFrom_add_one_of_bits
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (source target : Fin n)
    (hbits :
      ∀ x : Nat,
        x < psi →
        (C (PPL.shiftRight ring target x)).id =
          lemma16ExpectedAddOneBit
            ring C source x) :
    PPL.segmentIdFrom ring C target psi =
      (PPL.segmentIdFrom ring C source psi + 1) %
        (2 ^ psi) := by
  simp only [terminal_segmentIdFrom_word]
  apply
    terminalWord_add_one_of_bits
      ring C source target psi 0
  intro x _hx0 hx
  have h := hbits x (by omega)
  first
  | exact h
  | (unfold lemma16ExpectedAddOneBit PPL.firstZeroBit at h
     exact h)
  | (unfold lemma16ExpectedAddOneBit PPL.firstZeroBit at h
     rw [h]
     by_cases hle : x ≤ PPL.firstZeroAux ring C source psi 0
     · rw [if_pos hle, if_pos hle]
     · rw [if_neg hle, if_neg hle])
  | (unfold lemma16ExpectedAddOneBit at h
     simp only [PPL.firstZeroBit] at h ⊢
     rw [h]
     split <;> split <;> simp_all)


/-! -------------------------------------------------------------------------
    Frozen-ID bridge for segmentIdFrom
------------------------------------------------------------------------- -/


private theorem terminalSegmentIdAux_eq_of_id_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (hid :
      ∀ i : Fin n,
        (D i).id = (C i).id)
    (start : Fin n) :
    ∀ len j : Nat,
      PPL.segmentIdAux ring D start len j =
        PPL.segmentIdAux ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      rfl
  | succ len ih =>
      intro j
      simp only [PPL.segmentIdAux]
      rw [hid (PPL.shiftRight ring start j)]
      rw [ih (j + 1)]


private theorem terminalSegmentIdFrom_eq_of_id_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (hid :
      ∀ i : Fin n,
        (D i).id = (C i).id)
    (start : Fin n)
    (len : Nat) :
    PPL.segmentIdFrom ring D start len =
      PPL.segmentIdFrom ring C start len := by
  unfold PPL.segmentIdFrom
  exact
    terminalSegmentIdAux_eq_of_id_eq
      ring C D hid start len 0


/-! -------------------------------------------------------------------------
    Row B
------------------------------------------------------------------------- -/


theorem lemma16TerminalFinalBitMismatchRow_proved :
    Lemma16TerminalFinalBitMismatchRow := by
  unfold Lemma16TerminalFinalBitMismatchRow

  intro n psi kappa
  intro hpsi hn3 ring Cepoch
  intro b k kind G e z q
  intro hgeom hdist hids
  intro hq hqLast hstage
  intro hpay hprefix hbad hc1

  intro hmatch

  have hresponder :=
    lemma16FreshMacroStage_c1_responder_of_borderGeometry
      hpsi ring b k e z q
      hgeom hstage hc1

  have hpayBit :
      PPL.tokenBitBool z.value =
        lemma16ExpectedAddOneBit
          ring Cepoch k q := by
    unfold PPL.payloadCorrect at hpay
    unfold lemma16ExpectedAddOneBit
    dsimp only at hpay ⊢
    exact hpay.1

  have hfinal :
      (Cepoch
          (PPL.shiftRight ring b q)).id =
        lemma16ExpectedAddOneBit
          ring Cepoch k q := by
    calc
      (Cepoch
          (PPL.shiftRight ring b q)).id =
          (G.phys
            (PPL.shiftRight ring b q)).id :=
        (hids _).symm
      _ =
          (G.phys
            (ring.rightNeighbor e)).id := by
        rw [hresponder]
      _ = PPL.tokenBitBool z.value :=
        hmatch.symm
      _ =
          lemma16ExpectedAddOneBit
            ring Cepoch k q :=
        hpayBit

  have hbits :
      ∀ x : Nat,
        x < psi →
        (Cepoch
            (PPL.shiftRight ring b x)).id =
          lemma16ExpectedAddOneBit
            ring Cepoch k x := by
    intro x hx
    by_cases hxq : x < q
    · exact hprefix x hxq
    · have hxeq : x = q := by
        omega
      subst x
      exact hfinal

  have hwordEpoch :
      PPL.segmentIdFrom
          ring Cepoch b psi =
        (PPL.segmentIdFrom
            ring Cepoch k psi + 1) %
          (2 ^ psi) :=
    terminalSegmentIdFrom_add_one_of_bits
      ring Cepoch k b hbits

  have hb :
      PPL.IsBorder G.phys b :=
    hbad.1

  have hdistPair :=
    lemma16DistReady_nextBorderDistance_eq
      hpsi ring G.phys b hdist hb

  have hdn :
      PPL.nextBorderDistance
          ring G.phys b =
        psi :=
    hdistPair.1

  have hdp :
      PPL.prevBorderDistance
          ring G.phys b =
        psi :=
    hdistPair.2

  have hbadPsi :
      PPL.segmentIdFrom
          ring G.phys b psi ≠
        (PPL.segmentIdFrom
            ring G.phys k psi + 1) %
          (2 ^ psi) := by
    have hneq := hbad.2.2.2
    simpa [hdn, hdp] using hneq

  have hfreezeB :
      PPL.segmentIdFrom
          ring G.phys b psi =
        PPL.segmentIdFrom
          ring Cepoch b psi :=
    terminalSegmentIdFrom_eq_of_id_eq
      ring Cepoch G.phys hids b psi

  have hfreezeK :
      PPL.segmentIdFrom
          ring G.phys k psi =
        PPL.segmentIdFrom
          ring Cepoch k psi :=
    terminalSegmentIdFrom_eq_of_id_eq
      ring Cepoch G.phys hids k psi

  apply hbadPsi
  rw [hfreezeB, hfreezeK]
  exact hwordEpoch


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16TerminalFinalBitMismatchRow_proved
