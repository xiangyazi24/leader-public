import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderCases
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/--
Wrap-only transition remainder.

At the final/root edge, any white token that survives at the responder after
the complete P_PL-prime letter is the identical pre-step responder white
token.  This strips all Risky-path geometry from the wrap leaf.
-/
def L18GappedRiskyInsertedResponderWrapWhiteTokenFrame : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    ring.rightNeighbor e = root ->
    forall t : TokenData psi,
      PPL.tokenAt .white
          (pprimeStep ring C e
            (ring.rightNeighbor e)) =
        some t ->
      PPL.tokenAt .white
          (C (ring.rightNeighbor e)) =
        some t

/--
Non-wrap transition remainder.

For a responder already inside rooted S_0, every surviving white post-token
has exactly one of the three shapes relevant to risk:
* unchanged old responder token;
* old initiator positive token moved right, c |-> c-1;
* a negative token.

There is deliberately no fresh-positive alternative.  Under CDLAt and
non-wrap offset < psi, the initiator has rooted offset < psi, hence canonical
dist < psi, while a fresh white birth requires dist = tokenD' psi .white = psi.
-/
def L18GappedRiskyInsertedResponderNonwrapWhiteOutputRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    Not (ring.rightNeighbor e = root) ->
    cyclicOffset ring root
        (ring.rightNeighbor e) < psi ->
    forall t' : TokenData psi,
      PPL.tokenAt .white
          (pprimeStep ring C e
            (ring.rightNeighbor e)) =
        some t' ->
      (exists t : TokenData psi,
          PPL.tokenAt .white
              (C (ring.rightNeighbor e)) =
            some t /\
          t' = t) \/
      (exists t : TokenData psi,
          PPL.tokenAt .white (C e) = some t /\
          2 <=
            PPL.decodeOffset psi
              (PPL.tokenCode t) /\
          PPL.decodeOffset psi
              (PPL.tokenCode t') =
            PPL.decodeOffset psi
              (PPL.tokenCode t) - 1) \/
      PPL.decodeOffset psi
          (PPL.tokenCode t') < 0

private theorem q20231_tokenRisky_of_same_token
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (i : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (hC :
      PPL.tokenAt kind (C i) = some t)
    (hD :
      PPL.tokenAt kind (D i) = some t)
    (hRisk :
      PPL.tokenRisky ring root D i kind) :
    PPL.tokenRisky ring root C i kind := by
  unfold PPL.tokenRisky at hRisk ⊢
  rw [hD] at hRisk
  rw [hC]
  exact hRisk

/--
If a positive initiator token c>=2 moves to the responder with c-1, post-risk
at the responder implies pre-risk at the initiator.  The physical target is
unchanged; only the host advances by one and the code decreases by one.
-/
private theorem q20231_movedRisky_pre
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (t t' : TokenData psi)
    (hCtok :
      PPL.tokenAt kind (C e) = some t)
    (hDtok :
      PPL.tokenAt kind
          (D (ring.rightNeighbor e)) =
        some t')
    (hc2 :
      2 <=
        PPL.decodeOffset psi
          (PPL.tokenCode t))
    (hc' :
      PPL.decodeOffset psi
          (PPL.tokenCode t') =
        PPL.decodeOffset psi
          (PPL.tokenCode t) - 1)
    (he0 :
      InSegment ring root psi 0 e)
    (hRisk :
      PPL.tokenRisky ring root D
        (ring.rightNeighbor e) kind) :
    PPL.tokenRisky ring root C e kind := by
  cases hcode :
      PPL.decodeOffset psi
        (PPL.tokenCode t) with
  | negSucc m =>
      rw [hcode] at hc2
      omega
  | ofNat m =>
      have hm2 : 2 <= m := by
        rw [hcode] at hc2
        simp only [Int.ofNat_eq_coe] at hc2
        omega

      have hcode' :
          PPL.decodeOffset psi
              (PPL.tokenCode t') =
            ((m - 1 : Nat) : Int) := by
        rw [hc', hcode]
        simp only [Int.ofNat_eq_coe]
        omega

      unfold PPL.tokenRisky at hRisk ⊢
      rw [hDtok] at hRisk
      rw [hCtok]
      dsimp only at hRisk ⊢
      rw [hcode'] at hRisk
      rw [hcode]
      try dsimp only at hRisk ⊢

      constructor
      · omega
      · intro h
        by_cases hz : h.val = 0
        · rw [hz,
            l18Risk2ShiftRight_zero ring e]
          exact he0
        · have hval : h.val < m + 1 :=
            h.isLt
          let hp : Fin ((m - 1) + 1) :=
            ⟨h.val - 1, by omega⟩
          have hs := hRisk.2 hp
          have hsite :
              PPL.shiftRight ring
                  (ring.rightNeighbor e)
                  hp.val =
                PPL.shiftRight ring e h.val := by
            change
              PPL.shiftRight ring
                  (PPL.shiftRight ring e 1)
                  hp.val =
                PPL.shiftRight ring e h.val
            calc
              PPL.shiftRight ring
                  (PPL.shiftRight ring e 1)
                  hp.val =
                PPL.shiftRight ring e
                  (1 + hp.val) :=
                l18Risk2ShiftRight_add
                  ring e 1 hp.val
              _ =
                PPL.shiftRight ring e h.val := by
                congr 2
                dsimp only [hp]
                omega
          rw [hsite] at hs
          exact hs

/--
A negative white token at any rooted offset < psi is non-risky.  This is
packaged through the existing safe-code lemma rather than reopening Risky.
-/
private theorem q20231_negative_not_risky
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (D : Config n psi kappa)
    (i : Fin n)
    (hi :
      cyclicOffset ring root i < psi)
    (t : TokenData psi)
    (ht :
      PPL.tokenAt .white (D i) = some t)
    (hneg :
      PPL.decodeOffset psi
          (PPL.tokenCode t) < 0) :
    Not
      (PPL.tokenRisky ring root D i .white) := by
  let k : Nat :=
    cyclicOffset ring root i

  have hk : k < psi := by
    dsimp only [k]
    exact hi

  have hsite :
      PPL.shiftRight ring root k = i := by
    dsimp only [k]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root i

  have hsafe :
      forall u : TokenData psi,
        PPL.tokenAt .white
            (D (PPL.shiftRight ring root k)) =
          some u ->
        PPL.decodeOffset psi
              (PPL.tokenCode u) < 0 \/
          PPL.decodeOffset psi
              (PPL.tokenCode u) =
            ((psi : Nat) : Int) := by
    intro u hu
    rw [hsite] at hu
    have hut : u = t := by
      apply Option.some.inj
      exact hu.symm.trans ht
    subst u
    exact Or.inl hneg

  have hnr :=
    l18Risk2SafeCode_not_tokenRisky
      hpsi hlt ring root D
      k hk TokenKind.white hsafe

  rw [hsite] at hnr
  exact hnr

theorem l18GappedRiskyInsertedResponderWrapWhiteCase_of_tokenFrame
    (hframe :
      L18GappedRiskyInsertedResponderWrapWhiteTokenFrame) :
    L18GappedRiskyInsertedResponderWrapWhiteCase := by
  unfold
    L18GappedRiskyInsertedResponderWrapWhiteTokenFrame
    at hframe
  unfold
    L18GappedRiskyInsertedResponderWrapWhiteCase

  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root C e
  intro hC hroot hpre
  intro hpost

  cases ht :
      PPL.tokenAt .white
        (pprimeStep ring C e
          (ring.rightNeighbor e)) with
  | none =>
      unfold PPL.tokenRisky at hpost
      rw [ht] at hpost
      exact hpost

  | some t =>
      have htpre :=
        hframe
          hn3 hpsi hlt
          ring root C e
          hC hroot t ht

      have hpreRisk :=
        q20231_tokenRisky_of_same_token
          ring root
          C (pprimeStep ring C e)
          (ring.rightNeighbor e)
          TokenKind.white t
          htpre ht hpost

      exact hpre hpreRisk

theorem l18GappedRiskyInsertedResponderNonwrapWhiteCase_of_outputRow
    (hshape :
      L18GappedRiskyInsertedResponderNonwrapWhiteOutputRow) :
    L18GappedRiskyInsertedResponderNonwrapWhiteCase := by
  unfold
    L18GappedRiskyInsertedResponderNonwrapWhiteOutputRow
    at hshape
  unfold
    L18GappedRiskyInsertedResponderNonwrapWhiteCase

  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root C e
  intro hC hroot hroff hpreE hpreR
  intro hpost

  cases ht :
      PPL.tokenAt .white
        (pprimeStep ring C e
          (ring.rightNeighbor e)) with
  | none =>
      unfold PPL.tokenRisky at hpost
      rw [ht] at hpost
      exact hpost

  | some t' =>
      have hs :=
        hshape
          hn3 hpsi hlt
          ring root C e
          hC hroot hroff
          t' ht

      rcases hs with hstay | hmoved | hneg

      · rcases hstay with
          ⟨t, htpre, htt⟩
        subst t'
        have hpreRisk :=
          q20231_tokenRisky_of_same_token
            ring root
            C (pprimeStep ring C e)
            (ring.rightNeighbor e)
            TokenKind.white t
            htpre ht hpost
        exact hpreR hpreRisk

      · rcases hmoved with
          ⟨t, htpre, hc2, hc'⟩

        have hoff :=
          l18Gapped_rightNeighbor_offset_of_ne_root
            ring root e hroot

        have heoff :
            cyclicOffset ring root e < psi := by
          rw [hoff] at hroff
          omega

        have he0 :
            InSegment ring root psi 0 e := by
          unfold InSegment
          dsimp only
          have hmin :
              Nat.min psi n = psi :=
            Nat.min_eq_left
              (Nat.le_of_lt hlt)
          simpa [hmin] using heoff

        have hpreRisk :=
          q20231_movedRisky_pre
            ring root
            C (pprimeStep ring C e)
            e TokenKind.white
            t t'
            htpre ht
            hc2 hc'
            he0 hpost

        exact hpreE hpreRisk

      · exact
          (q20231_negative_not_risky
            hpsi hlt
            ring root
            (pprimeStep ring C e)
            (ring.rightNeighbor e)
            hroff t' ht hneg)
            hpost

/--
Both requested white leaves reduce to the two transition-only rows above.
-/
theorem l18GappedRiskyInsertedResponderWhiteCases_of_rows
    (hWrap :
      L18GappedRiskyInsertedResponderWrapWhiteTokenFrame)
    (hNonwrap :
      L18GappedRiskyInsertedResponderNonwrapWhiteOutputRow) :
    L18GappedRiskyInsertedResponderWrapWhiteCase /\
      L18GappedRiskyInsertedResponderNonwrapWhiteCase := by
  constructor
  · exact
      l18GappedRiskyInsertedResponderWrapWhiteCase_of_tokenFrame
        hWrap
  · exact
      l18GappedRiskyInsertedResponderNonwrapWhiteCase_of_outputRow
        hNonwrap

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapWhiteCase_of_tokenFrame
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapWhiteCase_of_outputRow
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWhiteCases_of_rows
