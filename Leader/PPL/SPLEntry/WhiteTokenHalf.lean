import Leader.PPL.SPLEntry.EstablishmentTokensAtCut
import Leader.PPL.SPLEntry.BuiltPairSelectedWhite
import Init.Omega

/-!
# L18 prime: white selected token half, and the token-half establishment cut

`L18PrimeSelectedWhiteTokenHalfFrame` (`L18PrimeEstablishmentTokensAtCut.lean`)
is the white sibling of `l18PrimeStepSelectedTokenHalfBlack`: one prime letter
preserves the white token implication of any pair `s ≤ b` at the two
interacting sites, from the white token implication of pair `s` alone.

It is obtained exactly as the black one: `q20305OldCorrectTokWhite` is a copy
of the private white old-image transport `q20299OldCorrect`
(`L18PrimeBuiltPairSelectedWhite.lean`) whose pre-hypothesis `L18BuildPairOK`
is weakened to the two white token implications at `e` and `rightNeighbor e`;
the original proof reads nothing else of the pair.  The fresh-birth branch
reuses the private `q20299FreshCorrect` unchanged.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option linter.unusedVariables false

open PPL
open PPL.Safety.SPL

open Lean Elab Term Meta in
elab "q20305w% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairSelectedWhite).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20305ids% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairIds).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20305route% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.Safety.SPLWhiteCorrectnessRoute).num 0).str
      "PPL").str "Safety").str "SPL").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20305init% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.Safety.SPLWhiteOldImageInitiatorMovedRightSemantic).num 0).str
      "PPL").str "Safety").str "SPL").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20305resp% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.Safety.SPLWhiteOldImageResponderSemantic).num 0).str
      "PPL").str "Safety").str "SPL").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20305carry% " s:str : term => do
  let n : Name :=
    ((((`_private.Leader.PPL.TokenCorrectness.PersistenceCarry).num 0).str
      "PPL").str s.getString)
  mkConstWithFreshMVarLevels n


/-- Copy of the private `q20299OldCorrect` (L18PrimeBuiltPairSelectedWhite)
with its pre-hypothesis weakened from `L18BuildPairOK` to the white token
implications at the two interacting sites (the only parts the proof reads). -/
theorem q20305OldCorrectTokWhite
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (hCDL : CDLAt ring root C)
    (hPostCDL : CDLAt ring root D)
    (hpreE :
      (ValidToken .white C e ∧
          WorkingFor ring root C e .white seg.val) →
        CorrectToken ring root C e .white seg.val)
    (hpreR :
      (ValidToken .white C (ring.rightNeighbor e) ∧
          WorkingFor ring root C (ring.rightNeighbor e) .white seg.val) →
        CorrectToken ring root C (ring.rightNeighbor e) .white seg.val)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root D seg.val)
    (i : Fin n)
    (hi : i = e ∨ i = ring.rightNeighbor e)
    (t' : TokenData psi)
    (hpost :
      tokenAt .white (D i) = some t')
    (hOld :
      SPLPostTokenOldImage
        hpsi ring C e i .white t')
    (hVW :
      ValidToken .white D i ∧
        WorkingFor ring root D
          i .white seg.val) :
    CorrectToken ring root D i .white seg.val := by
  replace hOld :=
    (q20305w% "q20299OldImageWhite") hpsi ring C e i t' hOld
  dsimp only at hOld
  rcases hOld with
    ⟨j, t, _hwhere, hCtok, hshape⟩

  let r := ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2

  have hp0 :=
    (q20305w% "q20299PreFrame")
      hpsi ring root C e hCDL
  have hp :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        p.2.dist = (C r).dist ∧
        tokenAt .white p.1 =
          tokenAt .white (C e) ∧
        tokenAt .white p.2 =
          tokenAt .white (C r) := by
    simpa [p, pre, r] using hp0

  rcases hshape with hleft | hright | hoff
  · rcases hleft with
      ⟨hje, hl0tok, hmove⟩
    subst j

    have hl0 :
        tokenAt .white
            (sourceClear .white p.1) =
          some t := by
      simpa [p, pre, r] using hl0tok
    have hvalidPre :
        ValidToken .white C e :=
      (q20305init% "q20276ValidOfCleared")
        .white C e p.1 t
        hp.1 hCtok hl0

    rcases hmove with hclosed | hopen
    · rcases hclosed with
        ⟨hgate, hie, hq⟩
      subst i
      have hgate' :
          ¬ ((sourceClear .white p.1).last = false ∧
              (sourceClear .white p.2).last = false) := by
        simpa [p, pre, r] using hgate
      have hq' :
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).1 =
            some t' := by
        simpa [p, pre, r] using hq
      have htt :
          t' = t :=
        (q20305route% "splWhiteOldClosedLeft_same")
          hpsi .white p.1 p.2
          t t' hl0 hgate' hq'
      subst t'
      have hworkPre :
          WorkingFor ring root C e .white seg.val :=
        (q20305resp%
          "splWhiteSemanticWorking_same_backward")
          ring root C D e .white seg.val t
          hCtok hpost hVW.2
      have hcorrPre :
          CorrectToken ring root C e .white seg.val :=
        hpreE
          ⟨hvalidPre, hworkPre⟩
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg C D
          e .white t
          hCtok hpost hsrc hcorrPre

    · rcases hopen with
        ⟨hgate, hrnone, hwhere⟩
      have hgate' :
          (sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false := by
        simpa [p, pre, r] using hgate
      have hrnone' :
          tokenAt .white
              (sourceClear .white p.2) =
            none := by
        simpa [p, pre, r] using hrnone

      rcases hwhere with houtLeft | houtRight
      · rcases houtLeft with ⟨hie, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).1 =
              some t' := by
          simpa [p, pre, r] using hq
        have htt :
            t' = t :=
          (q20305route% "splWhiteOldOpenLeft_same")
            hpsi .white p.1 p.2
            t t' hgate' hl0 hrnone' hq'
        subst t'
        have hworkPre :
            WorkingFor ring root C e .white seg.val :=
          (q20305resp%
            "splWhiteSemanticWorking_same_backward")
            ring root C D e .white seg.val t
            hCtok hpost hVW.2
        have hcorrPre :
            CorrectToken ring root C e .white seg.val :=
          hpreE
            ⟨hvalidPre, hworkPre⟩
        exact
          PPL.remark2Right_correct_same_occurrence
            ring root seg C D
            e .white t
            hCtok hpost hsrc hcorrPre

      · rcases houtRight with ⟨hir, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).2 =
              some t' := by
          simpa [p, pre, r] using hq
        have hliteral :
            PPL.Remark2RightLiteralMotionData
              hpsi ring e r t t' := by
          simpa [r] using
            (q20305init% "q20276LiteralMotion")
              hpsi ring e p.1 p.2
              t t' hgate' hl0 hrnone' hq'

        have hworkPre :
            WorkingFor ring root C e .white seg.val := by
          have hm := hliteral
          unfold PPL.Remark2RightLiteralMotionData at hm
          rcases hm.2.2 with hord | hturn
          · exact
              (q20305init% "q20276OrdinaryWorkingBackward")
                ring root C D e seg t t'
                hCtok hpost
                hord.1 hord.2.1
                (by simpa [r] using hord.2.2)
                hVW.2
          · exact
              (q20305w% "q20299TurnWorkingBackward")
                hpsi ring root C D e seg
                t t' hPostCDL
                hCtok hturn.1 hpost hturn.2
                hVW.1 hVW.2

        have hcorrPre :
            CorrectToken ring root C e .white seg.val :=
          hpreE
            ⟨hvalidPre, hworkPre⟩

        have hmotion :
            PPL.Remark2RightMotionData
              ring root seg.val e r t t' :=
          PPL.remark2RightLiteralMotionData_to_motion
            hpsi ring root seg C D
            e r .white t t'
            hCtok hpost
            hvalidPre hworkPre hcorrPre
            hCDL hPostCDL hsrc
            (by rfl) hliteral

        exact
          PPL.remark2Right_motion_preserves_correct
            ring root seg C D
            e r .white t t'
            hCtok hpost hsrc
            hcorrPre hmotion

  · rcases hright with
      ⟨hjr, hr0tok, hmove⟩
    subst j

    have hr0 :
        tokenAt .white
            (sourceClear .white p.2) =
          some t := by
      simpa [p, pre, r] using hr0tok
    have hvalidPre :
        ValidToken .white C r :=
      (q20305resp%
        "splWhiteSemanticValid_of_clear")
        p.2 C r t
        hp.2.2.1 hCtok hr0

    have hclearId :
        (sourceClear .white p.1).id =
          (C e).id := by
      calc
        (sourceClear .white p.1).id =
            p.1.id :=
          (q20305resp%
            "splWhiteSemanticSourceClear_id")
            .white p.1
        _ = (C e).id := hp.2.1

    rcases hmove with hclosed | hopen
    · rcases hclosed with
        ⟨hgate, hir, hq⟩
      subst i
      have hgate' :
          ¬ ((sourceClear .white p.1).last = false ∧
              (sourceClear .white p.2).last = false) := by
        simpa [p, pre, r] using hgate
      have hq' :
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).2 =
            some t' := by
        simpa [p, pre, r] using hq
      have htt :
          t' = t :=
        (q20305resp%
          "splWhiteSemanticClosedRight_same")
          hpsi p.1 p.2 t t'
          hr0 hgate' hq'
      have hpostT :
          tokenAt .white (D r) =
            some t := by
        rw [← htt]
        exact hpost
      have hworkPre :
          WorkingFor ring root C r .white seg.val :=
        (q20305resp%
          "splWhiteSemanticWorking_same_backward")
          ring root C D r .white seg.val t
          hCtok hpostT hVW.2
      have hcorrPre :
          CorrectToken ring root C r .white seg.val :=
        hpreR
          ⟨hvalidPre, hworkPre⟩
      subst t'
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg C D
          r .white t
          hCtok hpost hsrc hcorrPre

    · rcases hopen with ⟨hgate, hwhere⟩
      have hgate' :
          (sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false := by
        simpa [p, pre, r] using hgate
      rcases hwhere with houtLeft | houtRight

      · rcases houtLeft with ⟨hie, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).1 =
              some t' := by
          simpa [p, pre, r] using hq
        have hcases :=
          (q20305resp%
            "splWhiteSemanticResponderMoved_shape")
            hpsi ring e p.1 p.2
            t t' hgate' hr0 hq'
        rcases hcases with hord | hturn

        · rcases hord with
            ⟨holdNeg, hnewNeg,
              htarget, hbit, hcarry⟩
          have hworkPre :
              WorkingFor ring root C r .white seg.val :=
            (q20305resp%
              "splWhiteSemanticWorkingNegative_backward")
              ring root C D
              r e .white seg.val t t'
              hCtok hpost
              holdNeg hnewNeg htarget
              hVW.2
          have hcorrPre :
              CorrectToken ring root C r .white seg.val :=
            hpreR
              ⟨hvalidPre, hworkPre⟩
          exact
            (q20305route%
              "splWhiteSeamNegativeCorrect")
              ring root seg C D r e t t'
              hCtok hpost
              holdNeg hnewNeg htarget
              hbit hcarry hsrc hcorrPre

        · rcases hturn with ⟨hcneg, hval0⟩
          have hval :
              t' =
                PPL.remark2NegTurnValue
                  hpsi (C e).id t := by
            rw [← hclearId]
            exact hval0
          have hpostTurn :
              tokenAt .white (D e) =
                some
                  (PPL.remark2NegTurnValue
                    hpsi (C e).id t) := by
            rw [← hval]
            exact hpost
          have hworkPre :
              WorkingFor ring root C r .white seg.val :=
            (q20305resp%
              "splWhiteSemanticNegTurn_working_backward")
              hpsi ring root C D e seg t
              hCtok hcneg hpostTurn hVW.2
          have hcorrPre :
              CorrectToken ring root C r .white seg.val :=
            hpreR
              ⟨hvalidPre, hworkPre⟩
          have hpostNext :
              tokenAt .white (D e) =
                some
                  (PPL.remark2NegTurnNext
                    hpsi (C e).id t) := by
            rw [← PPL.remark2NegTurnValue_eq_next]
            exact hpostTurn
          exact
            (q20305w% "q20299NegTurnCorrect")
              hpsi hn3 ring root seg
              C D e r .white t
              (by rfl) hCtok hcneg
              hpostNext hworkPre hcorrPre hsrc

      · rcases houtRight with ⟨hir, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).2 =
              some t' := by
          simpa [p, pre, r] using hq
        have htt :
            t' = t :=
          (q20305resp%
            "splWhiteSemanticOpenRight_same")
            hpsi p.1 p.2 t t'
            hgate' hr0 hq'
        have hpostT :
            tokenAt .white (D r) =
              some t := by
          rw [← htt]
          exact hpost
        have hworkPre :
            WorkingFor ring root C r .white seg.val :=
          (q20305resp%
            "splWhiteSemanticWorking_same_backward")
            ring root C D r .white seg.val t
            hCtok hpostT hVW.2
        have hcorrPre :
            CorrectToken ring root C r .white seg.val :=
          hpreR
            ⟨hvalidPre, hworkPre⟩
        subst t'
        exact
          PPL.remark2Right_correct_same_occurrence
            ring root seg C D
            r .white t
            hCtok hpost hsrc hcorrPre

  · rcases hoff with
      ⟨hji, hie, hir, _htt⟩
    subst j
    rcases hi with hieq | hireq
    · exact False.elim (hie hieq)
    · exact False.elim (hir hireq)


/-- The white selected-site token half, `L18PrimeSelectedWhiteTokenHalfFrame`.
Mirror of `l18PrimeStepSelectedTokenHalfBlack`. -/
theorem l18PrimeSelectedWhiteTokenHalfFrame_proved :
    L18PrimeSelectedWhiteTokenHalfFrame := by
  intro n psi kappa hn3 hpsi ring root b C e hb hPrefix s hs hTok
  intro i hi hVW
  let seg' : Fin (segmentCount n psi - 2) :=
    ⟨s, by unfold l18BlockCount at hb; omega⟩
  have hsrc :
      sourceIota ring root C s =
        sourceIota ring root (pprimeStep ring C e) s :=
    (q20305ids% "q20256SourceIotaProtected")
      hn3 hpsi ring root b C e hb hPrefix s hs
  have hCDL : CDLAt ring root C := hPrefix.1
  have hPostCDL : CDLAt ring root (pprimeStep ring C e) :=
    (q20305w% "q20299PostCDL")
      hn3 hpsi ring root b C e hb hPrefix
  cases ht : tokenAt .white ((pprimeStep ring C e) i) with
  | none =>
      have hv := hVW.1
      unfold ValidToken at hv
      rw [ht] at hv
      exact False.elim hv
  | some t' =>
      have hprov :=
        l18PrimeSelectedPostTokenProvenance
          hn3 hpsi ring root C e hCDL
          i hi .white t' ht
      rcases hprov with hOld | hFresh
      · exact
          q20305OldCorrectTokWhite
            hn3 hpsi ring root
            C (pprimeStep ring C e) e
            seg' hCDL hPostCDL
            (hTok e) (hTok (ring.rightNeighbor e))
            (by simpa [seg'] using hsrc)
            i hi t' ht hOld
            (by simpa [seg'] using hVW)
      · exact
          (q20305w% "q20299FreshCorrect")
            hn3 hpsi ring root
            C (pprimeStep ring C e) e
            seg' hCDL
            (by simpa [seg'] using hsrc)
            i t' ht hFresh
            (by simpa [seg'] using hVW)

/-- Establishment cut, token half, with the white input discharged: only the
half-word token row `L18PrimeHalfWordTokenHalfRow` remains. -/
theorem l18PrimeLemma4EstablishmentTokensAtCut_of_halfRow
    (hHalf : L18PrimeHalfWordTokenHalfRow)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hsub :
      (PPL.lemma4Word ring
        (shiftRight ring root (b * psi)) psi).Sublist cut) :
    let E := runPPrime ring C cut
    l18HitsSPL ring root C cut = true ∨
      ∀ i : Fin n,
        ((ValidToken .black E i ∧ WorkingFor ring root E i .black b) →
            CorrectToken ring root E i .black b) ∧
          ((ValidToken .white E i ∧ WorkingFor ring root E i .white b) →
            CorrectToken ring root E i .white b) :=
  l18PrimeLemma4EstablishmentTokensAtCut
    l18PrimeSelectedWhiteTokenHalfFrame_proved hHalf
    hn3 hpsi ring root b C cut hb hPrefix hsub

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q20305OldCorrectTokWhite
#print axioms PPL.Convergence.L18.l18PrimeSelectedWhiteTokenHalfFrame_proved
#print axioms PPL.Convergence.L18.l18PrimeLemma4EstablishmentTokensAtCut_of_halfRow
