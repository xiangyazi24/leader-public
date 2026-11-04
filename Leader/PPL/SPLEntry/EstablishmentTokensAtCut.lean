import Leader.PPL.SPLEntry.PairRowAssembly
import Leader.PPL.TokenCompletion.HalfPowerReduction
import Init.Data.List.Sublist
import Init.Omega

/-!
# L18 prime establishment cut: the token half

Target: `l18PrimeLemma4EstablishmentTokensAtCut`.  Under `L18BuildPrefixAt
ring root b C` and block `b`'s `lemma4Word` as a sublist of `cut`, with
`E := runPPrime ring C cut`, either the cut hits `S_PL` or every valid token
working for pair `b` at `E` is correct (both colours).

`hminimal` of the earlier formulation is NOT needed for the token half and is dropped:
the token half, once true, is preserved by every later prime letter
(`l18PrimeStepTokenHalf`), so any cut containing the word works.

Structure:

1. `q20303OldCorrectTok`: the black old-image transport of the landed
   established-pair theorem, with its pre-hypothesis weakened from
   `L18BuildPairOK` (ID + tokens) to the black token implication at the two
   interacting sites.  The ID half of the pair is never used.
2. `l18PrimeStepSelectedTokenHalfBlack`: one prime letter preserves the black
   token half of any pair `s ≤ b` at the two selected sites, from the token
   half alone (source frame `q20256SourceIotaProtected` covers `s = b`).
3. `l18PrimeStepTokenHalf` / `l18PrimeRunTokenHalf`: the token half of pair
   `b` survives every prime letter / schedule from `Prefix b`, given the white
   selected sibling `L18PrimeSelectedWhiteTokenHalfFrame` (explicit input).
4. `l18PrimeLemma4EstablishmentTokensAtCut`: the target, from (3) and the
   explicit input `L18PrimeHalfWordTokenHalfRow` (the token half after the
   first-half purge `H^psi`), via `lemma4Word = H^psi ++ H^psi`.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option linter.unusedVariables false

open PPL
open PPL.Safety.SPL

open Lean Elab Term Meta in
elab "q20303blk% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairSelectedBlack).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20303ids% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairIds).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20303route% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairStepRoute).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20303gap% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuildGappedAssembly).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

/-- The token half of `L18BuildPairOK ring root C seg` (its second field). -/
def L18TokenHalfAt
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (seg : Nat) : Prop :=
  ∀ i : Fin n,
    ((ValidToken .black C i ∧ WorkingFor ring root C i .black seg) →
        CorrectToken ring root C i .black seg) ∧
      ((ValidToken .white C i ∧ WorkingFor ring root C i .white seg) →
        CorrectToken ring root C i .white seg)

/-! ## 1. Black old-image transport from the token half only -/

/-- Copy of the private `q20293OldCorrect` (L18PrimeBuiltPairSelectedBlack)
whose pre-hypothesis is only the black token implication at the two
interacting sites instead of the whole `L18BuildPairOK`; the original proof
reads only those two implications of the pair (never its ID equation). -/
theorem q20303OldCorrectTok
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
      (ValidToken .black C e ∧
          WorkingFor ring root C e .black seg.val) →
        CorrectToken ring root C e .black seg.val)
    (hpreR :
      (ValidToken .black C (ring.rightNeighbor e) ∧
          WorkingFor ring root C (ring.rightNeighbor e) .black seg.val) →
        CorrectToken ring root C (ring.rightNeighbor e) .black seg.val)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root D seg.val)
    (i : Fin n)
    (hi : i = e ∨ i = ring.rightNeighbor e)
    (t' : TokenData psi)
    (hpost :
      tokenAt .black (D i) = some t')
    (hOld :
      SPLPostTokenOldImage
        hpsi ring C e i .black t')
    (hVW :
      ValidToken .black D i ∧
        WorkingFor ring root D
          i .black seg.val) :
    CorrectToken ring root D i .black seg.val := by
  replace hOld :=
    (q20303blk% "q20293OldImageBlack") hpsi ring C e i t' hOld
  dsimp only at hOld
  rcases hOld with
    ⟨j, t, _hwhere, hCtok, hshape⟩

  let r := ring.rightNeighbor e
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)

  have hp0 :=
    (q20303blk% "q20293PreFrame")
      hpsi ring root C e hCDL
  have hp :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        p.2.dist = (C r).dist ∧
        tokenAt .black p.1 =
          tokenAt .black (C e) ∧
        tokenAt .black p.2 =
          tokenAt .black (C r) := by
    simpa [p, r] using hp0

  rcases hshape with hleft | hright | hoff
  · rcases hleft with
      ⟨hje, hl0tok, hmove⟩
    subst j

    have hl0 :
        tokenAt .black
            (sourceClear .black p.1) =
          some t := by
      simpa [p, r] using hl0tok
    have hvalidPre :
        ValidToken .black C e :=
      (q20293init% "q20253ValidOfCleared")
        .black C e p.1 t
        hp.1 hCtok hl0

    rcases hmove with hclosed | hopen
    · rcases hclosed with
        ⟨hgate, hie, hq⟩
      subst i
      have hgate' :
          ¬ ((sourceClear .black p.1).last = false ∧
              (sourceClear .black p.2).last = false) := by
        simpa [p, r] using hgate
      have hq' :
          tokenAt .black
              (moveToken hpsi .black p.1 p.2).1 =
            some t' := by
        simpa [p, r] using hq
      have htt :
          t' = t :=
        (q20293branch% "splBlackOldClosedLeft_same")
          hpsi .black p.1 p.2
          t t' hl0 hgate' hq'
      subst t'
      have hworkPre :
          WorkingFor ring root C e .black seg.val :=
        (q20293resp%
          "splBlackSemanticWorking_same_backward")
          ring root C D e .black seg.val t
          hCtok hpost hVW.2
      have hcorrPre :
          CorrectToken ring root C e .black seg.val :=
        hpreE
          ⟨hvalidPre, hworkPre⟩
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg C D
          e .black t
          hCtok hpost hsrc hcorrPre

    · rcases hopen with
        ⟨hgate, hrnone, hwhere⟩
      have hgate' :
          (sourceClear .black p.1).last = false ∧
            (sourceClear .black p.2).last = false := by
        simpa [p, r] using hgate
      have hrnone' :
          tokenAt .black
              (sourceClear .black p.2) =
            none := by
        simpa [p, r] using hrnone
      rcases hwhere with houtLeft | houtRight
      · rcases houtLeft with ⟨hie, hq⟩
        subst i
        have hq' :
            tokenAt .black
                (moveToken hpsi .black p.1 p.2).1 =
              some t' := by
          simpa [p, r] using hq
        have htt :
            t' = t :=
          (q20293branch% "splBlackOldOpenLeft_same")
            hpsi .black p.1 p.2
            t t' hgate' hl0 hrnone' hq'
        subst t'
        have hworkPre :
            WorkingFor ring root C e .black seg.val :=
          (q20293resp%
            "splBlackSemanticWorking_same_backward")
            ring root C D e .black seg.val t
            hCtok hpost hVW.2
        have hcorrPre :
            CorrectToken ring root C e .black seg.val :=
          hpreE
            ⟨hvalidPre, hworkPre⟩
        exact
          PPL.remark2Right_correct_same_occurrence
            ring root seg C D
            e .black t
            hCtok hpost hsrc hcorrPre

      · rcases houtRight with ⟨hir, hq⟩
        subst i
        have hq' :
            tokenAt .black
                (moveToken hpsi .black p.1 p.2).2 =
              some t' := by
          simpa [p, r] using hq
        have hliteral :
            PPL.Remark2RightLiteralMotionData
              hpsi ring e r t t' := by
          simpa [r] using
            (q20293init% "q20253LiteralMotion")
              hpsi ring e p.1 p.2
              t t' hgate' hl0 hrnone' hq'

        have hworkPre :
            WorkingFor ring root C e .black seg.val := by
          have hm := hliteral
          unfold PPL.Remark2RightLiteralMotionData at hm
          rcases hm.2.2 with hord | hturn
          · exact
              (q20293init%
                "q20253OrdinaryWorkingBackward")
                ring root C D e seg t t'
                hCtok hpost
                hord.1 hord.2.1
                (by simpa [r] using hord.2.2)
                hVW.2
          · exact
              (q20303blk% "q20293TurnWorkingBackward")
                hpsi ring root C D e seg
                t t' hPostCDL
                hCtok hturn.1 hpost hturn.2
                hVW.1 hVW.2

        have hcorrPre :
            CorrectToken ring root C e .black seg.val :=
          hpreE
            ⟨hvalidPre, hworkPre⟩

        have hmotion :
            PPL.Remark2RightMotionData
              ring root seg.val e r t t' :=
          PPL.remark2RightLiteralMotionData_to_motion
            hpsi ring root seg C D
            e r .black t t'
            hCtok hpost
            hvalidPre hworkPre hcorrPre
            hCDL hPostCDL hsrc
            (by rfl) hliteral

        exact
          PPL.remark2Right_motion_preserves_correct
            ring root seg C D
            e r .black t t'
            hCtok hpost hsrc
            hcorrPre hmotion

  · rcases hright with
      ⟨hjr, hr0tok, hmove⟩
    subst j

    have hr0 :
        tokenAt .black
            (sourceClear .black p.2) =
          some t := by
      simpa [p, r] using hr0tok
    have hvalidPre :
        ValidToken .black C r :=
      (q20293resp%
        "splBlackSemanticValid_of_clear")
        p.2 C r t
        hp.2.2.1 hCtok hr0

    have hclearId :
        (sourceClear .black p.1).id =
          (C e).id := by
      calc
        (sourceClear .black p.1).id =
            p.1.id :=
          (q20293resp%
            "splBlackSemanticSourceClear_id")
            .black p.1
        _ = (C e).id := hp.2.1

    rcases hmove with hclosed | hopen
    · rcases hclosed with
        ⟨hgate, hir, hq⟩
      subst i
      have hgate' :
          ¬ ((sourceClear .black p.1).last = false ∧
              (sourceClear .black p.2).last = false) := by
        simpa [p, r] using hgate
      have hq' :
          tokenAt .black
              (moveToken hpsi .black p.1 p.2).2 =
            some t' := by
        simpa [p, r] using hq
      have htt :
          t' = t :=
        (q20293resp%
          "splBlackSemanticClosedRight_same")
          hpsi p.1 p.2 t t'
          hr0 hgate' hq'
      have hpostT :
          tokenAt .black (D r) =
            some t := by
        rw [← htt]
        exact hpost
      have hworkPre :
          WorkingFor ring root C r .black seg.val :=
        (q20293resp%
          "splBlackSemanticWorking_same_backward")
          ring root C D r .black seg.val t
          hCtok hpostT hVW.2
      have hcorrPre :
          CorrectToken ring root C r .black seg.val :=
        hpreR
          ⟨hvalidPre, hworkPre⟩
      subst t'
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg C D
          r .black t
          hCtok hpost hsrc hcorrPre

    · rcases hopen with ⟨hgate, hwhere⟩
      have hgate' :
          (sourceClear .black p.1).last = false ∧
            (sourceClear .black p.2).last = false := by
        simpa [p, r] using hgate
      rcases hwhere with houtLeft | houtRight
      · rcases houtLeft with ⟨hie, hq⟩
        subst i
        have hq' :
            tokenAt .black
                (moveToken hpsi .black p.1 p.2).1 =
              some t' := by
          simpa [p, r] using hq
        have hcases :=
          (q20293resp%
            "splBlackSemanticResponderMoved_shape")
            hpsi ring e p.1 p.2
            t t' hgate' hr0 hq'
        rcases hcases with hord | hturn
        · rcases hord with
            ⟨holdNeg, hnewNeg,
              htarget, hbit, hcarry⟩
          have hworkPre :
              WorkingFor ring root C r .black seg.val :=
            (q20293resp%
              "splBlackSemanticWorkingNegative_backward")
              ring root C D
              r e .black seg.val t t'
              hCtok hpost
              holdNeg hnewNeg htarget
              hVW.2
          have hcorrPre :
              CorrectToken ring root C r .black seg.val :=
            hpreR
              ⟨hvalidPre, hworkPre⟩
          exact
            (q20293seam%
              "splBlackSeamNegativeCorrect")
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
              tokenAt .black (D e) =
                some
                  (PPL.remark2NegTurnValue
                    hpsi (C e).id t) := by
            rw [← hval]
            exact hpost
          have hworkPre :
              WorkingFor ring root C r .black seg.val :=
            (q20293resp%
              "splBlackSemanticNegTurn_working_backward")
              hpsi ring root C D e seg t
              hCtok hcneg hpostTurn hVW.2
          have hcorrPre :
              CorrectToken ring root C r .black seg.val :=
            hpreR
              ⟨hvalidPre, hworkPre⟩
          have hpostNext :
              tokenAt .black (D e) =
                some
                  (PPL.remark2NegTurnNext
                    hpsi (C e).id t) := by
            rw [← PPL.remark2NegTurnValue_eq_next]
            exact hpostTurn
          exact
            (q20303blk% "q20293NegTurnCorrect")
              hpsi hn3 ring root seg
              C D e r .black t
              (by rfl) hCtok hcneg
              hpostNext hworkPre hcorrPre hsrc

      · rcases houtRight with ⟨hir, hq⟩
        subst i
        have hq' :
            tokenAt .black
                (moveToken hpsi .black p.1 p.2).2 =
              some t' := by
          simpa [p, r] using hq
        have htt :
            t' = t :=
          (q20293resp%
            "splBlackSemanticOpenRight_same")
            hpsi p.1 p.2 t t'
            hgate' hr0 hq'
        have hpostT :
            tokenAt .black (D r) =
              some t := by
          rw [← htt]
          exact hpost
        have hworkPre :
            WorkingFor ring root C r .black seg.val :=
          (q20293resp%
            "splBlackSemanticWorking_same_backward")
            ring root C D r .black seg.val t
            hCtok hpostT hVW.2
        have hcorrPre :
            CorrectToken ring root C r .black seg.val :=
          hpreR
            ⟨hvalidPre, hworkPre⟩
        subst t'
        exact
          PPL.remark2Right_correct_same_occurrence
            ring root seg C D
            r .black t
            hCtok hpost hsrc hcorrPre

  · rcases hoff with
      ⟨hji, hie, hir, _htt⟩
    subst j
    rcases hi with hieq | hireq
    · exact False.elim (hie hieq)
    · exact False.elim (hir hireq)



/-! ## 2. Black selected sites, from the token half -/

/-- One prime letter preserves the black token implication of pair `s ≤ b`
at the two interacting sites, assuming only the black token implication of
pair `s` at the pre-state (no ID equation for pair `s`). -/
theorem l18PrimeStepSelectedTokenHalfBlack
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (s : Nat)
    (hs : s ≤ b)
    (hTok :
      ∀ j : Fin n,
        (ValidToken .black C j ∧ WorkingFor ring root C j .black s) →
          CorrectToken ring root C j .black s) :
    ∀ i : Fin n,
      (i = e ∨ i = ring.rightNeighbor e) →
      (ValidToken .black (pprimeStep ring C e) i ∧
        WorkingFor ring root (pprimeStep ring C e) i .black s) →
      CorrectToken ring root (pprimeStep ring C e) i .black s := by
  intro i hi hVW
  let seg' : Fin (segmentCount n psi - 2) :=
    ⟨s, by unfold l18BlockCount at hb; omega⟩
  have hsrc :
      sourceIota ring root C s =
        sourceIota ring root (pprimeStep ring C e) s :=
    (q20303ids% "q20256SourceIotaProtected")
      hn3 hpsi ring root b C e hb hPrefix s hs
  have hCDL : CDLAt ring root C := hPrefix.1
  have hPostCDL : CDLAt ring root (pprimeStep ring C e) :=
    (q20303blk% "q20293PostCDL")
      hn3 hpsi ring root b C e hb hPrefix
  cases ht : tokenAt .black ((pprimeStep ring C e) i) with
  | none =>
      have hv := hVW.1
      unfold ValidToken at hv
      rw [ht] at hv
      exact False.elim hv
  | some t' =>
      have hprov :=
        l18PrimeSelectedPostTokenProvenance
          hn3 hpsi ring root C e hCDL
          i hi .black t' ht
      rcases hprov with hOld | hFresh
      · exact
          q20303OldCorrectTok
            hn3 hpsi ring root
            C (pprimeStep ring C e) e
            seg' hCDL hPostCDL
            (hTok e) (hTok (ring.rightNeighbor e))
            (by simpa [seg'] using hsrc)
            i hi t' ht hOld
            (by simpa [seg'] using hVW)
      · exact
          (q20303blk% "q20293FreshCorrect")
            hn3 hpsi ring root
            C (pprimeStep ring C e) e
            seg' hCDL
            (by simpa [seg'] using hsrc)
            i t' ht hFresh
            (by simpa [seg'] using hVW)

/-! ## 3. The white sibling (explicit input) and the token-half frame -/

/-- White sibling of `l18PrimeStepSelectedTokenHalfBlack`, same hypotheses.
Explicit input (not proved here).  It implies the assembly's
`L18PrimeSelectedWhiteFrame` (`l18PrimeSelectedWhiteFrame_of_tokenHalf`). -/
def L18PrimeSelectedWhiteTokenHalfFrame : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (s : Nat)
    (hs : s ≤ b)
    (hTok :
      ∀ j : Fin n,
        (ValidToken .white C j ∧ WorkingFor ring root C j .white s) →
          CorrectToken ring root C j .white s),
    ∀ i : Fin n,
      (i = e ∨ i = ring.rightNeighbor e) →
      (ValidToken .white (pprimeStep ring C e) i ∧
        WorkingFor ring root (pprimeStep ring C e) i .white s) →
      CorrectToken ring root (pprimeStep ring C e) i .white s

theorem l18PrimeSelectedWhiteFrame_of_tokenHalf
    (hW : L18PrimeSelectedWhiteTokenHalfFrame) :
    L18PrimeSelectedWhiteFrame := by
  intro n psi kappa hn3 hpsi ring root b C e hb hPrefix hIds seg hseg i hi hVW
  exact
    hW hn3 hpsi ring root b C e hb hPrefix seg.val (Nat.le_of_lt hseg)
      (fun j => ((hPrefix.2.2 seg hseg).2 j).2) i hi hVW

/-- One prime letter preserves the token half of pair `b` from `Prefix b`. -/
theorem l18PrimeStepTokenHalf
    (hW : L18PrimeSelectedWhiteTokenHalfFrame)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hT : L18TokenHalfAt ring root C b) :
    L18TokenHalfAt ring root (pprimeStep ring C e) b := by
  intro i
  by_cases hsel : i = e ∨ i = ring.rightNeighbor e
  · exact
      ⟨l18PrimeStepSelectedTokenHalfBlack hn3 hpsi ring root b C e hb hPrefix
          b (Nat.le_refl b) (fun j => (hT j).1) i hsel,
        hW hn3 hpsi ring root b C e hb hPrefix
          b (Nat.le_refl b) (fun j => (hT j).2) i hsel⟩
  · have hie : i ≠ e := fun h => hsel (Or.inl h)
    have hir : i ≠ ring.rightNeighbor e := fun h => hsel (Or.inr h)
    have hsrc :
        sourceIota ring root C b =
          sourceIota ring root (pprimeStep ring C e) b :=
      (q20303ids% "q20256SourceIotaProtected")
        hn3 hpsi ring root b C e hb hPrefix b (Nat.le_refl b)
    exact
      ⟨(q20303route% "q20252_offPairCorrect")
          ring root C e i ⟨b, hb⟩ .black hie hir hsrc (hT i).1,
        (q20303route% "q20252_offPairCorrect")
          ring root C e i ⟨b, hb⟩ .white hie hir hsrc (hT i).2⟩

/-- The token half of pair `b` survives any prime schedule from `Prefix b`. -/
theorem l18PrimeRunTokenHalf
    (hW : L18PrimeSelectedWhiteTokenHalfFrame)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi) :
    ∀ (C : Config n psi kappa) (schedule : DetSchedule n),
      L18BuildPrefixAt ring root b C →
      L18TokenHalfAt ring root C b →
      L18TokenHalfAt ring root (runPPrime ring C schedule) b := by
  intro C schedule
  induction schedule generalizing C with
  | nil =>
      intro _ hT
      exact hT
  | cons e rest ih =>
      intro hPrefix hT
      exact
        ih (pprimeStep ring C e)
          (l18PrimeStepPreservesBuildPrefix_of_white
            (l18PrimeSelectedWhiteFrame_of_tokenHalf hW)
            hn3 hpsi ring root b C e hb hPrefix)
          (l18PrimeStepTokenHalf hW hn3 hpsi ring root b C e hb hPrefix hT)

/-! ## 4. The establishment cut, token half -/

/-- Explicit input: the token half of pair `b` after the first-half purge.
From `Prefix b`, along any prime schedule containing block `b`'s half word
`H^psi`, either `S_PL` is hit or every valid token working for pair `b` is
correct.  Paper content: `H^psi` purges every start-old selected-colour
lineage in the window (`halfPowerFirstPowerInduction_proved`), and every
lineage born at the border reads the frozen source `S_b` and is transported
correctly (fresh-birth rows + Remark 2). -/
def L18PrimeHalfWordTokenHalfRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (pre : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hsub :
      (PPL.lemma4HalfWord ring
        (shiftRight ring root (b * psi)) psi).Sublist pre),
    l18HitsSPL ring root C pre = true ∨
      L18TokenHalfAt ring root (runPPrime ring C pre) b

/-- Establishment cut, token half, without `hminimal`. -/
theorem l18PrimeLemma4EstablishmentTokensAtCut
    (hW : L18PrimeSelectedWhiteTokenHalfFrame)
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
            CorrectToken ring root E i .white b) := by
  intro E
  rw [PPL.lemma4Word_eq_two_halves] at hsub
  obtain ⟨pre, rest, hcut, hpre, _hrest⟩ := List.append_sublist_iff.1 hsub
  subst hcut
  rcases hHalf hn3 hpsi ring root b C pre hb hPrefix hpre with hhit | hT
  · exact Or.inl
      ((q20303gap% "l18HitsSPL_append_left_true") ring root C pre rest hhit)
  · right
    have hPre : L18BuildPrefixAt ring root b (runPPrime ring C pre) :=
      l18PrimeRunPreservesBuildPrefix_of_white
        (l18PrimeSelectedWhiteFrame_of_tokenHalf hW)
        hn3 hpsi ring root b C pre hb hPrefix
    have h := l18PrimeRunTokenHalf hW hn3 hpsi ring root b hb
      (runPPrime ring C pre) rest hPre hT
    show L18TokenHalfAt ring root (runPPrime ring C (pre ++ rest)) b
    rw [runPPrime_append]
    exact h

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q20303OldCorrectTok
#print axioms PPL.Convergence.L18.l18PrimeStepSelectedTokenHalfBlack
#print axioms PPL.Convergence.L18.l18PrimeRunTokenHalf
#print axioms PPL.Convergence.L18.l18PrimeLemma4EstablishmentTokensAtCut
