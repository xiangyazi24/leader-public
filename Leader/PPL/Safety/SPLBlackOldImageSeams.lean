import Leader.PPL.Safety.SPLBlackOldImageBranches
import Leader.PPL.Safety.PeacefulScan
import Leader.PPL.TokenCorrectness.PersistenceLeftRow

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

private theorem splBlackSeamSourceIota
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hSPL : SPLAt ring root C)
    (seg : Nat) :
    sourceIota ring root C seg =
      sourceIota ring root
        (nextConfig ring C e) seg := by
  have hf :=
    splAlgorithm23FieldFrameResidual_proved
      hn3 hpsi ring root C e hSPL
  dsimp only at hf
  funext x
  unfold sourceIota
  exact
    (hf.2.2.2
      (shiftRight ring
        (sourceStart psi ring root seg)
        x.val)).symm

private theorem splBlackSeamPostCDL
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hSPL : SPLAt ring root C) :
    CDLAt ring root (nextConfig ring C e) := by
  have hcpb :
      CPB ring (nextConfig ring C e) := by
    simpa [nextConfig] using
      (PPL.Safety.PeacefulProps.cpb_step_closed_proved
        hn3 hpsi ring C e hSPL.1.1)
  have hleader :=
    splAlgorithm23_leader_of_field
      splAlgorithm23FieldFrameResidual_proved
      hn3 hpsi ring root C e hSPL
  have hgeom :=
    splAlgorithm23_geometry_of_field
      splAlgorithm23FieldFrameResidual_proved
      hn3 hpsi ring root C e hSPL
  dsimp only at hleader hgeom
  exact ⟨hcpb, hleader, hgeom⟩

private theorem splBlackSeamNegativeCorrect
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (i j : Fin n)
    (t t' : TokenData psi)
    (ht : tokenAt .black (C i) = some t)
    (ht' : tokenAt .black (C' j) = some t')
    (hcOld : decodeOffset psi (tokenCode t) < 0)
    (hcNew : decodeOffset psi (tokenCode t') < 0)
    (htarget :
      tokenTargetSite ring j t' =
        tokenTargetSite ring i t)
    (hbit :
      tokenBitBool t' = tokenBitBool t)
    (hcarry :
      tokenCarryBool t' = tokenCarryBool t)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hcorr :
      CorrectToken ring root C i .black seg.val) :
    CorrectToken ring root C' j .black seg.val := by
  unfold CorrectToken at hcorr ⊢
  rw [ht] at hcorr
  rw [ht']
  dsimp only at hcorr ⊢
  have holdNot :
      Not (0 < decodeOffset psi (tokenCode t)) := by
    omega
  have hnewNot :
      Not (0 < decodeOffset psi (tokenCode t')) := by
    omega
  rw [if_neg holdNot] at hcorr
  rw [if_neg hnewNot]
  rw [htarget]
  rcases hcorr with
    ⟨hparity, _hold, hrel, hx, hpay⟩
  exact
    ⟨hparity, hcNew, hrel, hx,
      PPL.remark2Right_payloadCorrect_transport
        ring root C C' seg.val
        _ hx t t' hbit hcarry hsrc hpay⟩

/--
Exact remaining right-seam bridge.

The landed right mirror is supplied explicitly.  The row contains no
CorrectToken conclusion: it only recovers the pre-step valid/working facts and
the literal right-motion certificate from the already-selected physical
branch.
-/
def SPLBlackOldImageInitiatorMovedRightSemanticRow : Prop :=
  PPL.Remark2RightSelectedMirrorRowCorrected ->
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair
          hpsi (C e) (C rsite)
      let l0 := sourceClear .black p.1
      let r0 := sourceClear .black p.2
      let q := moveToken hpsi .black p.1 p.2
      let gate :=
        l0.last = false /\ r0.last = false
      tokenAt .black (C e) = some t ->
      tokenAt .black l0 = some t ->
      gate ->
      tokenAt .black r0 = none ->
      tokenAt .black q.2 = some t' ->
      tokenAt .black
          (nextConfig ring C e rsite) = some t' ->
      (ValidToken .black
          (nextConfig ring C e) rsite
        /\ WorkingFor ring root
          (nextConfig ring C e)
          rsite .black seg.val) ->
      ValidToken .black C e
        /\ WorkingFor ring root C e .black seg.val
        /\ PPL.Remark2RightLiteralMotionData
          hpsi ring e rsite t t'

theorem splBlackOldImageInitiatorMovedRightBranch_of_semantic
    (hsem : SPLBlackOldImageInitiatorMovedRightSemanticRow) :
    SPLBlackOldImageInitiatorMovedRightBranch := by
  unfold SPLBlackOldImageInitiatorMovedRightSemanticRow at hsem
  unfold SPLBlackOldImageInitiatorMovedRightBranch
  intro _hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg t t'
  dsimp only
  intro hCtok hl0tok hgate hrnone hq hpost hVW

  have hs :=
    hsem PPL.remark2RightSelectedMirrorRowCorrected_proved
      hn3 hpsi ring root C e hSPL
      seg t t'
      hCtok hl0tok hgate hrnone hq hpost hVW
  rcases hs with ⟨hvalid, hwork, hliteral⟩

  have hcorr :
      CorrectToken ring root C e .black seg.val :=
    ((hSPL.2.2 seg).2 e).1 ⟨hvalid, hwork⟩
  have hsrc :=
    splBlackSeamSourceIota
      hn3 hpsi ring root C e hSPL seg.val
  have hpostCDL :=
    splBlackSeamPostCDL
      hn3 hpsi ring root C e hSPL

  have hmotion :
      PPL.Remark2RightMotionData
        ring root seg.val
        e (ring.rightNeighbor e) t t' :=
    PPL.remark2RightLiteralMotionData_to_motion
      hpsi ring root seg
      C (nextConfig ring C e)
      e (ring.rightNeighbor e)
      .black t t'
      hCtok hpost
      hvalid hwork hcorr
      hSPL.1 hpostCDL hsrc
      rfl hliteral

  exact
    PPL.remark2Right_motion_preserves_correct
      ring root seg
      C (nextConfig ring C e)
      e (ring.rightNeighbor e)
      .black t t'
      hCtok hpost hsrc hcorr hmotion

/--
Exact remaining left-seam bridge.

The landed left mirror is supplied explicitly.  It must recover the old
responder's pre-step valid/working facts and classify the surviving physical
old image as stay, ordinary negative move, or the exact c=-1 turn.
-/
def SPLBlackOldImageResponderSemanticRow : Prop :=
  PPL.Remark2LeftSelectedMirrorRow ->
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair
          hpsi (C e) (C rsite)
      let r0 := sourceClear .black p.2
      let q := moveToken hpsi .black p.1 p.2
      let gate :=
        (sourceClear .black p.1).last = false
          /\ r0.last = false
      tokenAt .black (C rsite) = some t ->
      tokenAt .black r0 = some t ->
      ((Not gate
          /\ i = rsite
          /\ tokenAt .black q.2 = some t')
        \/ (gate
          /\ ((i = e
              /\ tokenAt .black q.1 = some t')
            \/ (i = rsite
              /\ tokenAt .black q.2 = some t')))) ->
      tokenAt .black
          (nextConfig ring C e i) = some t' ->
      (ValidToken .black
          (nextConfig ring C e) i
        /\ WorkingFor ring root
          (nextConfig ring C e)
          i .black seg.val) ->
      ValidToken .black C rsite
        /\ WorkingFor ring root C rsite .black seg.val
        /\ ((i = rsite /\ t' = t)
          \/ (i = e
            /\ decodeOffset psi (tokenCode t) < 0
            /\ decodeOffset psi (tokenCode t') < 0
            /\ tokenTargetSite ring e t' =
              tokenTargetSite ring rsite t
            /\ tokenBitBool t' = tokenBitBool t
            /\ tokenCarryBool t' = tokenCarryBool t)
          \/ (i = e
            /\ decodeOffset psi (tokenCode t) = -1
            /\ t' =
              PPL.remark2NegTurnValue
                hpsi (C e).id t))

theorem splBlackOldImageResponderBranch_of_semantic
    (hsem : SPLBlackOldImageResponderSemanticRow) :
    SPLBlackOldImageResponderBranch := by
  unfold SPLBlackOldImageResponderSemanticRow at hsem
  unfold SPLBlackOldImageResponderBranch
  intro _hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t t'
  dsimp only
  intro hCtok hr0tok hshape hpost hVW

  have hs :=
    hsem PPL.remark2LeftSelectedMirrorRow_proved
      hn3 hpsi ring root C e hSPL
      seg i t t'
      hCtok hr0tok hshape hpost hVW
  rcases hs with ⟨hvalid, hwork, hcases⟩

  let rsite := ring.rightNeighbor e
  have hcorr :
      CorrectToken ring root C rsite .black seg.val :=
    ((hSPL.2.2 seg).2 rsite).1
      ⟨hvalid, hwork⟩
  have hsrc :=
    splBlackSeamSourceIota
      hn3 hpsi ring root C e hSPL seg.val

  rcases hcases with hstay | hrest
  · rcases hstay with ⟨hir, htt⟩
    subst i
    subst t'
    exact
      PPL.remark2Right_correct_same_occurrence
        ring root seg
        C (nextConfig ring C e)
        rsite .black t
        hCtok hpost hsrc hcorr

  · rcases hrest with hord | hturn
    · rcases hord with
        ⟨hie, hcOld, hcNew, htarget, hbit, hcarry⟩
      subst i
      exact
        splBlackSeamNegativeCorrect
          ring root seg
          C (nextConfig ring C e)
          rsite e t t'
          hCtok hpost
          hcOld hcNew htarget
          hbit hcarry hsrc hcorr

    · rcases hturn with ⟨hie, hcneg, hval⟩
      subst i
      have hpostTurn :
          tokenAt .black
              ((nextConfig ring C e) e) =
            some
              (PPL.remark2NegTurnValue
                hpsi (C e).id t) := by
        rw [← hval]
        exact hpost
      have hpostCDL :=
        splBlackSeamPostCDL
          hn3 hpsi ring root C e hSPL
      exact
        PPL.remark2Row_negTurn_correct
          hpsi ring root seg
          C (nextConfig ring C e)
          e rsite .black t
          rfl rfl hCtok hcneg hpostTurn
          hvalid hwork hcorr
          hSPL.1 hpostCDL hsrc

theorem splAlgorithm23BlackOldImageRow_of_semanticSeams
    (hRight : SPLBlackOldImageInitiatorMovedRightSemanticRow)
    (hLeft : SPLBlackOldImageResponderSemanticRow) :
    SPLAlgorithm23BlackOldImageRow :=
  splAlgorithm23BlackOldImageRow_of_branches
    (splBlackOldImageInitiatorBranch_of_movedRight
      (splBlackOldImageInitiatorMovedRightBranch_of_semantic
        hRight))
    (splBlackOldImageResponderBranch_of_semantic hLeft)
    splBlackOldImageOffPairBranch_proved

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splBlackOldImageInitiatorMovedRightBranch_of_semantic
#print axioms PPL.Safety.SPL.splBlackOldImageResponderBranch_of_semantic
#print axioms PPL.Safety.SPL.splAlgorithm23BlackOldImageRow_of_semanticSeams
