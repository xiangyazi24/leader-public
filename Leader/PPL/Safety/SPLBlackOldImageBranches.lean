import Leader.PPL.Safety.SPLBlackOldImageRoute
import Leader.PPL.Safety.SPLFieldFrame
import Leader.PPL.TokenCorrectness.PersistenceRightRow
import Leader.PPL.TokenCorrectness.PersistenceRightMirror
import Leader.PPL.TokenCorrectness.PersistenceLeftMirror
import Leader.PPL.SPLEntry.RiskySweepLetterInductive

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Convergence.L18


/--
The global Algorithm-2/3 ID frame gives equality of every source bit read by
CorrectToken.  This is the missing global fact in the off-pair case: the host
state alone does not determine payloadCorrect.
-/
private theorem splBlackOldSourceIota_frame
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
  change
    (C
        (shiftRight ring
          (sourceStart psi ring root seg)
          x.val)).id =
      ((nextConfig ring C e)
        (shiftRight ring
          (sourceStart psi ring root seg)
          x.val)).id
  exact
    (hf.2.2.2
      (shiftRight ring
        (sourceStart psi ring root seg)
        x.val)).symm


/--
The off-pair old-image branch is fully closed.

The old token occurrence at i is literally unchanged.  CorrectToken is not
local in i because payloadCorrect scans source IDs, so source-Iota equality is
supplied separately by splBlackOldSourceIota_frame.
-/
theorem splBlackOldImageOffPairBranch_proved :
    SPLBlackOldImageOffPairBranch := by
  unfold SPLBlackOldImageOffPairBranch
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i _hie _hir hsame hcorr

  have hsrc :=
    splBlackOldSourceIota_frame
      hn3 hpsi ring root C e hSPL seg.val

  cases ht : tokenAt .black (C i) with
  | none =>
      unfold CorrectToken at hcorr
      rw [ht] at hcorr
      exact False.elim hcorr

  | some t =>
      have ht' :
          tokenAt .black
              ((nextConfig ring C e) i) =
            some t := by
        rw [hsame, ht]

      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg
          C (nextConfig ring C e)
          i .black t
          ht ht' hsrc hcorr


/--
Same-host transport used by the two initiator survivor cases that do not move
to the responder.

ValidToken depends only on the selected token and local dist.  WorkingFor
depends only on the selected token/host geometry.  CorrectToken additionally
depends on the global source payload, handled by hsrc.
-/
private theorem splBlackOldSameHost_correct
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg : Fin (segmentCount n psi - 2))
    (i : Fin n)
    (t : TokenData psi)
    (hSPL : SPLAt ring root C)
    (ht : tokenAt .black (C i) = some t)
    (ht' : tokenAt .black (C' i) = some t)
    (hdist : (C' i).dist = (C i).dist)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hVW :
      ValidToken .black C' i /\ WorkingFor ring root C' i .black seg.val) :
    CorrectToken ring root C' i .black seg.val := by
  have hvalidPost := hVW.1
  have hvalidPre :
      ValidToken .black C i := by
    unfold ValidToken at hvalidPost ⊢
    rw [ht'] at hvalidPost
    rw [ht]
    dsimp only at hvalidPost ⊢
    unfold tokenTargetCoordinate at hvalidPost ⊢
    rw [hdist] at hvalidPost
    exact hvalidPost

  have hworkPost := hVW.2
  have hworkPre :
      WorkingFor ring root C i .black seg.val := by
    unfold WorkingFor at hworkPost ⊢
    rw [ht'] at hworkPost
    rw [ht]
    dsimp only at hworkPost ⊢
    exact hworkPost

  have hcorrPre :
      CorrectToken ring root C i .black seg.val :=
    ((hSPL.2.2 seg).2 i).1
      ⟨hvalidPre, hworkPre⟩

  exact
    PPL.remark2Right_correct_same_occurrence
      ring root seg C C'
      i .black t
      ht ht' hsrc hcorrPre


/--
Closed line-13 gate: MoveToken is just the two sourceClear outputs, so a live
old initiator occurrence retains exactly the same TokenData value.
-/
private theorem splBlackOldClosedLeft_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hsource :
      tokenAt kind (sourceClear kind l) = some t)
    (hgate :
      Not
        ((sourceClear kind l).last = false /\ (sourceClear kind r).last = false))
    (hq :
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        some t') :
    t' = t := by
  have hframe :
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        tokenAt kind (sourceClear kind l) := by
    rw [← l18Risk2MoveTokenMirror_eq
      hpsi kind l r]
    simp [l18Risk2MoveTokenMirror, hgate]

  have hs : some t' = some t := by
    calc
      some t' =
          tokenAt kind
            (moveToken hpsi kind l r).1 :=
        hq.symm
      _ = tokenAt kind (sourceClear kind l) :=
        hframe
      _ = some t := hsource

  exact Option.some.inj hs


/--
Open gate, old left live, cleared right empty, and the output still lives on
the left: the positive cases would move/turn right, so the surviving left
value is the old value.
-/
private theorem splBlackOldOpenLeft_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear kind l).last = false /\ (sourceClear kind r).last = false)
    (hsource :
      tokenAt kind (sourceClear kind l) = some t)
    (hrnone :
      tokenAt kind (sourceClear kind r) = none)
    (hq :
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        some t') :
    t' = t := by
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi kind l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq

  by_cases hc1 :
      decodeOffset psi (tokenCode t) = 1
  · have hf : False := by
      simpa
        [hsource, hrnone, hc1,
          l18Risk2SourceSet_tokenAt]
        using hq
    exact False.elim hf

  · by_cases hc2 :
        2 <= decodeOffset psi (tokenCode t)
    · have hf : False := by
        simpa
          [hsource, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq
      exact False.elim hf

    · have hs : t = t' := by
        simpa
          [hsource, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq
      exact hs.symm


/--
The sole remaining initiator case after the literal MoveToken split:

* line-13 gate is open;
* the old black initiator token survived sourceClear;
* the cleared responder black slot is empty;
* the old lineage survives on rightNeighbor e.

This is exactly the physical seam corresponding to the landed corrected
right-selected Remark-2 mirror row.
-/
def SPLBlackOldImageInitiatorMovedRightBranch : Prop :=
  PPL.remark2_one_step_unique ->
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
          (nextConfig ring C e rsite) =
        some t' ->
      (ValidToken .black
          (nextConfig ring C e) rsite /\ WorkingFor ring root
          (nextConfig ring C e)
          rsite .black seg.val) ->
      CorrectToken ring root
        (nextConfig ring C e)
        rsite .black seg.val


/--
Proved adapter: all initiator old-image cases except the genuine moved-right
survivor are closed here.
-/
theorem splBlackOldImageInitiatorBranch_of_movedRight
    (hMove :
      SPLBlackOldImageInitiatorMovedRightBranch) :
    SPLBlackOldImageInitiatorBranch := by
  unfold SPLBlackOldImageInitiatorMovedRightBranch at hMove
  unfold SPLBlackOldImageInitiatorBranch

  intro hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t t'
  dsimp only
  intro hCtok hl0tok hshape hpost hVW

  have hf :=
    splAlgorithm23FieldFrameResidual_proved
      hn3 hpsi ring root C e hSPL
  dsimp only at hf

  have hsrc :=
    splBlackOldSourceIota_frame
      hn3 hpsi ring root C e hSPL seg.val

  rcases hshape with hclosed | hopen

  · rcases hclosed with
      ⟨hgate, hie, hq⟩
    subst i

    let p :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e)
        (C (ring.rightNeighbor e))

    have hl0 :
        tokenAt .black
            (sourceClear .black p.1) =
          some t := by
      simpa [p] using hl0tok

    have hgate' :
        Not
          ((sourceClear .black p.1).last = false /\ (sourceClear .black p.2).last = false) := by
      simpa [p] using hgate

    have hq' :
        tokenAt .black
            (moveToken hpsi .black p.1 p.2).1 =
          some t' := by
      simpa [p] using hq

    have htt :
        t' = t :=
      splBlackOldClosedLeft_same
        hpsi .black p.1 p.2
        t t' hl0 hgate' hq'
    subst t'

    exact
      splBlackOldSameHost_correct
        ring root
        C (nextConfig ring C e)
        seg e t
        hSPL
        hCtok hpost
        (hf.2.1 e)
        hsrc hVW

  · rcases hopen with
      ⟨hgate, hrnone, hwhere⟩

    rcases hwhere with hleft | hright

    · rcases hleft with
        ⟨hie, hq⟩
      subst i

      let p :=
        PPL.Safety.PeacefulProps.preTokenPair
          hpsi (C e)
          (C (ring.rightNeighbor e))

      have hgate' :
          (sourceClear .black p.1).last = false /\ (sourceClear .black p.2).last = false := by
        simpa [p] using hgate

      have hl0 :
          tokenAt .black
              (sourceClear .black p.1) =
            some t := by
        simpa [p] using hl0tok

      have hr0 :
          tokenAt .black
              (sourceClear .black p.2) =
            none := by
        simpa [p] using hrnone

      have hq' :
          tokenAt .black
              (moveToken hpsi .black p.1 p.2).1 =
            some t' := by
        simpa [p] using hq

      have htt :
          t' = t :=
        splBlackOldOpenLeft_same
          hpsi .black p.1 p.2
          t t' hgate' hl0 hr0 hq'
      subst t'

      exact
        splBlackOldSameHost_correct
          ring root
          C (nextConfig ring C e)
          seg e t
          hSPL
          hCtok hpost
          (hf.2.1 e)
          hsrc hVW

    · rcases hright with
        ⟨hir, hq⟩
      subst i

      exact
        hMove hRemark
          hn3 hpsi ring root C e hSPL
          seg t t'
          hCtok hl0tok
          hgate hrnone hq
          hpost hVW


end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splBlackOldImageOffPairBranch_proved
#print axioms PPL.Safety.SPL.SPLBlackOldImageInitiatorMovedRightBranch
#print axioms PPL.Safety.SPL.splBlackOldImageInitiatorBranch_of_movedRight
