import Leader.PPL.Safety.SPLTokenResidualRoute
import Leader.PPL.Safety.SPLFieldFrame
import Leader.PPL.Safety.PeacefulScan
import Leader.PPL.TokenCorrectness.PersistenceRightRow
import Leader.PPL.TokenCorrectness.PersistenceRightMirror
import Leader.PPL.TokenCorrectness.PersistenceLeftMirror
import Leader.PPL.TokenCorrectness.PersistenceLeftRow
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Init.Omega

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Convergence.L18

private def splWhiteSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  PPL.moveToken hpsi .black p.1 p.2

/-! -------------------------------------------------------------------------
    Top-level white route
------------------------------------------------------------------------- -/

def SPLAlgorithm23WhiteOldImageRow : Prop :=
  PPL.remark2_one_step_unique →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀ (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t' : TokenData psi),
      tokenAt .white
          (nextConfig ring C e i) =
        some t' →
      SPLPostTokenOldImage
          hpsi ring C e i .white t' →
      (ValidToken .white
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .white seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        i .white seg.val

def SPLAlgorithm23WhiteFreshBirthRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀ (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t' : TokenData psi),
      tokenAt .white
          (nextConfig ring C e i) =
        some t' →
      SPLFreshBorderBirthImage
          hpsi 0 ring C e i .white t' →
      (ValidToken .white
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .white seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        i .white seg.val

theorem splAlgorithm23WhiteCorrectnessRow_of_caseRows
    (hOld : SPLAlgorithm23WhiteOldImageRow)
    (hFresh : SPLAlgorithm23WhiteFreshBirthRow) :
    SPLAlgorithm23WhiteCorrectnessRow := by
  unfold SPLAlgorithm23WhiteOldImageRow at hOld
  unfold SPLAlgorithm23WhiteFreshBirthRow at hFresh
  unfold SPLAlgorithm23WhiteCorrectnessRow
  intro hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i hVW
  rcases hVW with ⟨hValid, hWork⟩
  cases ht :
      tokenAt .white
        (nextConfig ring C e i) with
  | none =>
      unfold ValidToken at hValid
      rw [ht] at hValid
      exact False.elim hValid
  | some t' =>
      have hp :
          SPLPostTokenOldImage
              hpsi ring C e i .white t' ∨
            SPLFreshBorderBirthImage
              hpsi 0 ring C e i .white t' :=
        splPostTokenProvenance_proved
          hn3 hpsi 0 ring root C e hSPL
          i .white t' ht
      rcases hp with hOldImage | hBirth
      · exact
          hOld hRemark
            hn3 hpsi ring root C e hSPL
            seg i t' ht hOldImage
            ⟨hValid, hWork⟩
      · exact
          hFresh
            hn3 hpsi ring root C e hSPL
            seg i t' ht hBirth
            ⟨hValid, hWork⟩

/-! -------------------------------------------------------------------------
    White old-image route
------------------------------------------------------------------------- -/

def SPLWhiteOldImageInitiatorBranch : Prop :=
  PPL.remark2_one_step_unique →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        splWhiteSelectedInput
          hpsi (C e) (C rsite)
      let l0 := sourceClear .white p.1
      let r0 := sourceClear .white p.2
      let q := moveToken hpsi .white p.1 p.2
      let gate :=
        l0.last = false ∧ r0.last = false
      tokenAt .white (C e) = some t →
      tokenAt .white l0 = some t →
      ((¬ gate ∧
          i = e ∧
          tokenAt .white q.1 = some t') ∨
        (gate ∧
          tokenAt .white r0 = none ∧
          ((i = e ∧
              tokenAt .white q.1 = some t') ∨
            (i = rsite ∧
              tokenAt .white q.2 = some t')))) →
      tokenAt .white
          (nextConfig ring C e i) =
        some t' →
      (ValidToken .white
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .white seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        i .white seg.val

def SPLWhiteOldImageResponderBranch : Prop :=
  PPL.remark2_one_step_unique →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        splWhiteSelectedInput
          hpsi (C e) (C rsite)
      let l0 := sourceClear .white p.1
      let r0 := sourceClear .white p.2
      let q := moveToken hpsi .white p.1 p.2
      let gate :=
        l0.last = false ∧ r0.last = false
      tokenAt .white (C rsite) = some t →
      tokenAt .white r0 = some t →
      ((¬ gate ∧
          i = rsite ∧
          tokenAt .white q.2 = some t') ∨
        (gate ∧
          ((i = e ∧
              tokenAt .white q.1 = some t') ∨
            (i = rsite ∧
              tokenAt .white q.2 = some t')))) →
      tokenAt .white
          (nextConfig ring C e i) =
        some t' →
      (ValidToken .white
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .white seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        i .white seg.val

private theorem splWhiteOldStep_other
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    nextConfig ring C e i = C i := by
  unfold nextConfig PopulationProtocol.step
  simp [hie, hir]

def SPLWhiteOldImageOffPairBranch : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n),
      i ≠ e →
      i ≠ ring.rightNeighbor e →
      nextConfig ring C e i = C i →
      CorrectToken ring root C i .white seg.val →
      CorrectToken ring root
        (nextConfig ring C e)
        i .white seg.val

theorem splAlgorithm23WhiteOldImageRow_of_branches
    (hInitiator : SPLWhiteOldImageInitiatorBranch)
    (hResponder : SPLWhiteOldImageResponderBranch)
    (hOff : SPLWhiteOldImageOffPairBranch) :
    SPLAlgorithm23WhiteOldImageRow := by
  unfold SPLWhiteOldImageInitiatorBranch at hInitiator
  unfold SPLWhiteOldImageResponderBranch at hResponder
  unfold SPLAlgorithm23WhiteOldImageRow
  intro hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t' hpost hOld hVW

  unfold SPLPostTokenOldImage at hOld
  dsimp only at hOld
  rcases hOld with
    ⟨j, t, _hwhere, hCtok, hshape⟩
  rcases hshape with hleft | hright | hoff

  · rcases hleft with
      ⟨hje, hl0tok, hmove⟩
    subst j
    exact
      hInitiator hRemark
        hn3 hpsi ring root C e hSPL
        seg i t t'
        hCtok
        (by exact hl0tok)
        (by exact hmove)
        hpost hVW

  · rcases hright with
      ⟨hjr, hr0tok, hmove⟩
    subst j
    exact
      hResponder hRemark
        hn3 hpsi ring root C e hSPL
        seg i t t'
        hCtok
        (by exact hr0tok)
        (by exact hmove)
        hpost hVW

  · rcases hoff with
      ⟨hji, hie, hir, _htt⟩
    subst j
    have hsame :
        nextConfig ring C e i = C i :=
      splWhiteOldStep_other
        ring C e i hie hir
    have hVW0 :
        ValidToken .white C i ∧
          WorkingFor ring root C i
            .white seg.val := by
      unfold ValidToken WorkingFor at hVW
      unfold ValidToken WorkingFor
      rw [hsame] at hVW
      exact hVW
    exact
      hOff hn3 hpsi ring root C e hSPL
        seg i hie hir hsame
        (((hSPL.2.2 seg).2 i).2 hVW0)

/-! -------------------------------------------------------------------------
    Shared proved old-image infrastructure
------------------------------------------------------------------------- -/

private theorem splWhiteSourceIota_frame
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
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

theorem splWhiteOldImageOffPairBranch_proved :
    SPLWhiteOldImageOffPairBranch := by
  unfold SPLWhiteOldImageOffPairBranch
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i _hie _hir hsame hcorr

  have hsrc :=
    splWhiteSourceIota_frame
      hn3 hpsi ring root C e hSPL seg.val

  cases ht : tokenAt .white (C i) with
  | none =>
      unfold CorrectToken at hcorr
      rw [ht] at hcorr
      exact False.elim hcorr
  | some t =>
      have ht' :
          tokenAt .white
              ((nextConfig ring C e) i) =
            some t := by
        rw [hsame, ht]
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg
          C (nextConfig ring C e)
          i .white t
          ht ht' hsrc hcorr

private theorem splWhiteOldSameHost_correct
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg : Fin (segmentCount n psi - 2))
    (i : Fin n)
    (t : TokenData psi)
    (hSPL : SPLAt ring root C)
    (ht : tokenAt .white (C i) = some t)
    (ht' : tokenAt .white (C' i) = some t)
    (hdist : (C' i).dist = (C i).dist)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hVW :
      ValidToken .white C' i ∧
        WorkingFor ring root C' i .white seg.val) :
    CorrectToken ring root C' i .white seg.val := by
  have hvalidPost := hVW.1
  have hvalidPre :
      ValidToken .white C i := by
    unfold ValidToken at hvalidPost ⊢
    rw [ht'] at hvalidPost
    rw [ht]
    dsimp only at hvalidPost ⊢
    unfold tokenTargetCoordinate at hvalidPost ⊢
    rw [hdist] at hvalidPost
    exact hvalidPost

  have hworkPost := hVW.2
  have hworkPre :
      WorkingFor ring root C i .white seg.val := by
    unfold WorkingFor at hworkPost ⊢
    rw [ht'] at hworkPost
    rw [ht]
    dsimp only at hworkPost ⊢
    exact hworkPost

  have hcorrPre :
      CorrectToken ring root C i .white seg.val :=
    ((hSPL.2.2 seg).2 i).2
      ⟨hvalidPre, hworkPre⟩

  exact
    PPL.remark2Right_correct_same_occurrence
      ring root seg C C'
      i .white t
      ht ht' hsrc hcorrPre

private theorem splWhiteOldClosedLeft_same
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hsource :
      tokenAt kind (sourceClear kind l) = some t)
    (hgate :
      ¬ ((sourceClear kind l).last = false ∧
          (sourceClear kind r).last = false))
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

private theorem splWhiteOldOpenLeft_same
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear kind l).last = false ∧
        (sourceClear kind r).last = false)
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
        2 ≤ decodeOffset psi (tokenCode t)
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

def SPLWhiteOldImageInitiatorMovedRightBranch : Prop :=
  PPL.remark2_one_step_unique →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀
      (seg : Fin (segmentCount n psi - 2))
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        splWhiteSelectedInput
          hpsi (C e) (C rsite)
      let l0 := sourceClear .white p.1
      let r0 := sourceClear .white p.2
      let q := moveToken hpsi .white p.1 p.2
      let gate :=
        l0.last = false ∧ r0.last = false
      tokenAt .white (C e) = some t →
      tokenAt .white l0 = some t →
      gate →
      tokenAt .white r0 = none →
      tokenAt .white q.2 = some t' →
      tokenAt .white
          (nextConfig ring C e rsite) =
        some t' →
      (ValidToken .white
          (nextConfig ring C e) rsite ∧
        WorkingFor ring root
          (nextConfig ring C e)
          rsite .white seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        rsite .white seg.val

theorem splWhiteOldImageInitiatorBranch_of_movedRight
    (hMove :
      SPLWhiteOldImageInitiatorMovedRightBranch) :
    SPLWhiteOldImageInitiatorBranch := by
  unfold SPLWhiteOldImageInitiatorMovedRightBranch at hMove
  unfold SPLWhiteOldImageInitiatorBranch
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
    splWhiteSourceIota_frame
      hn3 hpsi ring root C e hSPL seg.val

  rcases hshape with hclosed | hopen

  · rcases hclosed with
      ⟨hgate, hie, hq⟩
    subst i

    let p :=
      splWhiteSelectedInput
        hpsi (C e)
        (C (ring.rightNeighbor e))

    have hl0 :
        tokenAt .white
            (sourceClear .white p.1) =
          some t := by
      simpa [p] using hl0tok

    have hgate' :
        ¬ ((sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false) := by
      simpa [p] using hgate

    have hq' :
        tokenAt .white
            (moveToken hpsi .white p.1 p.2).1 =
          some t' := by
      simpa [p] using hq

    have htt :
        t' = t :=
      splWhiteOldClosedLeft_same
        hpsi .white p.1 p.2
        t t' hl0 hgate' hq'
    subst t'

    exact
      splWhiteOldSameHost_correct
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
        splWhiteSelectedInput
          hpsi (C e)
          (C (ring.rightNeighbor e))

      have hgate' :
          (sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false := by
        simpa [p] using hgate

      have hl0 :
          tokenAt .white
              (sourceClear .white p.1) =
            some t := by
        simpa [p] using hl0tok

      have hr0 :
          tokenAt .white
              (sourceClear .white p.2) =
            none := by
        simpa [p] using hrnone

      have hq' :
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).1 =
            some t' := by
        simpa [p] using hq

      have htt :
          t' = t :=
        splWhiteOldOpenLeft_same
          hpsi .white p.1 p.2
          t t' hgate' hl0 hr0 hq'
      subst t'

      exact
        splWhiteOldSameHost_correct
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

/-! -------------------------------------------------------------------------
    White fresh birth: proved
------------------------------------------------------------------------- -/

private theorem splFreshWhiteSourceClear_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).dist = q.dist := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none => rfl
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem splFreshWhiteSourceClear_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).id = q.id := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none => rfl
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem splWhiteBlackPass_left_fields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    (moveToken hpsi .black l r).1.dist = l.dist ∧
      (moveToken hpsi .black l r).1.id = l.id ∧
      (moveToken hpsi .black l r).1.last = l.last := by
  have h :=
    PPL.moveToken_initiator_fields
      hpsi .black l r
  have hd :=
    congrArg
      (fun q : State psi kappa => q.dist) h
  have hi :=
    congrArg
      (fun q : State psi kappa => q.id) h
  have hl :=
    congrArg
      (fun q : State psi kappa => q.last) h
  exact
    ⟨by simpa [PPL.eraseKindToken] using hd,
      by simpa [PPL.eraseKindToken] using hi,
      by simpa [PPL.eraseKindToken] using hl⟩

private theorem splFreshWhiteLeft_none
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa)
    (hgate :
      (sourceClear .white l).last = false ∧
        (sourceClear .white r).last = false)
    (hlnone :
      tokenAt .white (sourceClear .white l) = none)
    (hrnone :
      tokenAt .white (sourceClear .white r) = none)
    (hdist :
      (sourceClear .white l).dist.val =
        tokenD' psi .white) :
    tokenAt .white
        (moveToken hpsi .white l r).1 =
      none := by
  have hpsiNeOne :
      ((psi : Nat) : Int) ≠ 1 := by
    omega
  have hpsiGeTwo :
      (2 : Int) ≤ ((psi : Nat) : Int) := by
    omega
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi TokenKind.white l r]
  unfold l18Risk2MoveTokenMirror
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte]
  simp
    [hlnone, hrnone, hdist, tokenD',
      l18Risk2SourceSet_tokenAt,
      l18Risk2MkToken, tokenCode,
      decodeOffset_psi psi hpsi,
      hpsiNeOne, hpsiGeTwo]

private theorem splFreshWhiteRight_data
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa)
    (t' : TokenData psi)
    (hgate :
      (sourceClear .white l).last = false ∧
        (sourceClear .white r).last = false)
    (hlnone :
      tokenAt .white (sourceClear .white l) = none)
    (hrnone :
      tokenAt .white (sourceClear .white r) = none)
    (hdist :
      (sourceClear .white l).dist.val =
        tokenD' psi .white)
    (hq :
      tokenAt .white
          (moveToken hpsi .white l r).2 =
        some t') :
    decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int) - 1 ∧
      tokenBitBool t' =
        !(sourceClear .white l).id ∧
      tokenCarryBool t' =
        (sourceClear .white l).id := by
  have hpsiNeOne :
      ((psi : Nat) : Int) ≠ 1 := by
    omega
  have hpsiGeTwo :
      (2 : Int) ≤ ((psi : Nat) : Int) := by
    omega
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi TokenKind.white l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq
  simp
    [hlnone, hrnone, hdist, tokenD',
      l18Risk2SourceSet_tokenAt,
      l18Risk2MkToken, tokenCode,
      decodeOffset_psi psi hpsi,
      hpsiNeOne, hpsiGeTwo] at hq

  have hdec :=
    congrArg
      (fun u : TokenData psi =>
        decodeOffset psi (tokenCode u))
      hq.symm
  have hcode :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int) - 1 := by
    simpa
      [l18Risk2MkToken, tokenCode,
        decode_encode]
      using hdec

  have hbit0 :=
    congrArg tokenBitBool hq.symm
  have hbit :
      tokenBitBool t' =
        !(sourceClear .white l).id := by
    cases hb : (sourceClear .white l).id <;>
      simpa
        [l18Risk2MkToken, l18Risk2BitToFin,
          tokenBitBool, hb]
        using hbit0

  have hcarry0 :=
    congrArg tokenCarryBool hq.symm
  have hcarry :
      tokenCarryBool t' =
        (sourceClear .white l).id := by
    cases hb : (sourceClear .white l).id <;>
      simpa
        [l18Risk2MkToken, l18Risk2BitToFin,
          tokenCarryBool, hb]
        using hcarry0

  exact ⟨hcode, hbit, hcarry⟩

private theorem splFreshWhite_certificate
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (t' : TokenData psi)
    (hC : SPLAt ring root C)
    (hFresh :
      SPLFreshBorderBirthImage
        hpsi 0 ring C e i .white t') :
    i = ring.rightNeighbor e ∧
      (C e).dist.val = psi ∧
      (C e).last = false ∧
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int) - 1 ∧
      tokenBitBool t' = !(C e).id ∧
      tokenCarryBool t' = (C e).id := by
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C (ring.rightNeighbor e))
  let p :=
    moveToken hpsi .black pre.1 pre.2

  have hrow0 :=
    splAlgorithm2DistWriteIdempotent
      hn3 hpsi ring root C e hC
  dsimp only at hrow0
  have hpreDist :
      pre.1.dist = (C e).dist := by
    simpa [pre] using hrow0.2.2.2.1
  have hpreId :
      pre.1.id = (C e).id := by
    simpa [pre] using hrow0.2.2.2.2.2.1

  have hlast0 :=
    splAlgorithm2LastWriteIdempotent
      hn3 hpsi ring root C e hC
  dsimp only at hlast0
  have hpreLast :
      pre.1.last = (C e).last := by
    simpa [pre] using hlast0.1

  have hb :=
    splWhiteBlackPass_left_fields
      hpsi pre.1 pre.2

  have hpDist :
      p.1.dist = (C e).dist := by
    calc
      p.1.dist = pre.1.dist := by
        simpa [p] using hb.1
      _ = (C e).dist := hpreDist

  have hpId :
      p.1.id = (C e).id := by
    calc
      p.1.id = pre.1.id := by
        simpa [p] using hb.2.1
      _ = (C e).id := hpreId

  have hpLast :
      p.1.last = (C e).last := by
    calc
      p.1.last = pre.1.last := by
        simpa [p] using hb.2.2
      _ = (C e).last := hpreLast

  unfold SPLFreshBorderBirthImage at hFresh
  dsimp only at hFresh
  rcases hFresh with
    ⟨_hborder, hllast, hrlast,
      hlnone, hrnone, hdist, hout, _hmeta⟩

  have hllast' :
      (sourceClear .white p.1).last = false := by
    exact hllast
  have hrlast' :
      (sourceClear .white p.2).last = false := by
    exact hrlast
  have hlnone' :
      tokenAt .white
          (sourceClear .white p.1) =
        none := by
    exact hlnone
  have hrnone' :
      tokenAt .white
          (sourceClear .white p.2) =
        none := by
    exact hrnone
  have hdist' :
      (sourceClear .white p.1).dist.val =
        tokenD' psi .white := by
    exact hdist
  have hgate :
      (sourceClear .white p.1).last = false ∧
        (sourceClear .white p.2).last = false :=
    ⟨hllast', hrlast'⟩

  have hdistC :
      (C e).dist.val = psi := by
    calc
      (C e).dist.val = p.1.dist.val := by
        exact congrArg Fin.val hpDist.symm
      _ =
          (sourceClear .white p.1).dist.val := by
        exact
          congrArg Fin.val
            (splFreshWhiteSourceClear_dist
              TokenKind.white p.1).symm
      _ = psi := by
        simpa [tokenD'] using hdist'

  have hlastC :
      (C e).last = false := by
    calc
      (C e).last = p.1.last := hpLast.symm
      _ = (sourceClear .white p.1).last :=
        (l18Risk2SourceClear_last
          TokenKind.white p.1).symm
      _ = false := hllast'

  have hclearId :
      (sourceClear .white p.1).id =
        (C e).id := by
    calc
      (sourceClear .white p.1).id =
          p.1.id :=
        splFreshWhiteSourceClear_id
          TokenKind.white p.1
      _ = (C e).id := hpId

  rcases hout with hleft | hright

  · rcases hleft with ⟨_hie, hq1⟩
    have hq1' :
        tokenAt .white
            (moveToken hpsi .white p.1 p.2).1 =
          some t' := by
      exact hq1
    have hn :=
      splFreshWhiteLeft_none
        hpsi p.1 p.2
        hgate hlnone' hrnone' hdist'
    have hbad :
        (none : Option (TokenData psi)) =
          some t' :=
      hn.symm.trans hq1'
    cases hbad

  · rcases hright with ⟨hir, hq2⟩
    have hq2' :
        tokenAt .white
            (moveToken hpsi .white p.1 p.2).2 =
          some t' := by
      exact hq2
    have hd :=
      splFreshWhiteRight_data
        hpsi p.1 p.2 t'
        hgate hlnone' hrnone' hdist' hq2'
    rcases hd with ⟨hcode, hbit0, hcarry0⟩

    have hbit :
        tokenBitBool t' = !(C e).id := by
      calc
        tokenBitBool t' =
            !(sourceClear .white p.1).id :=
          hbit0
        _ = !(C e).id := by
          rw [hclearId]

    have hcarry :
        tokenCarryBool t' = (C e).id := by
      calc
        tokenCarryBool t' =
            (sourceClear .white p.1).id :=
          hcarry0
        _ = (C e).id := hclearId

    exact
      ⟨hir, hdistC, hlastC,
        hcode, hbit, hcarry⟩

private theorem splFreshWhite_targetSite
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hcode :
      decodeOffset psi (tokenCode t) =
        ((psi : Nat) : Int) - 1) :
    tokenTargetSite ring
        (ring.rightNeighbor e) t =
      shiftRight ring e psi := by
  have hcodeNat :
      decodeOffset psi (tokenCode t) =
        ((psi - 1 : Nat) : Int) := by
    calc
      decodeOffset psi (tokenCode t) =
          ((psi : Nat) : Int) - 1 :=
        hcode
      _ = ((psi - 1 : Nat) : Int) := by
        omega
  have hpos :
      0 < decodeOffset psi (tokenCode t) := by
    rw [hcodeNat]
    try simp only [Int.ofNat_eq_coe]
    omega
  unfold tokenTargetSite
  rw [if_pos hpos, hcodeNat]
  change
    shiftRight ring
        (shiftRight ring e 1) (psi - 1) =
      shiftRight ring e psi
  calc
    shiftRight ring
        (shiftRight ring e 1) (psi - 1) =
        shiftRight ring e (1 + (psi - 1)) :=
      l18Risk2ShiftRight_add
        ring e 1 (psi - 1)
    _ = shiftRight ring e psi := by
      congr 2
      omega

private theorem splFreshWhite_geometry
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t' : TokenData psi)
    (hC : SPLAt ring root C)
    (hpost :
      tokenAt .white
          ((nextConfig ring C e)
            (ring.rightNeighbor e)) =
        some t')
    (hwork :
      WorkingFor ring root
        (nextConfig ring C e)
        (ring.rightNeighbor e)
        .white seg.val)
    (hdist : (C e).dist.val = psi)
    (hlast : (C e).last = false)
    (hcode :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int) - 1) :
    seg.val % 2 = 1 ∧
      shiftRight ring root
          (seg.val * psi) =
        e ∧
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
        shiftRight ring e psi ∧
      cyclicOffset ring
          (shiftRight ring root
            (seg.val * psi))
          (tokenTargetSite ring
            (ring.rightNeighbor e) t') =
        psi := by
  let zeta := segmentCount n psi
  let off := cyclicOffset ring root e

  have hgeom := hC.1.2.2 e
  dsimp only at hgeom

  have hoff2 :
      off % (2 * psi) = psi := by
    calc
      off % (2 * psi) =
          (C e).dist.val := by
        simpa [off] using hgeom.1.symm
      _ = psi := hdist

  have hbelow :
      off < psi * (zeta - 1) := by
    by_cases hge :
        psi * (zeta - 1) ≤ off
    · have ht : (C e).last = true := by
        apply hgeom.2.mpr
        simpa [off, zeta] using hge
      rw [hlast] at ht
      contradiction
    · omega

  let a := off / (2 * psi)
  have hdec :=
    Nat.mod_add_div off (2 * psi)
  rw [hoff2] at hdec

  have hoffEq :
      off = (2 * a + 1) * psi := by
    dsimp only [a]
    calc
      off =
          psi +
            (2 * psi) *
              (off / (2 * psi)) :=
        hdec.symm
      _ =
          (2 * (off / (2 * psi)) + 1) *
            psi := by
        rw [Nat.add_mul, Nat.one_mul]
        ac_rfl

  have hslt :
      2 * a + 1 < zeta - 1 := by
    have hm :
        psi * (2 * a + 1) <
          psi * (zeta - 1) := by
      calc
        psi * (2 * a + 1) =
            (2 * a + 1) * psi :=
          Nat.mul_comm _ _
        _ = off := hoffEq.symm
        _ < psi * (zeta - 1) := hbelow
    exact
      (Nat.mul_lt_mul_left
        (by omega : 0 < psi)).mp hm

  have hoffPlus :
      off + psi = (2 * a + 2) * psi := by
    rw [hoffEq, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

  have hth0 :=
    l18Gapped_lastThreshold_lt
      (n := n) (psi := psi) hn3 hpsi
  have hth :
      psi * (zeta - 1) < n := by
    simpa [l18GappedLastThreshold, zeta]
      using hth0

  have hoffPlusLtN :
      off + psi < n := by
    have hle :
        2 * a + 2 ≤ zeta - 1 := by
      omega
    have hm :=
      Nat.mul_le_mul_right psi hle
    calc
      off + psi =
          (2 * a + 2) * psi :=
        hoffPlus
      _ ≤ (zeta - 1) * psi := hm
      _ = psi * (zeta - 1) :=
        Nat.mul_comm _ _
      _ < n := hth

  have hpsiN : psi < n := by
    omega

  have htarget :=
    splFreshWhite_targetSite
      hpsi ring e t' hcode

  have htargetRoot :
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
        shiftRight ring root (off + psi) := by
    calc
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
          shiftRight ring e psi :=
        htarget
      _ =
          shiftRight ring
            (shiftRight ring root off) psi := by
        rw [l18Risk2ShiftRight_cyclicOffset
          ring root e]
      _ =
          shiftRight ring root (off + psi) :=
        l18Risk2ShiftRight_add
          ring root off psi

  have htargetOff :
      cyclicOffset ring root
          (tokenTargetSite ring
            (ring.rightNeighbor e) t') =
        off + psi := by
    rw [htargetRoot]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root (off + psi) hoffPlusLtN

  have hw := hwork
  unfold WorkingFor at hw
  rw [hpost] at hw
  dsimp only at hw

  have hin :
      InSegment ring root psi
        ((seg.val + 1) % segmentCount n psi)
        (tokenTargetSite ring
          (ring.rightNeighbor e) t') := by
    rcases hw.2 with hp | hn
    · exact hp.2
    · have hc := hcode
      try simp only [Int.ofNat_eq_coe] at hc
      have hf : False := by
        omega
      exact False.elim hf

  have hseglt :
      seg.val < zeta - 2 := by
    simpa [zeta] using seg.isLt

  have hidxLt :
      seg.val + 1 < zeta := by
    omega

  have hidx0 :
      (seg.val + 1) % zeta =
        seg.val + 1 :=
    Nat.mod_eq_of_lt hidxLt

  have hidx :
      (seg.val + 1) %
          segmentCount n psi =
        seg.val + 1 := by
    simpa [zeta] using hidx0

  unfold InSegment at hin
  dsimp only at hin
  rw [hidx, htargetOff] at hin

  have hlowerMul :
      (seg.val + 1) * psi ≤
        (2 * a + 2) * psi := by
    rw [← hoffPlus]
    exact hin.1

  have hlower :
      seg.val + 1 ≤ 2 * a + 2 :=
    Nat.le_of_mul_le_mul_right
      hlowerMul (by omega)

  have hupper0 :
      off + psi <
        (seg.val + 1 + 1) * psi :=
    Nat.lt_of_lt_of_le
      hin.2 (Nat.min_le_left _ _)

  have hupperMul :
      psi * (2 * a + 2) <
        psi * (seg.val + 2) := by
    calc
      psi * (2 * a + 2) =
          (2 * a + 2) * psi :=
        Nat.mul_comm _ _
      _ = off + psi := hoffPlus.symm
      _ <
          (seg.val + 1 + 1) * psi :=
        hupper0
      _ = (seg.val + 2) * psi := by
        rw [show
          seg.val + 1 + 1 =
            seg.val + 2 by omega]
      _ = psi * (seg.val + 2) :=
        Nat.mul_comm _ _

  have hupper :
      2 * a + 2 < seg.val + 2 :=
    (Nat.mul_lt_mul_left
      (by omega : 0 < psi)).mp hupperMul

  have hseg :
      seg.val = 2 * a + 1 := by
    omega

  have hparity :
      seg.val % 2 = 1 := by
    rw [hseg]
    omega

  have hoffSeg :
      off = seg.val * psi := by
    calc
      off = (2 * a + 1) * psi := hoffEq
      _ = seg.val * psi := by
        rw [hseg]

  have hsource :
      shiftRight ring root
          (seg.val * psi) =
        e := by
    rw [← hoffSeg]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root e

  have hrel :
      cyclicOffset ring
          (shiftRight ring root
            (seg.val * psi))
          (tokenTargetSite ring
            (ring.rightNeighbor e) t') =
        psi := by
    rw [hsource, htarget]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring e psi hpsiN

  exact
    ⟨hparity, hsource, htarget, hrel⟩

private theorem splFreshWhiteFirstZeroAux_ge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (source : Fin n) :
    ∀ fuel j : Nat,
      j ≤ firstZeroAux ring D source fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j
      simp [firstZeroAux]
  | succ fuel ih =>
      intro j
      simp only [firstZeroAux]
      split
      · omega
      · have h := ih (j + 1)
        omega

private theorem splFreshWhiteFirstZeroBit_zero_of_false
    {n psi kappa : Nat}
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (source : Fin n)
    (hhead : (D source).id = false) :
    firstZeroBit ring D source = 0 := by
  cases psi with
  | zero => omega
  | succ fuel =>
      simp
        [firstZeroBit, firstZeroAux,
          l18Risk2ShiftRight_zero, hhead]

private theorem splFreshWhiteFirstZeroBit_pos_of_true
    {n psi kappa : Nat}
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (source : Fin n)
    (hhead : (D source).id = true) :
    0 < firstZeroBit ring D source := by
  cases psi with
  | zero => omega
  | succ fuel =>
      have hstep :
          firstZeroBit ring D source =
            firstZeroAux ring D source fuel 1 := by
        simp
          [firstZeroBit, firstZeroAux,
            l18Risk2ShiftRight_zero, hhead]
      rw [hstep]
      have hge :=
        splFreshWhiteFirstZeroAux_ge
          ring D source fuel 1
      omega

private theorem splFreshWhitePayload_x0
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (source : Fin n)
    (t : TokenData psi)
    (hbit :
      tokenBitBool t = !(D source).id)
    (hcarry :
      tokenCarryBool t = (D source).id) :
    payloadCorrect ring D source 0 t := by
  cases hs : (D source).id with
  | false =>
      have hj :=
        splFreshWhiteFirstZeroBit_zero_of_false
          (by omega) ring D source hs
      have hb := hbit
      have hc := hcarry
      rw [hs] at hb hc
      simp at hb hc
      unfold payloadCorrect
      dsimp only
      rw [l18Risk2ShiftRight_zero, hs, hj]
      simp only
        [Nat.zero_le, if_pos,
          Nat.lt_irrefl, if_false,
          Bool.not_false]
      exact ⟨hb, hc⟩

  | true =>
      have hj :=
        splFreshWhiteFirstZeroBit_pos_of_true
          (by omega) ring D source hs
      have hb := hbit
      have hc := hcarry
      rw [hs] at hb hc
      simp at hb hc
      unfold payloadCorrect
      dsimp only
      rw [l18Risk2ShiftRight_zero, hs]
      simp only
        [Nat.zero_le, if_pos,
          hj, Bool.not_true]
      exact ⟨hb, hc⟩

theorem splAlgorithm23WhiteFreshBirthRow_proved :
    SPLAlgorithm23WhiteFreshBirthRow := by
  unfold SPLAlgorithm23WhiteFreshBirthRow
  intro n psi kappa
  intro hn3 hpsi ring root C e hC
  intro seg i t' hpost hFresh hVW
  rcases hVW with ⟨_hvalid, hwork⟩

  have hcert :=
    splFreshWhite_certificate
      hn3 hpsi ring root C e i t' hC hFresh
  rcases hcert with
    ⟨hir, hdist, hlast,
      hcode, hbit, hcarry⟩
  subst i

  have hgeo :=
    splFreshWhite_geometry
      hn3 hpsi ring root C e
      seg t' hC hpost hwork
      hdist hlast hcode
  rcases hgeo with
    ⟨hparity, hsource, _htarget, hrel⟩

  have hf :=
    splAlgorithm23FieldFrameResidual_proved
      hn3 hpsi ring root C e hC
  dsimp only at hf

  have hid :
      ((nextConfig ring C e) e).id =
        (C e).id :=
    hf.2.2.2 e

  have hbitPost :
      tokenBitBool t' =
        !((nextConfig ring C e) e).id := by
    calc
      tokenBitBool t' = !(C e).id := hbit
      _ = !((nextConfig ring C e) e).id := by
        simpa using
          congrArg
            (fun b : Bool => !b)
            hid.symm

  have hcarryPost :
      tokenCarryBool t' =
        ((nextConfig ring C e) e).id := by
    calc
      tokenCarryBool t' = (C e).id := hcarry
      _ = ((nextConfig ring C e) e).id :=
        hid.symm

  have hpayE :
      payloadCorrect ring
        (nextConfig ring C e)
        e 0 t' :=
    splFreshWhitePayload_x0
      hpsi ring
      (nextConfig ring C e)
      e t' hbitPost hcarryPost

  have hpay :
      payloadCorrect ring
        (nextConfig ring C e)
        (shiftRight ring root
          (seg.val * psi))
        0 t' := by
    rw [hsource]
    exact hpayE

  have hcodeNat :
      decodeOffset psi (tokenCode t') =
        ((psi - 1 : Nat) : Int) := by
    calc
      decodeOffset psi (tokenCode t') =
          ((psi : Nat) : Int) - 1 :=
        hcode
      _ = ((psi - 1 : Nat) : Int) := by
        omega

  have hpos :
      0 < decodeOffset psi (tokenCode t') := by
    rw [hcodeNat]
    try simp only [Int.ofNat_eq_coe]
    omega

  unfold CorrectToken
  rw [hpost]
  dsimp only
  refine ⟨hparity, ?_⟩
  rw [if_pos hpos, hrel]
  try dsimp only
  refine ⟨by omega, ?_⟩
  simp only [Nat.sub_self]
  exact ⟨by omega, hpay⟩

/-! -------------------------------------------------------------------------
    The two and only two open semantic seams
------------------------------------------------------------------------- -/

private theorem splWhiteSeamPostCDL
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
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

private theorem splWhiteSeamNegativeCorrect
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (i j : Fin n)
    (t t' : TokenData psi)
    (ht : tokenAt .white (C i) = some t)
    (ht' : tokenAt .white (C' j) = some t')
    (hcOld :
      decodeOffset psi (tokenCode t) < 0)
    (hcNew :
      decodeOffset psi (tokenCode t') < 0)
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
      CorrectToken ring root
        C i .white seg.val) :
    CorrectToken ring root
      C' j .white seg.val := by
  unfold CorrectToken at hcorr ⊢
  rw [ht] at hcorr
  rw [ht']
  dsimp only at hcorr ⊢
  have holdNot :
      ¬ (0 < decodeOffset psi (tokenCode t)) := by
    omega
  have hnewNot :
      ¬ (0 < decodeOffset psi (tokenCode t')) := by
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

def SPLWhiteOldImageInitiatorMovedRightSemanticRow : Prop :=
  PPL.Remark2RightSelectedMirrorRowCorrected →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀
      (seg : Fin (segmentCount n psi - 2))
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        splWhiteSelectedInput
          hpsi (C e) (C rsite)
      let l0 := sourceClear .white p.1
      let r0 := sourceClear .white p.2
      let q := moveToken hpsi .white p.1 p.2
      let gate :=
        l0.last = false ∧ r0.last = false
      tokenAt .white (C e) = some t →
      tokenAt .white l0 = some t →
      gate →
      tokenAt .white r0 = none →
      tokenAt .white q.2 = some t' →
      tokenAt .white
          (nextConfig ring C e rsite) =
        some t' →
      (ValidToken .white
          (nextConfig ring C e) rsite ∧
        WorkingFor ring root
          (nextConfig ring C e)
          rsite .white seg.val) →
      ValidToken .white C e ∧
        WorkingFor ring root C e .white seg.val ∧
        PPL.Remark2RightLiteralMotionData
          hpsi ring e rsite t t'

theorem splWhiteOldImageInitiatorMovedRightBranch_of_semantic
    (hsem :
      SPLWhiteOldImageInitiatorMovedRightSemanticRow) :
    SPLWhiteOldImageInitiatorMovedRightBranch := by
  unfold
    SPLWhiteOldImageInitiatorMovedRightSemanticRow
      at hsem
  unfold SPLWhiteOldImageInitiatorMovedRightBranch
  intro _hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg t t'
  dsimp only
  intro hCtok hl0tok hgate
    hrnone hq hpost hVW

  have hs :=
    hsem
      PPL.remark2RightSelectedMirrorRowCorrected_proved
      hn3 hpsi ring root C e hSPL
      seg t t'
      hCtok hl0tok hgate
      hrnone hq hpost hVW
  rcases hs with
    ⟨hvalid, hwork, hliteral⟩

  have hcorr :
      CorrectToken ring root
        C e .white seg.val :=
    ((hSPL.2.2 seg).2 e).2
      ⟨hvalid, hwork⟩

  have hsrc :=
    splWhiteSourceIota_frame
      hn3 hpsi ring root C e hSPL seg.val

  have hpostCDL :=
    splWhiteSeamPostCDL
      hn3 hpsi ring root C e hSPL

  have hmotion :
      PPL.Remark2RightMotionData
        ring root seg.val
        e (ring.rightNeighbor e) t t' :=
    PPL.remark2RightLiteralMotionData_to_motion
      hpsi ring root seg
      C (nextConfig ring C e)
      e (ring.rightNeighbor e)
      .white t t'
      hCtok hpost
      hvalid hwork hcorr
      hSPL.1 hpostCDL hsrc
      rfl hliteral

  exact
    PPL.remark2Right_motion_preserves_correct
      ring root seg
      C (nextConfig ring C e)
      e (ring.rightNeighbor e)
      .white t t'
      hCtok hpost hsrc hcorr hmotion

def SPLWhiteOldImageResponderSemanticRow : Prop :=
  PPL.Remark2LeftSelectedMirrorRow →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        splWhiteSelectedInput
          hpsi (C e) (C rsite)
      let r0 := sourceClear .white p.2
      let q := moveToken hpsi .white p.1 p.2
      let gate :=
        (sourceClear .white p.1).last = false ∧
          r0.last = false
      tokenAt .white (C rsite) = some t →
      tokenAt .white r0 = some t →
      ((¬ gate ∧
          i = rsite ∧
          tokenAt .white q.2 = some t') ∨
        (gate ∧
          ((i = e ∧
              tokenAt .white q.1 = some t') ∨
            (i = rsite ∧
              tokenAt .white q.2 = some t')))) →
      tokenAt .white
          (nextConfig ring C e i) =
        some t' →
      (ValidToken .white
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .white seg.val) →
      ValidToken .white C rsite ∧
        WorkingFor ring root
          C rsite .white seg.val ∧
        ((i = rsite ∧ t' = t) ∨
          (i = e ∧
            decodeOffset psi (tokenCode t) < 0 ∧
            decodeOffset psi (tokenCode t') < 0 ∧
            tokenTargetSite ring e t' =
              tokenTargetSite ring rsite t ∧
            tokenBitBool t' = tokenBitBool t ∧
            tokenCarryBool t' =
              tokenCarryBool t) ∨
          (i = e ∧
            decodeOffset psi (tokenCode t) = -1 ∧
            t' =
              PPL.remark2NegTurnValue
                hpsi (C e).id t))

theorem splWhiteOldImageResponderBranch_of_semantic
    (hsem :
      SPLWhiteOldImageResponderSemanticRow) :
    SPLWhiteOldImageResponderBranch := by
  unfold SPLWhiteOldImageResponderSemanticRow at hsem
  unfold SPLWhiteOldImageResponderBranch
  intro _hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t t'
  dsimp only
  intro hCtok hr0tok hshape hpost hVW

  have hs :=
    hsem
      PPL.remark2LeftSelectedMirrorRow_proved
      hn3 hpsi ring root C e hSPL
      seg i t t'
      hCtok hr0tok hshape hpost hVW
  rcases hs with
    ⟨hvalid, hwork, hcases⟩

  let rsite := ring.rightNeighbor e
  have hcorr :
      CorrectToken ring root
        C rsite .white seg.val :=
    ((hSPL.2.2 seg).2 rsite).2
      ⟨hvalid, hwork⟩

  have hsrc :=
    splWhiteSourceIota_frame
      hn3 hpsi ring root C e hSPL seg.val

  rcases hcases with hstay | hrest

  · rcases hstay with ⟨hir, htt⟩
    subst i
    subst t'
    exact
      PPL.remark2Right_correct_same_occurrence
        ring root seg
        C (nextConfig ring C e)
        rsite .white t
        hCtok hpost hsrc hcorr

  · rcases hrest with hord | hturn

    · rcases hord with
        ⟨hie, hcOld, hcNew,
          htarget, hbit, hcarry⟩
      subst i
      exact
        splWhiteSeamNegativeCorrect
          ring root seg
          C (nextConfig ring C e)
          rsite e t t'
          hCtok hpost
          hcOld hcNew htarget
          hbit hcarry hsrc hcorr

    · rcases hturn with
        ⟨hie, hcneg, hval⟩
      subst i
      have hpostTurn :
          tokenAt .white
              ((nextConfig ring C e) e) =
            some
              (PPL.remark2NegTurnValue
                hpsi (C e).id t) := by
        rw [← hval]
        exact hpost

      have hpostCDL :=
        splWhiteSeamPostCDL
          hn3 hpsi ring root C e hSPL

      exact
        PPL.remark2Row_negTurn_correct
          hpsi ring root seg
          C (nextConfig ring C e)
          e rsite .white t
          rfl rfl hCtok hcneg hpostTurn
          hvalid hwork hcorr
          hSPL.1 hpostCDL hsrc

theorem splAlgorithm23WhiteOldImageRow_of_semanticSeams
    (hInit :
      SPLWhiteOldImageInitiatorMovedRightSemanticRow)
    (hResp :
      SPLWhiteOldImageResponderSemanticRow) :
    SPLAlgorithm23WhiteOldImageRow :=
  splAlgorithm23WhiteOldImageRow_of_branches
    (splWhiteOldImageInitiatorBranch_of_movedRight
      (splWhiteOldImageInitiatorMovedRightBranch_of_semantic
        hInit))
    (splWhiteOldImageResponderBranch_of_semantic hResp)
    splWhiteOldImageOffPairBranch_proved

theorem splAlgorithm23WhiteCorrectnessRow_of_semanticSeams
    (hInit :
      SPLWhiteOldImageInitiatorMovedRightSemanticRow)
    (hResp :
      SPLWhiteOldImageResponderSemanticRow) :
    SPLAlgorithm23WhiteCorrectnessRow :=
  splAlgorithm23WhiteCorrectnessRow_of_caseRows
    (splAlgorithm23WhiteOldImageRow_of_semanticSeams
      hInit hResp)
    splAlgorithm23WhiteFreshBirthRow_proved

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splWhiteOldImageOffPairBranch_proved
#print axioms PPL.Safety.SPL.splAlgorithm23WhiteFreshBirthRow_proved
#print axioms PPL.Safety.SPL.splWhiteOldImageInitiatorMovedRightBranch_of_semantic
#print axioms PPL.Safety.SPL.splWhiteOldImageResponderBranch_of_semantic
#print axioms PPL.Safety.SPL.splAlgorithm23WhiteOldImageRow_of_semanticSeams
#print axioms PPL.Safety.SPL.splAlgorithm23WhiteCorrectnessRow_of_semanticSeams
