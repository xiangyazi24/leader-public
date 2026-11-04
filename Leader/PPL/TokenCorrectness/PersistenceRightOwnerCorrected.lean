import Leader.PPL.TokenCorrectness.PersistenceRightRow
import Leader.PPL.TransitionFacts


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Remark 2 right owner: corrected literal row and semantic assembly


The old Remark2RightOwnerRow put the source-relative c=1 turn equation in
the literal owner row.  That is false without a source segment.  The corrected
literal row below records only the exact turn value when c=1; the source-
relative equation is derived later from CorrectToken at the semantic layer.


The only bounded residual in this file is Remark2RightSelectedMirrorRowCorrected.
It is the finite selected-colour ghostMoveToken/MoveToken pair split and has no
root, segment, WorkingFor, CorrectToken, CDLAt, or sourceIota premise.
-/


/-! ## Corrected public row statement -/


private def rightCorrectedBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def rightCorrectedMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


def remark2RightTurnValue
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi) : TokenData psi :=
  rightCorrectedMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2


def Remark2RightLiteralMotionData
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e j : Fin n)
    (t t' : TokenData psi) : Prop :=
  And
    (tokenBitBool t' = tokenBitBool t)
    (And
      (tokenCarryBool t' = tokenCarryBool t)
      (Or
        (And
          (2 <= decodeOffset psi (tokenCode t))
          (And
            (0 < decodeOffset psi (tokenCode t'))
            (tokenTargetSite ring j t' =
              tokenTargetSite ring e t)))
        (And
          (decodeOffset psi (tokenCode t) = (1 : Int))
          (t' = remark2RightTurnValue hpsi t))))


def Remark2RightOwnerRowCorrected : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G e = some z ->
    forall (j : Fin n) (z' : GhostToken n psi),
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z' ->
      z'.lmeta.id = z.lmeta.id ->
      Or (j = e) (j = ring.rightNeighbor e) ->
      Or
        (And (j = e)
          (And (z'.value = z.value)
            (tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa) ring C e) j) =
              some z'.value)))
        (And (j = ring.rightNeighbor e)
          (And
            (tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa) ring C e) j) =
              some z'.value)
            (Remark2RightLiteralMotionData
              hpsi ring e j z.value z'.value)))


/-! ## Definitionally mirrored selected-colour row -/


private def rightCorrectedLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))


private instance instDecidableRightCorrectedLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (rightCorrectedLocalValid kind q t) := by
  unfold rightCorrectedLocalValid
  infer_instance


private def rightCorrectedPrelude
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let s := createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 :=
    if r0.mode = false then
      { r0 with dist := tmp }
    else
      r0
  let l1 :=
    if r1.leader = true then
      { l0 with last := true }
    else if Or (r1.dist.val = 0)
        (r1.dist.val = psi) then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)


private def rightCorrectedLiveShadow
    {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if And
              (z.value = t)
              (rightCorrectedLocalValid kind q t) then
            some z
          else
            none


private def rightCorrectedLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if rightCorrectedLocalValid kind q t then
        some t
      else
        none


private def rightCorrectedBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      rightCorrectedMkToken
        (offsetPsiCode psi hpsi)
        (rightCorrectedBitToFin (!idBit))
        (rightCorrectedBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def rightCorrectedBumpTo
    {n psi kappa : Nat}
    (kind : TokenKind) (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' : LineageMeta n :=
        { z.lmeta with
          moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if rightCorrectedLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def rightCorrectedGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := rightCorrectedLiveValue kind l
  let rv0 := rightCorrectedLiveValue kind r
  let gl0 := rightCorrectedLiveShadow kind l gl
  let gr0 := rightCorrectedLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (rightCorrectedBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (rightCorrectedBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide :=
      And (lv1 ≠ none) (rv0 ≠ none)
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if h1 : c = 1 then
          let next :=
            rightCorrectedMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            rightCorrectedBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            rightCorrectedMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            rightCorrectedBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some t =>
              let c :=
                decodeOffset psi (tokenCode t)
              if hm1 : c = -1 then
                let next :=
                  if t.2 = (1 : Fin 2) then
                    rightCorrectedMkToken
                      (offsetPsiCode psi hpsi)
                      (rightCorrectedBitToFin (!l.id))
                      (rightCorrectedBitToFin l.id)
                  else
                    rightCorrectedMkToken
                      (offsetPsiCode psi hpsi)
                      (rightCorrectedBitToFin l.id)
                      (0 : Fin 2)
                let b :=
                  rightCorrectedBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  rightCorrectedMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  rightCorrectedBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else
                ⟨gl2, gr0, []⟩
    | none =>
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c :=
              decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                if t.2 = (1 : Fin 2) then
                  rightCorrectedMkToken
                    (offsetPsiCode psi hpsi)
                    (rightCorrectedBitToFin (!l.id))
                    (rightCorrectedBitToFin l.id)
                else
                  rightCorrectedMkToken
                    (offsetPsiCode psi hpsi)
                    (rightCorrectedBitToFin l.id)
                    (0 : Fin 2)
              let b :=
                rightCorrectedBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                rightCorrectedMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                rightCorrectedBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩


private def rightCorrectedSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k


private def rightCorrectedSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := rightCorrectedPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2


private def rightCorrectedSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre :=
    rightCorrectedSelectedInput hpsi kind l r
  moveToken hpsi kind pre.1 pre.2


private def rightCorrectedMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let pre :=
    rightCorrectedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  rightCorrectedGhostMoveToken
    hpsi kind step e
    pre.1 pre.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))


private theorem rightCorrectedGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      rightCorrectedSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (rightCorrectedMovedPair
          hpsi ring step G e kind).left
        (rightCorrectedMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl


/-! ## Public physical-token projection through the whole P_PL row -/


private theorem rightCorrectedElimTokenLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (eliminateLeaders l r).1 =
      tokenAt kind l := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left
      l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, tokenAt]
        using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, tokenAt]
        using ht


private theorem rightCorrectedElimTokenRight
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (eliminateLeaders l r).2 =
      tokenAt kind r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right
      l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, tokenAt]
        using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, tokenAt]
        using ht


private theorem rightCorrectedWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    And
      (tokenAt TokenKind.black
          (moveToken hpsi
            TokenKind.white l r).1 =
        tokenAt TokenKind.black l)
      (tokenAt TokenKind.black
          (moveToken hpsi
            TokenKind.white l r).2 =
        tokenAt TokenKind.black r) := by
  have hi :=
    moveToken_initiator_fields
      hpsi TokenKind.white l r
  have hir :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  refine And.intro ?_ ?_
  · simpa [eraseKindToken, tokenAt]
      using hir
  · rcases
      moveToken_responder_fields
        hpsi TokenKind.white l r with hr | hr
    · have hrr :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          tokenAt]
        using hrr
    · have hrr :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          birthFields, tokenAt]
        using hrr


private theorem rightCorrectedPplTokenPair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      (tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind
          (rightCorrectedSelectedOutput
            hpsi kind l r).1)
      (tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind
          (rightCorrectedSelectedOutput
            hpsi kind l r).2) := by
  cases kind with
  | black =>
      let p := rightCorrectedPrelude hpsi l r
      let b :=
        moveToken hpsi TokenKind.black
          p.1 p.2
      let w :=
        moveToken hpsi TokenKind.white
          b.1 b.2
      have hw :=
        rightCorrectedWhitePreservesBlack
          hpsi b.1 b.2
      have hel :=
        rightCorrectedElimTokenLeft
          TokenKind.black w.1 w.2
      have her :=
        rightCorrectedElimTokenRight
          TokenKind.black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          rightCorrectedSelectedOutput
              hpsi TokenKind.black l r =
            b := by
        rfl
      rw [hfull, hselected]
      exact
        And.intro
          (hel.trans hw.1)
          (her.trans hw.2)
  | white =>
      let p := rightCorrectedPrelude hpsi l r
      let b :=
        moveToken hpsi TokenKind.black
          p.1 p.2
      let w :=
        moveToken hpsi TokenKind.white
          b.1 b.2
      have hel :=
        rightCorrectedElimTokenLeft
          TokenKind.white w.1 w.2
      have her :=
        rightCorrectedElimTokenRight
          TokenKind.white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          rightCorrectedSelectedOutput
              hpsi TokenKind.white l r =
            w := by
        rfl
      rw [hfull, hselected]
      exact And.intro hel her


private theorem rightCorrectedStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    And
      (tokenAt kind
          ((PopulationProtocol.step
            (protocol psi kappa)
            ring C e) e) =
        tokenAt kind
          (rightCorrectedSelectedOutput
            hpsi kind
            (C e)
            (C (ring.rightNeighbor e))).1)
      (tokenAt kind
          ((PopulationProtocol.step
            (protocol psi kappa)
            ring C e)
            (ring.rightNeighbor e)) =
        tokenAt kind
          (rightCorrectedSelectedOutput
            hpsi kind
            (C e)
            (C (ring.rightNeighbor e))).2) := by
  have hne :
      ring.rightNeighbor e ≠ e :=
    remark2Right_rightNeighbor_ne_self
      hn3 ring e
  have hp :=
    rightCorrectedPplTokenPair
      hpsi kind
      (C e)
      (C (ring.rightNeighbor e))
  have hl :
      PopulationProtocol.step
          (protocol psi kappa)
          ring C e e =
        (ppl hpsi
          (C e)
          (C (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      PopulationProtocol.step
          (protocol psi kappa)
          ring C e
          (ring.rightNeighbor e) =
        (ppl hpsi
          (C e)
          (C (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    And.intro
      (by rw [hl]; exact hp.1)
      (by rw [hr]; exact hp.2)


/-!
Exact finite residual: the selected-colour ghost shadow starts with the tracked
initiator lineage literally equal to some z.  A same-ID survivor is either the
same left owner, or the right bump with the corrected literal motion data.
The two hypotheses are precisely the old-responder and same-step-birth
anti-alias facts supplied by GhostIdsUniqueAt.
-/
def Remark2RightSelectedMirrorRowCorrected : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi),
    (forall (zr : GhostToken n psi),
      gr = some zr ->
      zr.lmeta.id ≠ z.lmeta.id) ->
    z.lmeta.id ≠ .born kind step ->
    forall (z' : GhostToken n psi),
      And
        ((rightCorrectedGhostMoveToken
              hpsi kind step e
              l r (some z) gr).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).1 =
              some z.value))
        ((rightCorrectedGhostMoveToken
              hpsi kind step e
              l r (some z) gr).right =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (tokenAt kind
                (moveToken hpsi kind l r).2 =
              some z'.value)
            (Remark2RightLiteralMotionData
              hpsi ring e (ring.rightNeighbor e)
              z.value z'.value))


/-! ## Lift the finite selected-colour split to the corrected owner row -/


theorem remark2RightOwnerRowCorrected_proved
    (hlocal : Remark2RightSelectedMirrorRowCorrected) :
    Remark2RightOwnerRowCorrected := by
  unfold Remark2RightOwnerRowCorrected
  intro n psi kappa hpsi hn3
  intro ring step C e G kind z
  intro hphys _hG huniq howner
  subst C
  intro j z' hpost hid hj


  have hne :
      ring.rightNeighbor e ≠ e :=
    remark2Right_rightNeighbor_ne_self
      hn3 ring e


  have hNoRight :
      forall (zr : GhostToken n psi),
        ghostTokenAt kind G
            (ring.rightNeighbor e) =
          some zr ->
        zr.lmeta.id ≠ z.lmeta.id := by
    intro zr hr
    exact
      remark2Right_no_responder_alias
        hn3 ring step G kind e z zr
        huniq howner hr


  have hOldNotFresh :
      z.lmeta.id ≠ .born kind step :=
    remark2Right_tracked_ne_sameStepBirth
      step G kind e z huniq howner


  let p :=
    rightCorrectedSelectedInput
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))


  have hstep :=
    rightCorrectedStepTokenPair
      hpsi hn3 ring G.phys e kind


  have hselected :
      rightCorrectedSelectedOutput
          hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e)) =
        moveToken hpsi kind p.1 p.2 := by
    rfl
  rw [hselected] at hstep


  rw [rightCorrectedGhostTokenAtStep
    hpsi ring step G e kind j] at hpost


  have hrow :=
    hlocal hpsi ring step e kind
      p.1 p.2
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z hNoRight hOldNotFresh z'


  rcases hj with hje | hjr
  · subst j
    have hlive :
        (rightCorrectedGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (some z)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).left =
          some z' := by
      have hp := hpost
      simp only
        [rightCorrectedSetTwo, if_pos rfl]
        at hp
      change
        (rightCorrectedMovedPair
          hpsi ring step G e kind).left =
            some z' at hp
      change
        (rightCorrectedGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).left =
            some z' at hp
      rw [howner] at hp
      exact hp


    have hstay :=
      hrow.1 hlive hid
    rcases hstay with ⟨hzz, htok⟩
    subst z'


    have htok' :
        tokenAt kind
            ((PopulationProtocol.step
              (protocol psi kappa)
              ring G.phys e) e) =
          some z.value := by
      rw [hstep.1]
      exact htok


    exact
      Or.inl
        (And.intro rfl
          (And.intro rfl htok'))


  · subst j
    have hlive :
        (rightCorrectedGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (some z)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).right =
          some z' := by
      have hp := hpost
      simp only
        [rightCorrectedSetTwo,
          if_neg hne, if_pos rfl] at hp
      change
        (rightCorrectedMovedPair
          hpsi ring step G e kind).right =
            some z' at hp
      change
        (rightCorrectedGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).right =
            some z' at hp
      rw [howner] at hp
      exact hp


    have hmove :=
      hrow.2 hlive hid
    rcases hmove with ⟨htok, hdata⟩


    have htok' :
        tokenAt kind
            ((PopulationProtocol.step
              (protocol psi kappa)
              ring G.phys e)
              (ring.rightNeighbor e)) =
          some z'.value := by
      rw [hstep.2]
      exact htok


    exact
      Or.inr
        (And.intro rfl
          (And.intro htok' hdata))


/-! ## Public cyclic geometry for the c=1 turn -/


private theorem rightCorrected_shiftRight_add
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (a b : Nat) :
    shiftRight ring (shiftRight ring i a) b =
      shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem rightCorrected_cyclicOffset_shiftRight_of_lt
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) :
    cyclicOffset ring i (shiftRight ring i d) = d := by
  unfold cyclicOffset shiftRight
  change
    (((i.val + d) % n + n - i.val) % n) = d
  have hi : i.val < n := i.isLt
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - i.val = n + d := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt hd]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - i.val = d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]


private theorem rightCorrected_shiftRight_cyclicOffset
    {n : Nat} (ring : DirectedRing n)
    (a b : Fin n) :
    shiftRight ring a
        (cyclicOffset ring a b) = b := by
  apply Fin.ext
  change
    (a.val +
        ((b.val + n - a.val) % n)) % n =
      b.val
  by_cases hab : a.val <= b.val
  · have heq :
        b.val + n - a.val =
          n + (b.val - a.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt
        (by omega : b.val - a.val < n)]
    have hsum :
        a.val + (b.val - a.val) = b.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt b.isLt]
  · have hlt :
        b.val + n - a.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        a.val + (b.val + n - a.val) =
          b.val + n := by
      omega
    rw [hsum, Nat.add_mod_right,
      Nat.mod_eq_of_lt b.isLt]


private theorem rightCorrected_shiftLeft_shiftRight_sub
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d k : Nat)
    (hk : k <= d) (hd : d < n) :
    shiftLeft ring (shiftRight ring i d) k =
      shiftRight ring i (d - k) := by
  apply Fin.ext
  unfold shiftLeft shiftRight
  change
    (((i.val + d) % n + n - k % n) % n) =
      (i.val + (d - k)) % n
  have hklt : k < n := by
    exact Nat.lt_of_le_of_lt hk hd
  rw [Nat.mod_eq_of_lt hklt]
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - k =
          n + (i.val + (d - k)) := by
      omega
    rw [heq, Nat.add_mod_left]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - k =
          i.val + (d - k) := by
      omega
    rw [heq]


private theorem rightCorrected_interior_pair_fits
    {n psi : Nat}
    (hpsi : 0 < psi)
    (seg : Fin (segmentCount n psi - 2)) :
    2 * psi < n := by
  have hz : 3 <= segmentCount n psi := by
    have hs := seg.isLt
    omega
  unfold segmentCount at hz
  have hmul :
      3 * psi <= n + psi - 1 :=
    (Nat.le_div_iff_mul_le hpsi).mp hz
  omega


private theorem rightCorrected_old_target_one
    {n psi : Nat}
    (ring : DirectedRing n)
    (e : Fin n) (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) = (1 : Int)) :
    tokenTargetSite ring e t =
      ring.rightNeighbor e := by
  have h :
      tokenTargetSite ring e t =
        shiftRight ring e 1 := by
    unfold tokenTargetSite
    rw [hc]
    simp
  exact h


private theorem rightCorrected_turn_decode
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (remark2RightTurnValue hpsi t)) =
      1 - ((psi : Nat) : Int) := by
  exact decodeOffset_negPsiPlusOne psi hpsi


private theorem rightCorrected_turn_target
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (j : Fin n) (t : TokenData psi) :
    tokenTargetSite ring j
        (remark2RightTurnValue hpsi t) =
      shiftLeft ring j (psi - 1) := by
  unfold tokenTargetSite
  rw [rightCorrected_turn_decode hpsi t]
  have hnpos :
      Not (0 < (1 - ((psi : Nat) : Int))) := by
    omega
  rw [if_neg hnpos]
  have hz :
      1 - ((psi : Nat) : Int) =
        -(((psi - 1 : Nat) : Int)) := by
    omega
  rw [hz]
  simp


private theorem rightCorrected_turn_coordinate
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C : Config n psi kappa)
    (e j : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (ht : tokenAt kind (C e) = some t)
    (hc :
      decodeOffset psi (tokenCode t) = (1 : Int))
    (hjr : j = ring.rightNeighbor e)
    (hcorr :
      CorrectToken ring root C e kind seg.val) :
    cyclicOffset ring
        (sourceStart psi ring root seg.val)
        (tokenTargetSite ring j
          (remark2RightTurnValue hpsi t)) =
      cyclicOffset ring
          (sourceStart psi ring root seg.val)
          (tokenTargetSite ring e t) -
        psi + 1 := by
  let source :=
    sourceStart psi ring root seg.val
  let oldTarget :=
    tokenTargetSite ring e t
  let rel :=
    cyclicOffset ring source oldTarget


  have holdTarget :
      oldTarget = ring.rightNeighbor e := by
    dsimp [oldTarget]
    exact
      rightCorrected_old_target_one
        ring e t hc


  have hjold : j = oldTarget := by
    exact hjr.trans holdTarget.symm


  have hcorr0 := hcorr
  unfold CorrectToken at hcorr0
  rw [ht] at hcorr0
  dsimp only at hcorr0
  rw [hc, if_pos (by omega)] at hcorr0
  rcases hcorr0 with
    ⟨_hparity, hrelGe, hx, _hpay⟩


  have hrelGe' : psi <= rel := by
    simpa only [source, oldTarget, rel, sourceStart]
      using hrelGe
  have hx' : rel - psi < psi := by
    simpa only [source, oldTarget, rel, sourceStart]
      using hx
  have hrelLt : rel < 2 * psi := by
    omega


  have hfit :
      2 * psi < n :=
    rightCorrected_interior_pair_fits
      (by omega) seg
  have hrelN : rel < n := by
    omega
  have hk : psi - 1 <= rel := by
    omega


  have hsiteOld :
      shiftRight ring source rel = oldTarget :=
    rightCorrected_shiftRight_cyclicOffset
      ring source oldTarget


  let d := rel - (psi - 1)
  have hdEq :
      d = rel - psi + 1 := by
    dsimp [d]
    omega
  have hdN : d < n := by
    dsimp [d]
    omega


  have hnewSite :
      tokenTargetSite ring j
          (remark2RightTurnValue hpsi t) =
        shiftRight ring source d := by
    rw [rightCorrected_turn_target
      hpsi ring j t]
    rw [hjold]
    rw [← hsiteOld]
    change
      shiftLeft ring
          (shiftRight ring source rel)
          (psi - 1) =
        shiftRight ring source d
    rw [rightCorrected_shiftLeft_shiftRight_sub
      ring source rel (psi - 1) hk hrelN]


  calc
    cyclicOffset ring source
        (tokenTargetSite ring j
          (remark2RightTurnValue hpsi t)) =
      d := by
        rw [hnewSite]
        exact
          rightCorrected_cyclicOffset_shiftRight_of_lt
            ring source d hdN
    _ = rel - psi + 1 := hdEq
    _ =
      cyclicOffset ring source
          (tokenTargetSite ring e t) -
        psi + 1 := by
          rfl


/-!
Semantic upgrade of the corrected literal data.  The ordinary c>=2 branch
only rewrites the preserved target.  The c=1 branch uses CorrectToken to place
the old target in source-relative coordinates and the preceding finite-ring
lemma to subtract psi-1 even when the right move crosses n-1 -> 0.
-/
theorem remark2RightLiteralMotionData_to_motion
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (e j : Fin n)
    (kind : TokenKind)
    (t t' : TokenData psi)
    (ht : tokenAt kind (C e) = some t)
    (_ht' : tokenAt kind (C' j) = some t')
    (_hvalid : ValidToken kind C e)
    (_hwork :
      WorkingFor ring root C e kind seg.val)
    (hcorr :
      CorrectToken ring root C e kind seg.val)
    (_hC : CDLAt ring root C)
    (_hC' : CDLAt ring root C')
    (_hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hjr : j = ring.rightNeighbor e)
    (hdata :
      Remark2RightLiteralMotionData
        hpsi ring e j t t') :
    Remark2RightMotionData
      ring root seg.val e j t t' := by
  rcases hdata with
    ⟨hbit, hcarry, hord | hturn⟩
  · rcases hord with
      ⟨hc2, hnewPos, htarget⟩
    refine
      And.intro hbit
        (And.intro hcarry
          (Or.inl ?_))
    refine
      And.intro (by omega)
        (And.intro hnewPos ?_)
    rw [htarget]
  · rcases hturn with
      ⟨hc1, hvalue⟩
    subst t'
    have hnewNeg :
        decodeOffset psi
            (tokenCode
              (remark2RightTurnValue hpsi t)) < 0 := by
      rw [rightCorrected_turn_decode hpsi t]
      omega
    have hcoord :=
      rightCorrected_turn_coordinate
        hpsi ring root seg C
        e j kind t ht hc1 hjr hcorr
    refine
      And.intro hbit
        (And.intro hcarry
          (Or.inr ?_))
    exact
      And.intro hc1
        (And.intro hnewNeg hcoord)


/-! ## Re-derive the selected semantic row -/


theorem remark2RightSelectedRow_of_corrected
    (hrow : Remark2RightOwnerRowCorrected) :
    Remark2RightSelectedRow := by
  unfold Remark2RightSelectedRow
  intro n psi kappa hpsi hn3
  intro ring root seg step C e G kind z
  intro hphys hG huniq howner
  intro hvalid hwork hcorr hC hC'
  intro j z' hsrc hpost hid hj


  have htok0 :
      tokenAt kind (C e) = some z.value :=
    remark2Right_ghostSound_token
      C G kind e z hphys hG howner


  have hout :=
    hrow hpsi hn3 ring
      step C e G kind z
      hphys hG huniq howner
      j z' hpost hid hj


  rcases hout with hstay | hmove
  · rcases hstay with
      ⟨hje, hvalue, htok1⟩
    subst j
    rw [hvalue] at htok1
    exact
      remark2Right_correct_same_occurrence
        ring root seg
        C
        (PopulationProtocol.step
          (protocol psi kappa) ring C e)
        e kind z.value
        htok0 htok1 hsrc hcorr


  · rcases hmove with
      ⟨hjr, htok1, hliteral⟩
    have hmotion :=
      remark2RightLiteralMotionData_to_motion
        hpsi ring root seg
        C
        (PopulationProtocol.step
          (protocol psi kappa) ring C e)
        e j kind z.value z'.value
        htok0 htok1
        hvalid hwork hcorr hC hC'
        hsrc hjr hliteral
    exact
      remark2Right_motion_preserves_correct
        ring root seg
        C
        (PopulationProtocol.step
          (protocol psi kappa) ring C e)
        e j kind z.value z'.value
        htok0 htok1 hsrc hcorr hmotion


theorem remark2RightSelectedRow_proved
    (hlocal : Remark2RightSelectedMirrorRowCorrected) :
    Remark2RightSelectedRow :=
  remark2RightSelectedRow_of_corrected
    (remark2RightOwnerRowCorrected_proved hlocal)


end PPL


#print axioms PPL.remark2RightOwnerRowCorrected_proved
#print axioms PPL.remark2RightLiteralMotionData_to_motion
#print axioms PPL.remark2RightSelectedRow_proved


