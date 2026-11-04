import Leader.PPL.TokenCompletion.SweepOldOwnerRows
import Leader.PPL.TokenCompletion.SweepInitiatorSameId
import Leader.PPL.TokenCompletion.SweepResponder
import Leader.PPL.TokenCompletion.SweepResponderNegTurn
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
Interacted old-owner rows of the Lemma 4 sweep.

The two interacted rows (initiator / responder owner) are closed here by the
same literal ghostMoveToken case tree as the fresh same-ID sweep rows.  The
compiled same-ID row proofs in TokenCorrectnessLemma4SweepInitiatorArrival,
TokenCorrectnessLemma4SweepInitiatorRows and
TokenCorrectnessLemma4SweepResponderSameId never used their
Lemma4FreshKinematics premise and always exited through the survivor
disjunct, never through HasFreshCompletion.  Their private mirror families are
copied below under new prefixes; the row proofs are re-stated without the
kinematics premise and without the completion escape.

The old-owner rows then split on whether either selected-pair output still
carries the tracked lineage:
* yes: the survivor is placed in the post ghost map by the public site
  equations of TokenCorrectnessLemma4GhostStepExport;
* no: the lineage is deleted; off-pair sites keep their owners literally and
  ID uniqueness rules them out.
-/


/-! ## Mirror family A (copied from TokenCorrectnessLemma4SweepInitiatorArrival, prefix ooArr) -/

private def ooArrBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def ooArrMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def ooArrLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
        target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
        target ≤ (((psi - 1 : Nat)) : Int))

private instance instDecidableOoArrLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (ooArrLocalValid kind q t) := by
  unfold ooArrLocalValid
  infer_instance

private def ooArrSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def ooArrClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if ooArrLocalValid kind q t then
        q
      else
        ooArrSetToken kind q none

private def ooArrLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private theorem ooArrSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      ooArrSetToken kind q t := by
  cases kind <;> rfl

private theorem ooArrSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      ooArrClearInvalid kind q := by
  cases kind <;> rfl

private theorem ooArrSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = ooArrLeaderBirth q := by
  rfl

private def ooArrNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    ooArrMkToken
      (offsetPsiCode psi hpsi)
      (ooArrBitToFin (!sourceBit))
      (ooArrBitToFin sourceBit)
  else
    ooArrMkToken
      (offsetPsiCode psi hpsi)
      (ooArrBitToFin sourceBit)
      (0 : Fin 2)

private def ooArrMoveToken
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := sourceClear kind l
  let r := sourceClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧
          tokenAt kind l = none then
        sourceSet kind l
          (some
            (ooArrMkToken
              (offsetPsiCode psi hpsi)
              (ooArrBitToFin (!l.id))
              (ooArrBitToFin l.id)))
      else
        l
    let l :=
      if tokenAt kind l ≠ none ∧
          tokenAt kind r ≠ none then
        sourceSet kind l none
      else
        l
    let moveLeft :=
      fun (l r : State psi kappa) =>
        match tokenAt kind r with
        | none => (l, r)
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                ooArrNegTurnNext hpsi l.id t
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let nextOffset :=
                encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega)
              (sourceSet kind l
                  (some
                    (ooArrMkToken
                      nextOffset t.1.2 t.2)),
                sourceSet kind r none)
            else
              (l, r)
    match tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if hc1 : c = 1 then
          let bit := tokenBitBool t
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          (sourceSet kind l none,
            sourceSet kind r
              (some
                (ooArrMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2)))
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let nextOffset :=
            encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega)
          (sourceSet kind l none,
            sourceSet kind r
              (some
                (ooArrMkToken
                  nextOffset t.1.2 t.2)))
        else
          moveLeft l r
  else
    (l, r)

private theorem ooArrMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    ooArrMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl

private def ooArrLiveShadow
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if z.value = t ∧
              ooArrLocalValid kind q t then
            some z
          else
            none

private def ooArrLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if ooArrLocalValid kind q t then
        some t
      else
        none

private def ooArrBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      ooArrMkToken
        (offsetPsiCode psi hpsi)
        (ooArrBitToFin (!idBit))
        (ooArrBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def ooArrBumpTo
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' := ghostStepLineageAdvance z.lmeta
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if ooArrLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def ooArrGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := ooArrLiveValue kind l
  let rv0 := ooArrLiveValue kind r
  let gl0 := ooArrLiveShadow kind l gl
  let gr0 := ooArrLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ooArrBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ooArrBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if h1 : c = 1 then
          let next :=
            ooArrMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            ooArrBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            ooArrMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            ooArrBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some tr =>
              let cr := decodeOffset psi (tokenCode tr)
              if hm1 : cr = -1 then
                let next :=
                  ooArrNegTurnNext hpsi l.id tr
                let b :=
                  ooArrBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : cr ≤ -2 then
                have hc : ValidOffset psi cr :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode tr)
                let next :=
                  ooArrMkToken
                    (encodeOffset psi (cr + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    tr.1.2 tr.2
                let b :=
                  ooArrBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else
                ⟨gl2, gr0, []⟩
    | none =>
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                ooArrNegTurnNext hpsi l.id tr
              let b :=
                ooArrBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                ooArrMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                ooArrBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def ooArrPrelude
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
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
    else if r1.dist.val = 0 ∨
        r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def ooArrSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := ooArrPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2

private def ooArrSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := ooArrSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2

private def ooArrSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    ooArrSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  ooArrGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem ooArrSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ooArrSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

/-! ## Physical suffix frames -/

private theorem ooArrMoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.dist = l.dist ∧
      (moveToken hpsi kind l r).1.last = l.last ∧
      (moveToken hpsi kind l r).2.dist = r.dist ∧
      (moveToken hpsi kind l r).2.last = r.last := by
  have hi :=
    moveToken_initiator_fields hpsi kind l r
  rcases moveToken_responder_fields hpsi kind l r with
    hr | hr
  · cases kind <;>
      simp_all [eraseKindToken, eraseKindTokenId]
  · cases kind <;>
      simp_all
        [eraseKindToken, eraseKindTokenId, birthFields]

private theorem ooArrElimTokenPair
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (eliminateLeaders l r).1 =
        tokenAt kind l ∧
      tokenAt kind (eliminateLeaders l r).2 =
        tokenAt kind r := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  cases kind with
  | black =>
      constructor
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenB) hl
        simpa [PPL.Elim.otherView, tokenAt] using h
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenB) hr
        simpa [PPL.Elim.otherView, tokenAt] using h
  | white =>
      constructor
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenW) hl
        simpa [PPL.Elim.otherView, tokenAt] using h
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenW) hr
        simpa [PPL.Elim.otherView, tokenAt] using h

private theorem ooArrElimDistLast
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (eliminateLeaders l r).1.dist = l.dist ∧
      (eliminateLeaders l r).1.last = l.last ∧
      (eliminateLeaders l r).2.dist = r.dist ∧
      (eliminateLeaders l r).2.last = r.last := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    ⟨congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hr,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hr⟩

private theorem ooArrWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black (moveToken hpsi .white l r).1 =
        tokenAt .black l ∧
      tokenAt .black (moveToken hpsi .white l r).2 =
        tokenAt .black r := by
  have hi :=
    moveToken_initiator_fields
      hpsi TokenKind.white l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  constructor
  · simpa [eraseKindToken, tokenAt] using hil
  · rcases
      moveToken_responder_fields
        hpsi TokenKind.white l r with hr | hr
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken, tokenAt]
        using h
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          birthFields, tokenAt]
        using h

private theorem ooArrPplSelectedTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind
          (ooArrSelectedOutput
            hpsi kind l r).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind
          (ooArrSelectedOutput
            hpsi kind l r).2 := by
  cases kind with
  | black =>
      let p := ooArrPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        ooArrWhitePreservesBlack
          hpsi b.1 b.2
      have he :=
        ooArrElimTokenPair .black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooArrSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact ⟨he.1.trans hw.1, he.2.trans hw.2⟩
  | white =>
      let p := ooArrPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        ooArrElimTokenPair .white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooArrSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem ooArrPplSelectedDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (ppl hpsi l r).1.dist =
        (ooArrSelectedOutput
          hpsi kind l r).1.dist ∧
      (ppl hpsi l r).1.last =
        (ooArrSelectedOutput
          hpsi kind l r).1.last ∧
      (ppl hpsi l r).2.dist =
        (ooArrSelectedOutput
          hpsi kind l r).2.dist ∧
      (ppl hpsi l r).2.last =
        (ooArrSelectedOutput
          hpsi kind l r).2.last := by
  cases kind with
  | black =>
      let p := ooArrPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        ooArrMoveTokenDistLast
          hpsi .white b.1 b.2
      have he :=
        ooArrElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooArrSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact
        ⟨he.1.trans hw.1,
          he.2.1.trans hw.2.1,
          he.2.2.1.trans hw.2.2.1,
          he.2.2.2.trans hw.2.2.2⟩
  | white =>
      let p := ooArrPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        ooArrElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooArrSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem ooArrStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys e) =
      tokenAt kind
        (ooArrSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 ∧
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)) =
      tokenAt kind
        (ooArrSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
  have hp :=
    ooArrPplSelectedTokenPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      (ghostStep hpsi ring step G e).phys e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  rw [hl, hr]
  exact hp

private theorem ooArrStepDistLast
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ((ghostStep hpsi ring step G e).phys e).dist =
        (ooArrSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.dist ∧
      ((ghostStep hpsi ring step G e).phys e).last =
        (ooArrSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.last ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        (ooArrSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.dist ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).last =
        (ooArrSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.last := by
  have hp :=
    ooArrPplSelectedDistLast
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      (ghostStep hpsi ring step G e).phys e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  rw [hl, hr]
  exact hp

/-! ## Ring and validity arithmetic -/

private theorem ooArrCd_two_le_n
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 ≤ n := by
  by_cases hn2 : 2 ≤ n
  · exact hn2
  · have hn0 : 0 < n := ring.hn
    have hn1 : n = 1 := by
      omega
    subst n
    let x0 : Fin (2 * psi) := ⟨0, by omega⟩
    let x1 : Fin (2 * psi) := ⟨1, by omega⟩
    have h0 := (hCd x0).1
    have h1 := (hCd x1).1
    dsimp only [x0, x1] at h0 h1
    have hs :
        shiftRight ring k 0 =
          shiftRight ring k 1 := by
      apply Fin.ext
      simp [shiftRight]
    rw [hs] at h0
    cases kind with
    | black =>
        have hm1 :
            1 % (2 * psi) = 1 :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm1] at h0 h1
        omega
    | white =>
        have hm0 :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        have hm1 :
            (1 + psi) % (2 * psi) =
              1 + psi :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm0, hm1] at h0 h1
        omega

private theorem ooArrRightNeighbor_ne
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem ooArrRightNeighbor_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (d : Nat) :
    ring.rightNeighbor (shiftRight ring k d) =
      shiftRight ring k (d + 1) := by
  apply Fin.ext
  simp only
    [DirectedRing.rightNeighbor, shiftRight]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem ooArrGhostSoundAt
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧
      ooArrLocalValid
        kind (G.phys i) z.value := by
  cases kind with
  | black =>
      exact hsound.1 i z howner
  | white =>
      exact hsound.2 i z howner

private theorem ooArrLastDistPlusD
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi)) :
    q.dist.val + tokenD' psi kind =
      2 * psi - 1 := by
  cases kind with
  | black =>
      simp only [tokenD'] at hdist ⊢
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt
          (by omega :
            2 * psi - 1 < 2 * psi)] at hdist
      omega
  | white =>
      simp only [tokenD'] at hdist ⊢
      have hge :
          2 * psi ≤ 2 * psi - 1 + psi := by
        omega
      have hlt :
          2 * psi - 1 + psi - 2 * psi <
            2 * psi := by
        omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt hlt] at hdist
      omega

private theorem ooArrLastPositiveTargetBelow
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    tokenTargetCoordinate kind q t <
      ((psi : Nat) : Int) := by
  have hsum :=
    ooArrLastDistPlusD
      hpsi kind q hdist
  have hsumInt :
      (((q.dist.val + tokenD' psi kind :
        Nat)) : Int) =
        (((2 * psi - 1 : Nat)) : Int) :=
    congrArg (fun a : Nat => (a : Int)) hsum
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hpos hv
      simp only [Int.ofNat_eq_natCast] at hpos hv
      have hm :
          1 ≤ m ∧ m ≤ psi := by
        rcases hv with hn | hp <;> omega
      have hnum :
          ((q.dist.val : Nat) : Int) +
                ((m : Nat) : Int) +
                ((tokenD' psi kind : Nat) : Int) =
            (((2 * psi - 1 + m : Nat)) : Int) := by
        simp only [Int.natCast_add] at hsumInt
        omega
      unfold tokenTargetCoordinate
      rw [hc]
      simp only [Int.ofNat_eq_natCast]
      rw [hnum]
      change
        ((((2 * psi - 1 + m) % (2 * psi) :
          Nat)) : Int) <
          ((psi : Nat) : Int)
      have hge :
          2 * psi ≤ 2 * psi - 1 + m := by
        omega
      rw [Nat.mod_eq_sub_mod hge]
      have heq :
          2 * psi - 1 + m - 2 * psi =
            m - 1 := by
        omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
      exact_mod_cast (show m - 1 < psi by omega)
  | negSucc m =>
      rw [hc] at hpos
      omega

private theorem ooArrPositiveNotLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hlocal :
      ooArrLocalValid kind q t)
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    False := by
  have ht :=
    ooArrLastPositiveTargetBelow
      hpsi kind q t hdist hpos
  unfold ooArrLocalValid at hlocal
  dsimp only at hlocal
  rcases hlocal with hp | hn <;> omega

private theorem ooArrValidToken_of_local
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (i : Fin n)
    (q : State psi kappa)
    (t : TokenData psi)
    (htok :
      tokenAt kind (C i) = some t)
    (hdist :
      (C i).dist = q.dist)
    (hlocal :
      ooArrLocalValid kind q t) :
    ValidToken kind C i := by
  unfold ValidToken
  rw [htok]
  unfold ooArrLocalValid at hlocal
  unfold tokenTargetCoordinate at hlocal ⊢
  rw [hdist]
  exact hlocal

private theorem ooArrFresh_advance
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n)
    (hfresh : FreshAt kind k m) :
    FreshAt kind k (ghostStepLineageAdvance m) := by
  rcases hfresh with ⟨t, hid, hsite⟩
  exact
    ⟨t,
      by simpa [ghostStepLineageAdvance] using hid,
      by simpa [ghostStepLineageAdvance] using hsite⟩

/-! ## The c = 1 arrival classifier -/

private def ooArrBounceNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) : TokenData psi :=
  ooArrMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2

private theorem ooArrClass
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      decodeOffset psi (tokenCode z.value) = (1 : Int)) :
    ∀ z' : GhostToken n psi,
      ((ooArrGhostMoveToken
            hpsi kind step site
            l r (some z) gr).left =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        False) ∧
      ((ooArrGhostMoveToken
            hpsi kind step site
            l r (some z) gr).right =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        z'.lmeta =
            ghostStepLineageAdvance z.lmeta ∧
          z'.value =
            ooArrBounceNext hpsi z.value ∧
          ooArrLocalValid kind r z'.value ∧
          tokenAt kind
              (moveToken hpsi kind l r).2 =
            some z'.value) := by
  classical

  let noId : Option (GhostToken n psi) → Prop :=
    fun g =>
      ∀ u : GhostToken n psi,
        g = some u →
        u.lmeta.id = z.lmeta.id →
        False

  let finish :
      Option (TokenData psi) →
        Option (TokenData psi) →
        Option (GhostToken n psi) →
        Option (GhostToken n psi) →
        GhostMoveResult n psi :=
    fun lv2 rv0 gl2 gr0 =>
      match lv2 with
      | some t =>
          let c := decodeOffset psi (tokenCode t)
          if h1 : c = 1 then
            let next :=
              ooArrMkToken
                (offsetNegPsiPlusOneCode psi hpsi)
                t.1.2 t.2
            let b :=
              ooArrBumpTo kind r next gl2
            ⟨none, b.live, b.done⟩
          else if h2 : 2 ≤ c then
            have hvalid : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              ooArrMkToken
                (encodeOffset psi (c - 1) (by
                  rcases hvalid with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
                t.1.2 t.2
            let b :=
              ooArrBumpTo kind r next gl2
            ⟨none, b.live, b.done⟩
          else
            match rv0 with
            | none =>
                ⟨gl2, gr0, []⟩
            | some tr =>
                let cr :=
                  decodeOffset psi (tokenCode tr)
                if hm1 : cr = -1 then
                  let next :=
                    ooArrNegTurnNext hpsi l.id tr
                  let b :=
                    ooArrBumpTo kind l next gr0
                  ⟨b.live, none, b.done⟩
                else if hm2 : cr ≤ -2 then
                  have hvalid : ValidOffset psi cr :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    ooArrMkToken
                      (encodeOffset psi (cr + 1) (by
                        rcases hvalid with hn | hp
                        · left
                          omega
                        · exfalso
                          omega))
                      tr.1.2 tr.2
                  let b :=
                    ooArrBumpTo kind l next gr0
                  ⟨b.live, none, b.done⟩
                else
                  ⟨gl2, gr0, []⟩
      | none =>
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some tr =>
              let cr :=
                decodeOffset psi (tokenCode tr)
              if hm1 : cr = -1 then
                let next :=
                  ooArrNegTurnNext hpsi l.id tr
                let b :=
                  ooArrBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : cr ≤ -2 then
                have hvalid : ValidOffset psi cr :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode tr)
                let next :=
                  ooArrMkToken
                    (encodeOffset psi (cr + 1) (by
                      rcases hvalid with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    tr.1.2 tr.2
                let b :=
                  ooArrBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else
                ⟨gl2, gr0, []⟩

  have hNoNone : noId none := by
    intro u hu _
    cases hu

  have hShadowNoId :
      ∀ (q : State psi kappa)
        (g : Option (GhostToken n psi)),
        noId g →
        noId (ooArrLiveShadow kind q g) := by
    intro q g hg u hu hid
    cases g with
    | none =>
        simp [ooArrLiveShadow] at hu
    | some g0 =>
        cases ht : tokenAt kind q with
        | none =>
            simp [ooArrLiveShadow, ht] at hu
        | some t =>
            by_cases hv :
                g0.value = t ∧
                  ooArrLocalValid kind q t
            · have hgu : g0 = u := by
                simpa [ooArrLiveShadow, ht, hv]
                  using hu
              subst u
              exact hg g0 rfl hid
            · simp [ooArrLiveShadow, ht, hv] at hu

  have hSourceShadow :
      ∀ u : GhostToken n psi,
        ooArrLiveShadow kind l (some z) = some u →
        u = z ∧
          ooArrLiveValue kind l = some z.value := by
    intro u hu
    cases ht : tokenAt kind l with
    | none =>
        simp [ooArrLiveShadow, ht] at hu
    | some t =>
        by_cases hv :
            z.value = t ∧
              ooArrLocalValid kind l t
        · have hzu : z = u := by
            simpa [ooArrLiveShadow, ht, hv]
              using hu
          subst u
          constructor
          · rfl
          · unfold ooArrLiveValue
            simp [ht, hv.1, hv.2]
        · simp [ooArrLiveShadow, ht, hv] at hu

  have hBumpNoId :
      ∀ (q : State psi kappa)
        (v : TokenData psi)
        (g : Option (GhostToken n psi)),
        noId g →
        noId (ooArrBumpTo kind q v g).live := by
    intro q v g hg u hu hid
    cases g with
    | none =>
        simp [ooArrBumpTo] at hu
    | some g0 =>
        by_cases hv :
            ooArrLocalValid kind q v
        · simp only
            [ooArrBumpTo, if_pos hv,
              Option.some.injEq] at hu
          subst u
          have hid0 :
              g0.lmeta.id = z.lmeta.id := by
            simpa [ghostStepLineageAdvance]
              using hid
          exact hg g0 rfl hid0
        · simp [ooArrBumpTo, hv] at hu

  have hBumpSome :
      ∀ (q : State psi kappa)
        (v : TokenData psi)
        (g u : GhostToken n psi),
        (ooArrBumpTo kind q v (some g)).live =
            some u →
        u.lmeta =
            ghostStepLineageAdvance g.lmeta ∧
          u.value = v ∧
          ooArrLocalValid kind q v := by
    intro q v g u hu
    by_cases hv :
        ooArrLocalValid kind q v
    · simp only
        [ooArrBumpTo, if_pos hv,
          Option.some.injEq] at hu
      subst u
      exact ⟨rfl, rfl, hv⟩
    · simp [ooArrBumpTo, hv] at hu

  have hFinishNoId :
      ∀ (lv rv : Option (TokenData psi))
        (gl gr0 : Option (GhostToken n psi)),
        noId gl →
        noId gr0 →
        let q := finish lv rv gl gr0
        noId q.left ∧ noId q.right := by
    intro lv rv gl gr0 hgl hgr
    cases lv with
    | none =>
        cases rv with
        | none =>
            exact ⟨hgl, hgr⟩
        | some t =>
            by_cases h1 :
                decodeOffset psi (tokenCode t) = -1
            · simp only [finish, dif_pos h1]
              exact
                ⟨hBumpNoId l
                    (ooArrNegTurnNext hpsi l.id t)
                    gr0 hgr,
                  hNoNone⟩
            · by_cases h2 :
                decodeOffset psi (tokenCode t) ≤ -2
              · simp only
                  [finish, dif_neg h1, dif_pos h2]
                exact
                  ⟨hBumpNoId l _ gr0 hgr,
                    hNoNone⟩
              · simp only
                  [finish, dif_neg h1, dif_neg h2]
                exact ⟨hgl, hgr⟩
    | some t =>
        by_cases h1 :
            decodeOffset psi (tokenCode t) = 1
        · simp only [finish, dif_pos h1]
          exact
            ⟨hNoNone,
              hBumpNoId r _ gl hgl⟩
        · by_cases h2 :
            2 ≤ decodeOffset psi (tokenCode t)
          · simp only
              [finish, dif_neg h1, dif_pos h2]
            exact
              ⟨hNoNone,
                hBumpNoId r _ gl hgl⟩
          · cases rv with
            | none =>
                simp only
                  [finish, dif_neg h1, dif_neg h2]
                exact ⟨hgl, hgr⟩
            | some tr =>
                by_cases hm1 :
                    decodeOffset psi
                        (tokenCode tr) = -1
                · simp only
                    [finish, dif_neg h1, dif_neg h2,
                      dif_pos hm1]
                  exact
                    ⟨hBumpNoId l
                        (ooArrNegTurnNext
                          hpsi l.id tr)
                        gr0 hgr,
                      hNoNone⟩
                · by_cases hm2 :
                    decodeOffset psi
                        (tokenCode tr) ≤ -2
                  · simp only
                      [finish, dif_neg h1, dif_neg h2,
                        dif_neg hm1, dif_pos hm2]
                    exact
                      ⟨hBumpNoId l _ gr0 hgr,
                        hNoNone⟩
                  · simp only
                      [finish, dif_neg h1, dif_neg h2,
                        dif_neg hm1, dif_neg hm2]
                    exact ⟨hgl, hgr⟩

  have hSetToken :
      ∀ (q : State psi kappa)
        (v : Option (TokenData psi)),
        tokenAt kind (sourceSet kind q v) = v := by
    intro q v
    rw [ooArrSourceSet_eq]
    cases kind <;> rfl

  have hClearToken :
      ∀ q : State psi kappa,
        tokenAt kind (sourceClear kind q) =
          ooArrLiveValue kind q := by
    intro q
    rw [ooArrSourceClear_eq]
    unfold ooArrClearInvalid ooArrLiveValue
    cases ht : tokenAt kind q with
    | none =>
        simp only [ht]
    | some t =>
        by_cases hv :
            ooArrLocalValid kind q t
        · simp only [ht, if_pos hv]
        · simp only [ht, if_neg hv]
          unfold ooArrSetToken
          cases kind <;> rfl

  have hClearLast :
      ∀ q : State psi kappa,
        (sourceClear kind q).last = q.last := by
    intro q
    rw [ooArrSourceClear_eq]
    unfold ooArrClearInvalid
    cases ht : tokenAt kind q with
    | none =>
        simp only [ht]
    | some t =>
        by_cases hv :
            ooArrLocalValid kind q t
        · simp only [ht, if_pos hv]
        · simp only [ht, if_neg hv]
          unfold ooArrSetToken
          cases kind <;> rfl

  let lv0 := ooArrLiveValue kind l
  let rv0 := ooArrLiveValue kind r
  let gl0 := ooArrLiveShadow kind l (some z)
  let gr0 := ooArrLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    ooArrBirthGhost
      hpsi kind step site l.id
  let lv1 :=
    if guard then some birth.value else lv0
  let gl1 :=
    if guard then some birth else gl0
  let collide :=
    lv1 ≠ none ∧ rv0 ≠ none
  let lv2 :=
    if collide then none else lv1
  let gl2 :=
    if collide then none else gl1

  have hNoRight0 : noId gr := by
    intro u hu hid
    exact hNoRight u hu hid

  have hgr0 : noId gr0 := by
    simpa [gr0]
      using hShadowNoId r gr hNoRight0

  have hBirthNoId : noId (some birth) := by
    intro u hu hid
    have hbu : birth = u :=
      Option.some.inj hu
    subst u
    apply hNotBirth
    simpa [birth, ooArrBirthGhost]
      using hid.symm

  have hPrefix :
      (lv2 = some z.value ∧
          gl2 = some z ∧
          rv0 = none ∧
          lv0 = some z.value) ∨
        (noId gl2 ∧ noId gr0) := by
    by_cases hg : guard
    · right
      refine ⟨?_, hgr0⟩
      by_cases hcol : collide
      · have hnone : gl2 = none := by
          simp [gl2, hcol]
        rw [hnone]
        exact hNoNone
      · have hbirth : gl2 = some birth := by
          simp [gl2, hcol, gl1, hg]
        rw [hbirth]
        exact hBirthNoId
    · cases hgl : gl0 with
      | none =>
          right
          refine ⟨?_, hgr0⟩
          have hnone : gl2 = none := by
            by_cases hcol : collide
            · simp [gl2, hcol]
            · simp [gl2, hcol, gl1, hg, hgl]
          rw [hnone]
          exact hNoNone
      | some u =>
          have hshadow :
              ooArrLiveShadow kind l (some z) =
                some u := by
            simpa [gl0] using hgl
          have hs :=
            hSourceShadow u hshadow
          have hu : u = z := hs.1
          subst u
          have hlv :
              lv0 = some z.value := by
            simpa [lv0] using hs.2
          have hlv1 :
              lv1 = some z.value := by
            simp [lv1, hg, hlv]
          cases hrv : rv0 with
          | none =>
              left
              have hcol : ¬ collide := by
                simp [collide, hrv]
              refine ⟨?_, ?_, rfl, hlv⟩
              · simp [lv2, hcol, hlv1]
              · simp
                  [gl2, hcol, gl1, hg, hgl]
          | some tr =>
              right
              refine ⟨?_, hgr0⟩
              have hcol : collide := by
                simp [collide, hlv1, hrv]
              have hnone : gl2 = none := by
                simp [gl2, hcol]
              rw [hnone]
              exact hNoNone

  have hMoveEq :
      ooArrGhostMoveToken
          hpsi kind step site
          l r (some z) gr =
        finish lv2 rv0 gl2 gr0 := by
    unfold ooArrGhostMoveToken
    simp only [dif_pos hgate]
    rfl

  have hPhysical :
      lv0 = some z.value →
      rv0 = none →
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some (ooArrBounceNext hpsi z.value) := by
    intro hlv hrv
    have hlv' :
        ooArrLiveValue kind l =
          some z.value := by
      simpa [lv0] using hlv
    have hrv' :
        ooArrLiveValue kind r = none := by
      simpa [rv0] using hrv
    rw [← ooArrMoveToken_eq hpsi kind l r]
    unfold ooArrMoveToken
    simp
      [hClearToken, hClearLast, hSetToken,
        hlv', hrv', hgate.1, hgate.2, hc,
        ooArrBounceNext]

  have hSourceFinish :
      lv0 = some z.value →
      rv0 = none →
      let q :=
        finish
          (some z.value) none (some z) gr0
      q.left = none ∧
        ∀ u : GhostToken n psi,
          q.right = some u →
          u.lmeta.id = z.lmeta.id →
          u.lmeta =
              ghostStepLineageAdvance z.lmeta ∧
            u.value =
              ooArrBounceNext hpsi z.value ∧
            ooArrLocalValid kind r u.value ∧
            tokenAt kind
                (moveToken hpsi kind l r).2 =
              some u.value := by
    intro hlv hrv
    have hphys := hPhysical hlv hrv
    dsimp only
    constructor
    · simp [finish, hc]
    · intro u hu hid
      have hb :
          (ooArrBumpTo
              kind r
              (ooArrBounceNext hpsi z.value)
              (some z)).live =
            some u := by
        simpa
          [finish, hc, ooArrBounceNext]
          using hu
      have hs :=
        hBumpSome
          r (ooArrBounceNext hpsi z.value)
          z u hb
      refine
        ⟨hs.1, hs.2.1, ?_, ?_⟩
      · rw [hs.2.1]
        exact hs.2.2
      · simpa [hs.2.1] using hphys

  intro z'
  rcases hPrefix with hsrc | hno
  · rcases hsrc with
      ⟨hlv2, hgl2, hrv, hlv⟩
    have hs := hSourceFinish hlv hrv
    dsimp only at hs
    constructor
    · intro hout _
      rw [hMoveEq, hlv2, hgl2, hrv] at hout
      rw [hs.1] at hout
      cases hout
    · intro hout hid
      rw [hMoveEq, hlv2, hgl2, hrv] at hout
      exact hs.2 z' hout hid
  · have hf :=
      hFinishNoId
        lv2 rv0 gl2 gr0 hno.1 hno.2
    dsimp only at hf
    constructor
    · intro hout hid
      rw [hMoveEq] at hout
      exact hf.1 z' hout hid
    · intro hout hid
      rw [hMoveEq] at hout
      exact False.elim (hf.2 z' hout hid)

private theorem ooArrClass_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      decodeOffset psi (tokenCode z.value) = (1 : Int))
    (z' : GhostToken n psi)
    (hout :
      (ooArrGhostMoveToken
          hpsi kind step site
          l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  exact
    (ooArrClass
      hpsi kind step site l r gr z
      hgate hNoRight hNotBirth hc z').1
      hout hid

private theorem ooArrClass_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      decodeOffset psi (tokenCode z.value) = (1 : Int))
    (z' : GhostToken n psi)
    (hout :
      (ooArrGhostMoveToken
          hpsi kind step site
          l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z'.lmeta =
        ghostStepLineageAdvance z.lmeta ∧
      z'.value =
        ooArrBounceNext hpsi z.value ∧
      ooArrLocalValid kind r z'.value ∧
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some z'.value := by
  exact
    (ooArrClass
      hpsi kind step site l r gr z
      hgate hNoRight hNotBirth hc z').2
      hout hid

/-! ## Arrival-stage arithmetic -/

private theorem ooArrOldTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (x : Nat)
    (hx : x < 2 * psi)
    (hnext : x + 1 < 2 * psi)
    (hdist :
      q.dist.val =
        (x + tokenD' psi kind) % (2 * psi))
    (hc :
      decodeOffset psi (tokenCode t) = (1 : Int)) :
    tokenTargetCoordinate kind q t =
      (((x + 1 : Nat)) : Int) := by
  unfold tokenTargetCoordinate
  rw [hc, hdist]
  cases kind with
  | black =>
      simp only [tokenD', Nat.add_zero]
      rw [Nat.mod_eq_of_lt hx]
      have hsum :
          (((x : Nat) : Int) + 1 +
              ((0 : Nat) : Int)) =
            (((x + 1 : Nat)) : Int) := by
        omega
      rw [Int.emod_eq_of_lt (by omega) (by omega), hsum]
  | white =>
      simp only [tokenD']
      by_cases hsmall : x + psi < 2 * psi
      · rw [Nat.mod_eq_of_lt hsmall]
        have hsum :
            ((((x + psi : Nat)) : Int) +
                  1 + ((psi : Nat) : Int)) =
              (((x + 1 : Nat)) : Int) +
                (((2 * psi : Nat)) : Int) := by
          omega
        rw [hsum, Int.add_emod_right]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
      · have hge : 2 * psi ≤ x + psi := by
          omega
        have hlt :
            x + psi - 2 * psi < 2 * psi := by
          omega
        rw [Nat.mod_eq_sub_mod hge,
          Nat.mod_eq_of_lt hlt]
        have hxp : psi ≤ x := by
          omega
        have hnat :
            x + psi - 2 * psi = x - psi := by
          omega
        rw [hnat]
        have hsum :
            ((((x - psi : Nat)) : Int) +
                  1 + ((psi : Nat) : Int)) =
              (((x + 1 : Nat)) : Int) := by
          omega
        rw [hsum]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]

private theorem ooArrBounceTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (x : Nat)
    (hnext : x + 1 < 2 * psi)
    (hlow : psi ≤ x + 1)
    (hdist :
      q.dist.val =
        (x + 1 + tokenD' psi kind) % (2 * psi))
    (hnew :
      decodeOffset psi (tokenCode t) =
        1 - ((psi : Nat) : Int)) :
    tokenTargetCoordinate kind q t =
      (((x + 2 - psi : Nat)) : Int) := by
  unfold tokenTargetCoordinate
  rw [hnew, hdist]
  cases kind with
  | black =>
      simp only [tokenD', Nat.add_zero]
      rw [Nat.mod_eq_of_lt hnext]
      have hsum :
          ((((x + 1 : Nat)) : Int) +
                (1 - ((psi : Nat) : Int)) +
                ((0 : Nat) : Int)) =
            (((x + 2 - psi : Nat)) : Int) := by
        omega
      rw [hsum]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
  | white =>
      simp only [tokenD']
      by_cases hsmall :
          x + 1 + psi < 2 * psi
      · rw [Nat.mod_eq_of_lt hsmall]
        have hsum :
            ((((x + 1 + psi : Nat)) : Int) +
                  (1 - ((psi : Nat) : Int)) +
                  ((psi : Nat) : Int)) =
              (((x + 2 - psi : Nat)) : Int) +
                (((2 * psi : Nat)) : Int) := by
          omega
        rw [hsum, Int.add_emod_right]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
      · have hge :
            2 * psi ≤ x + 1 + psi := by
          omega
        have hlt :
            x + 1 + psi - 2 * psi <
              2 * psi := by
          omega
        rw [Nat.mod_eq_sub_mod hge,
          Nat.mod_eq_of_lt hlt]
        have hnat :
            x + 1 + psi - 2 * psi =
              x + 1 - psi := by
          omega
        rw [hnat]
        have hsum :
            ((((x + 1 - psi : Nat)) : Int) +
                  (1 - ((psi : Nat) : Int)) +
                  ((psi : Nat) : Int)) =
              (((x + 2 - psi : Nat)) : Int) := by
          omega
        rw [hsum]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]

private theorem ooArrStage_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (x : Nat)
    (hlow : psi ≤ x + 1)
    (hc :
      decodeOffset psi (tokenCode t) = (1 : Int))
    (hnew :
      decodeOffset psi (tokenCode t') =
        1 - ((psi : Nat) : Int))
    (holdTarget :
      tokenTargetCoordinate kind q t =
        (((x + 1 : Nat)) : Int))
    (hnewTarget :
      tokenTargetCoordinate kind q' t' =
        (((x + 2 - psi : Nat)) : Int)) :
    lemma4TokenStage kind q' t' =
      lemma4TokenStage kind q t := by
  have holdPos :
      0 < decodeOffset psi (tokenCode t) := by
    rw [hc]
    omega
  have hnewNotPos :
      ¬ 0 < decodeOffset psi (tokenCode t') := by
    rw [hnew]
    omega
  have htoOld :
      ((((x + 1 : Nat)) : Int).toNat) =
        x + 1 := by
    simp
  have htoNew :
      ((((x + 2 - psi : Nat)) : Int).toNat) =
        x + 2 - psi := by
    simp
  unfold lemma4TokenStage
  dsimp only
  rw [if_neg hnewNotPos, if_pos holdPos,
    hnewTarget, holdTarget, htoNew, htoOld]
  omega

private theorem ooArrProgress_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) = (1 : Int))
    (hnew :
      decodeOffset psi (tokenCode t') =
        1 - ((psi : Nat) : Int))
    (hstage :
      lemma4TokenStage kind q' t' =
        lemma4TokenStage kind q t) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  have holdPos :
      0 < decodeOffset psi (tokenCode t) := by
    rw [hc]
    omega
  have hnewNotPos :
      ¬ 0 < decodeOffset psi (tokenCode t') := by
    rw [hnew]
    omega
  have habs :
      (decodeOffset psi (tokenCode t')).natAbs =
        psi - 1 := by
    rw [hnew]
    have hz :
        1 - ((psi : Nat) : Int) =
          -(((psi - 1 : Nat)) : Int) := by
      omega
    rw [hz]
    simp
  have hto :
      (decodeOffset psi (tokenCode t)).toNat = 1 := by
    rw [hc]
    rfl
  unfold lemma4TokenProgress
  dsimp only
  rw [if_neg hnewNotPos, if_pos holdPos,
    hstage, habs, hto]
  omega

/-! ## Closed c = 1 row -/


/-! ## Mirror family B (copied from TokenCorrectnessLemma4SweepInitiatorRows, prefix ooIRows/ooIr) -/

private def ooIRowsBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def ooIRowsMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def ooIRowsLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
        target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
        target ≤ (((psi - 1 : Nat)) : Int))

private instance instDecidableOoIRowsLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (ooIRowsLocalValid kind q t) := by
  unfold ooIRowsLocalValid
  infer_instance

private def ooIRowsSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def ooIRowsClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if ooIRowsLocalValid kind q t then
        q
      else
        ooIRowsSetToken kind q none

private def ooIRowsLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private theorem ooIRowsSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      ooIRowsSetToken kind q t := by
  cases kind <;> rfl

private theorem ooIRowsSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      ooIRowsClearInvalid kind q := by
  cases kind <;> rfl

private theorem ooIRowsSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = ooIRowsLeaderBirth q := by
  rfl

private def ooIRowsNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    ooIRowsMkToken
      (offsetPsiCode psi hpsi)
      (ooIRowsBitToFin (!sourceBit))
      (ooIRowsBitToFin sourceBit)
  else
    ooIRowsMkToken
      (offsetPsiCode psi hpsi)
      (ooIRowsBitToFin sourceBit)
      (0 : Fin 2)

private def ooIRowsMoveToken
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := sourceClear kind l
  let r := sourceClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧
          tokenAt kind l = none then
        sourceSet kind l
          (some
            (ooIRowsMkToken
              (offsetPsiCode psi hpsi)
              (ooIRowsBitToFin (!l.id))
              (ooIRowsBitToFin l.id)))
      else
        l
    let l :=
      if tokenAt kind l ≠ none ∧
          tokenAt kind r ≠ none then
        sourceSet kind l none
      else
        l
    let moveLeft :=
      fun (l r : State psi kappa) =>
        match tokenAt kind r with
        | none => (l, r)
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                ooIRowsNegTurnNext hpsi l.id t
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let nextOffset :=
                encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega)
              (sourceSet kind l
                  (some
                    (ooIRowsMkToken
                      nextOffset t.1.2 t.2)),
                sourceSet kind r none)
            else
              (l, r)
    match tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if hc1 : c = 1 then
          let bit := tokenBitBool t
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          (sourceSet kind l none,
            sourceSet kind r
              (some
                (ooIRowsMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2)))
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let nextOffset :=
            encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega)
          (sourceSet kind l none,
            sourceSet kind r
              (some
                (ooIRowsMkToken
                  nextOffset t.1.2 t.2)))
        else
          moveLeft l r
  else
    (l, r)

private theorem ooIRowsMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    ooIRowsMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl

private def ooIRowsLiveShadow
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if z.value = t ∧
              ooIRowsLocalValid kind q t then
            some z
          else
            none

private def ooIRowsLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if ooIRowsLocalValid kind q t then
        some t
      else
        none

private def ooIRowsBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      ooIRowsMkToken
        (offsetPsiCode psi hpsi)
        (ooIRowsBitToFin (!idBit))
        (ooIRowsBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def ooIRowsBumpTo
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' := ghostStepLineageAdvance z.lmeta
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if ooIRowsLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def ooIRowsGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := ooIRowsLiveValue kind l
  let rv0 := ooIRowsLiveValue kind r
  let gl0 := ooIRowsLiveShadow kind l gl
  let gr0 := ooIRowsLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ooIRowsBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ooIRowsBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if h1 : c = 1 then
          let next :=
            ooIRowsMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            ooIRowsBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            ooIRowsMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            ooIRowsBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some tr =>
              let cr := decodeOffset psi (tokenCode tr)
              if hm1 : cr = -1 then
                let next :=
                  ooIRowsNegTurnNext hpsi l.id tr
                let b :=
                  ooIRowsBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : cr ≤ -2 then
                have hc : ValidOffset psi cr :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode tr)
                let next :=
                  ooIRowsMkToken
                    (encodeOffset psi (cr + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    tr.1.2 tr.2
                let b :=
                  ooIRowsBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else
                ⟨gl2, gr0, []⟩
    | none =>
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                ooIRowsNegTurnNext hpsi l.id tr
              let b :=
                ooIRowsBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                ooIRowsMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                ooIRowsBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def ooIRowsPrelude
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
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
    else if r1.dist.val = 0 ∨
        r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def ooIRowsSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := ooIRowsPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2

private def ooIRowsSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := ooIRowsSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2

private def ooIRowsSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    ooIRowsSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  ooIRowsGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem ooIRowsSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ooIRowsSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

/-! ## Physical suffix frames -/

private theorem ooIRowsMoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.dist = l.dist ∧
      (moveToken hpsi kind l r).1.last = l.last ∧
      (moveToken hpsi kind l r).2.dist = r.dist ∧
      (moveToken hpsi kind l r).2.last = r.last := by
  have hi :=
    moveToken_initiator_fields hpsi kind l r
  rcases moveToken_responder_fields hpsi kind l r with
    hr | hr
  · cases kind <;>
      simp_all [eraseKindToken, eraseKindTokenId]
  · cases kind <;>
      simp_all
        [eraseKindToken, eraseKindTokenId, birthFields]

private theorem ooIRowsElimTokenPair
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (eliminateLeaders l r).1 =
        tokenAt kind l ∧
      tokenAt kind (eliminateLeaders l r).2 =
        tokenAt kind r := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  cases kind with
  | black =>
      constructor
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenB) hl
        simpa [PPL.Elim.otherView, tokenAt] using h
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenB) hr
        simpa [PPL.Elim.otherView, tokenAt] using h
  | white =>
      constructor
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenW) hl
        simpa [PPL.Elim.otherView, tokenAt] using h
      · have h :=
          congrArg
            (fun q : PPL.Elim.OtherFields
              psi kappa => q.tokenW) hr
        simpa [PPL.Elim.otherView, tokenAt] using h

private theorem ooIRowsElimDistLast
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (eliminateLeaders l r).1.dist = l.dist ∧
      (eliminateLeaders l r).1.last = l.last ∧
      (eliminateLeaders l r).2.dist = r.dist ∧
      (eliminateLeaders l r).2.last = r.last := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    ⟨congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hr,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hr⟩

private theorem ooIRowsWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black (moveToken hpsi .white l r).1 =
        tokenAt .black l ∧
      tokenAt .black (moveToken hpsi .white l r).2 =
        tokenAt .black r := by
  have hi :=
    moveToken_initiator_fields
      hpsi TokenKind.white l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  constructor
  · simpa [eraseKindToken, tokenAt] using hil
  · rcases
      moveToken_responder_fields
        hpsi TokenKind.white l r with hr | hr
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken, tokenAt]
        using h
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          birthFields, tokenAt]
        using h

private theorem ooIRowsPplSelectedTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind
          (ooIRowsSelectedOutput
            hpsi kind l r).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind
          (ooIRowsSelectedOutput
            hpsi kind l r).2 := by
  cases kind with
  | black =>
      let p := ooIRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        ooIRowsWhitePreservesBlack
          hpsi b.1 b.2
      have he :=
        ooIRowsElimTokenPair .black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooIRowsSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact ⟨he.1.trans hw.1, he.2.trans hw.2⟩
  | white =>
      let p := ooIRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        ooIRowsElimTokenPair .white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooIRowsSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem ooIRowsPplSelectedDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (ppl hpsi l r).1.dist =
        (ooIRowsSelectedOutput
          hpsi kind l r).1.dist ∧
      (ppl hpsi l r).1.last =
        (ooIRowsSelectedOutput
          hpsi kind l r).1.last ∧
      (ppl hpsi l r).2.dist =
        (ooIRowsSelectedOutput
          hpsi kind l r).2.dist ∧
      (ppl hpsi l r).2.last =
        (ooIRowsSelectedOutput
          hpsi kind l r).2.last := by
  cases kind with
  | black =>
      let p := ooIRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        ooIRowsMoveTokenDistLast
          hpsi .white b.1 b.2
      have he :=
        ooIRowsElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooIRowsSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact
        ⟨he.1.trans hw.1,
          he.2.1.trans hw.2.1,
          he.2.2.1.trans hw.2.2.1,
          he.2.2.2.trans hw.2.2.2⟩
  | white =>
      let p := ooIRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        ooIRowsElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          ooIRowsSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem ooIRowsStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys e) =
      tokenAt kind
        (ooIRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 ∧
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)) =
      tokenAt kind
        (ooIRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
  have hp :=
    ooIRowsPplSelectedTokenPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      (ghostStep hpsi ring step G e).phys e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  rw [hl, hr]
  exact hp

private theorem ooIRowsStepDistLast
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ((ghostStep hpsi ring step G e).phys e).dist =
        (ooIRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.dist ∧
      ((ghostStep hpsi ring step G e).phys e).last =
        (ooIRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.last ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        (ooIRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.dist ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).last =
        (ooIRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.last := by
  have hp :=
    ooIRowsPplSelectedDistLast
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      (ghostStep hpsi ring step G e).phys e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        _
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  rw [hl, hr]
  exact hp

/-! ## Ring and validity arithmetic -/

private theorem ooIRowsCd_two_le_n
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 ≤ n := by
  by_cases hn2 : 2 ≤ n
  · exact hn2
  · have hn0 : 0 < n := ring.hn
    have hn1 : n = 1 := by
      omega
    subst n
    let x0 : Fin (2 * psi) := ⟨0, by omega⟩
    let x1 : Fin (2 * psi) := ⟨1, by omega⟩
    have h0 := (hCd x0).1
    have h1 := (hCd x1).1
    dsimp only [x0, x1] at h0 h1
    have hs :
        shiftRight ring k 0 =
          shiftRight ring k 1 := by
      apply Fin.ext
      simp [shiftRight]
    rw [hs] at h0
    cases kind with
    | black =>
        have hm1 :
            1 % (2 * psi) = 1 :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm1] at h0 h1
        omega
    | white =>
        have hm0 :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        have hm1 :
            (1 + psi) % (2 * psi) =
              1 + psi :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm0, hm1] at h0 h1
        omega

private theorem ooIRowsRightNeighbor_ne
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem ooIRowsRightNeighbor_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (d : Nat) :
    ring.rightNeighbor (shiftRight ring k d) =
      shiftRight ring k (d + 1) := by
  apply Fin.ext
  simp only
    [DirectedRing.rightNeighbor, shiftRight]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem ooIRowsGhostSoundAt
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧
      ooIRowsLocalValid
        kind (G.phys i) z.value := by
  cases kind with
  | black =>
      exact hsound.1 i z howner
  | white =>
      exact hsound.2 i z howner

private theorem ooIRowsLastDistPlusD
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi)) :
    q.dist.val + tokenD' psi kind =
      2 * psi - 1 := by
  cases kind with
  | black =>
      simp only [tokenD'] at hdist ⊢
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt
          (by omega :
            2 * psi - 1 < 2 * psi)] at hdist
      omega
  | white =>
      simp only [tokenD'] at hdist ⊢
      have hge :
          2 * psi ≤ 2 * psi - 1 + psi := by
        omega
      have hlt :
          2 * psi - 1 + psi - 2 * psi <
            2 * psi := by
        omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt hlt] at hdist
      omega

private theorem ooIRowsLastPositiveTargetBelow
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    tokenTargetCoordinate kind q t <
      ((psi : Nat) : Int) := by
  have hsum :=
    ooIRowsLastDistPlusD
      hpsi kind q hdist
  have hsumInt :
      (((q.dist.val + tokenD' psi kind :
        Nat)) : Int) =
        (((2 * psi - 1 : Nat)) : Int) :=
    congrArg (fun a : Nat => (a : Int)) hsum
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hpos hv
      simp only [Int.ofNat_eq_natCast] at hpos hv
      have hm :
          1 ≤ m ∧ m ≤ psi := by
        rcases hv with hn | hp <;> omega
      have hnum :
          ((q.dist.val : Nat) : Int) +
                ((m : Nat) : Int) +
                ((tokenD' psi kind : Nat) : Int) =
            (((2 * psi - 1 + m : Nat)) : Int) := by
        simp only [Int.natCast_add] at hsumInt
        omega
      unfold tokenTargetCoordinate
      rw [hc]
      simp only [Int.ofNat_eq_natCast]
      rw [hnum]
      change
        ((((2 * psi - 1 + m) % (2 * psi) :
          Nat)) : Int) <
          ((psi : Nat) : Int)
      have hge :
          2 * psi ≤ 2 * psi - 1 + m := by
        omega
      rw [Nat.mod_eq_sub_mod hge]
      have heq :
          2 * psi - 1 + m - 2 * psi =
            m - 1 := by
        omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
      exact_mod_cast (show m - 1 < psi by omega)
  | negSucc m =>
      rw [hc] at hpos
      omega

private theorem ooIRowsPositiveNotLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hlocal :
      ooIRowsLocalValid kind q t)
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    False := by
  have ht :=
    ooIRowsLastPositiveTargetBelow
      hpsi kind q t hdist hpos
  unfold ooIRowsLocalValid at hlocal
  dsimp only at hlocal
  rcases hlocal with hp | hn <;> omega

private theorem ooIRowsCanonicalSucc
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (x d a b : Nat)
    (ha :
      a = (x + d) % (2 * psi))
    (hb :
      b = (x + 1 + d) % (2 * psi)) :
    b = (a + 1) % (2 * psi) := by
  rw [ha, hb]
  have hone :
      1 % (2 * psi) = 1 :=
    Nat.mod_eq_of_lt (by omega)
  calc
    (x + 1 + d) % (2 * psi) =
        (x + d + 1) % (2 * psi) := by
          congr 1
          omega
    _ =
        (((x + d) % (2 * psi)) +
          (1 % (2 * psi))) %
            (2 * psi) := by
          rw [Nat.add_mod]
    _ =
        (((x + d) % (2 * psi)) + 1) %
            (2 * psi) := by
          rw [hone]

private theorem ooIRowsRightMoveTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hdist :
      q'.dist.val =
        (q.dist.val + 1) % (2 * psi))
    (hc :
      2 ≤ decodeOffset psi (tokenCode t))
    (hnew :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) - 1) :
    tokenTargetCoordinate kind q' t' =
      tokenTargetCoordinate kind q t := by
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  cases hco :
      decodeOffset psi (tokenCode t) with
  | negSucc m =>
      rw [hco] at hc
      omega
  | ofNat m =>
      rw [hco] at hc hnew hv
      simp only [Int.ofNat_eq_natCast] at hc hnew hv
      have hm :
          2 ≤ m ∧ m ≤ psi := by
        rcases hv with hn | hp <;> omega
      have hm1 : 1 ≤ m := by
        omega
      have hcast :
          (((m - 1 : Nat)) : Int) =
            ((m : Int) - 1) := by
        omega
      have hnew' :
          decodeOffset psi (tokenCode t') =
            (((m - 1 : Nat)) : Int) := by
        exact hnew.trans hcast.symm
      unfold tokenTargetCoordinate
      rw [hco, hnew', hdist]
      simp only [Int.ofNat_eq_natCast]
      have hq : q.dist.val < 2 * psi :=
        q.dist.isLt
      by_cases hnowrap :
          q.dist.val + 1 < 2 * psi
      · rw [Nat.mod_eq_of_lt hnowrap]
        congr 1
        omega
      · have hwrap :
            q.dist.val + 1 = 2 * psi := by
          omega
        have hqeq :
            q.dist.val = 2 * psi - 1 := by
          omega
        rw [hwrap, Nat.mod_self, hqeq]
        cases kind with
        | black =>
            simp only [tokenD']
            have hsmall :
                m - 1 < 2 * psi := by
              omega
            have hsum :
                (((2 * psi - 1 : Nat)) : Int) +
                    ((m : Nat) : Int) =
                  (((m - 1 : Nat)) : Int) +
                    (((2 * psi : Nat)) : Int) := by
              omega
            simp only
              [Int.natCast_zero, Int.zero_add,
                Int.add_zero]
            rw [hsum, Int.add_emod_right]
        | white =>
            simp only [tokenD']
            have hsmall :
                m - 1 + psi < 2 * psi := by
              omega
            have hsum :
                (((2 * psi - 1 : Nat)) : Int) +
                    ((m : Nat) : Int) +
                    ((psi : Nat) : Int) =
                  (((m - 1 + psi : Nat)) : Int) +
                    (((2 * psi : Nat)) : Int) := by
              omega
            have hleft :
                (((m - 1 : Nat) : Int) +
                    ((psi : Nat) : Int)) =
                  (((m - 1 + psi : Nat)) : Int) := by
              omega
            simp only
              [Int.natCast_zero, Int.zero_add,
                Int.add_zero]
            rw [hleft, hsum, Int.add_emod_right]

private theorem ooIRowsRightMoveProgress
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hc :
      2 ≤ decodeOffset psi (tokenCode t))
    (hnew :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) - 1)
    (htarget :
      tokenTargetCoordinate kind q' t' =
        tokenTargetCoordinate kind q t) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  have holdPos :
      0 < decodeOffset psi (tokenCode t) := by
    omega
  have hnewPos :
      0 < decodeOffset psi (tokenCode t') := by
    omega
  have hstage :
      lemma4TokenStage kind q' t' =
        lemma4TokenStage kind q t := by
    unfold lemma4TokenStage
    dsimp only
    rw [if_pos hnewPos, if_pos holdPos, htarget]
  unfold lemma4TokenProgress
  dsimp only
  rw [if_pos hnewPos, if_pos holdPos, hstage]
  have hv :
      ValidOffset psi
        (decodeOffset psi (tokenCode t)) :=
    decodeOffset_valid
      psi (by have := (tokenCode t).isLt; omega) (tokenCode t)
  cases hco :
      decodeOffset psi (tokenCode t) with
  | negSucc m =>
      rw [hco] at hc
      omega
  | ofNat m =>
      rw [hco] at hc hnew hv
      simp only [Int.ofNat_eq_natCast] at hc hnew hv
      have hm :
          2 ≤ m ∧ m ≤ psi := by
        rcases hv with hn | hp <;> omega
      have hcast :
          (((m - 1 : Nat)) : Int) =
            ((m : Int) - 1) := by
        omega
      have hnew' :
          decodeOffset psi (tokenCode t') =
            (((m - 1 : Nat)) : Int) := by
        exact hnew.trans hcast.symm
      rw [hnew']
      have e1 : (Int.ofNat m).toNat = m := rfl
      have e2 : (((m - 1 : Nat)) : Int).toNat = m - 1 := rfl
      rw [e1, e2]
      omega

private theorem ooIRowsValidToken_of_local
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (i : Fin n)
    (q : State psi kappa)
    (t : TokenData psi)
    (htok :
      tokenAt kind (C i) = some t)
    (hdist :
      (C i).dist = q.dist)
    (hlocal :
      ooIRowsLocalValid kind q t) :
    ValidToken kind C i := by
  unfold ValidToken
  rw [htok]
  unfold ooIRowsLocalValid at hlocal
  unfold tokenTargetCoordinate at hlocal ⊢
  rw [hdist]
  exact hlocal

private theorem ooIRowsValidToken_transfer
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (i : Fin n)
    (t : TokenData psi)
    (htok :
      tokenAt kind (C i) = some t)
    (htok' :
      tokenAt kind (C' i) = some t)
    (hdist :
      (C' i).dist = (C i).dist)
    (hvalid :
      ValidToken kind C i) :
    ValidToken kind C' i := by
  unfold ValidToken at hvalid ⊢
  rw [htok] at hvalid
  rw [htok']
  unfold tokenTargetCoordinate at hvalid ⊢
  rw [hdist]
  exact hvalid

private theorem ooIRowsFresh_advance
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n)
    (hfresh : FreshAt kind k m) :
    FreshAt kind k (ghostStepLineageAdvance m) := by
  rcases hfresh with ⟨t, hid, hsite⟩
  exact
    ⟨t,
      by simpa [ghostStepLineageAdvance] using hid,
      by simpa [ghostStepLineageAdvance] using hsite⟩

/-! ## Finite same-ID selected-colour classifications -/

private def ooIRowsRightNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (hc :
      2 ≤ decodeOffset psi (tokenCode t)) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hv : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  ooIRowsMkToken
    (encodeOffset psi (c - 1) (by
      rcases hv with hn | hp
      · exfalso
        omega
      · right
        omega))
    t.1.2 t.2

/-! ## Branch-level projection facts for the selected-colour move

The six branch helpers below are proved on one explicit case tree: the two
`last` flags, the two live values, the birth guard, and the decoded offset
signs.  In every branch the physical `ooIRowsMoveToken` and the ghost
`ooIRowsGhostMoveToken` take the same branch; the lemmas in this block
normalise the token projections, the cleared fields, and the shadow/bump
constructors so that one fixed `simp only` set decides every branch. -/

private theorem ooIrTokenAt_sourceSet
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q x) = x := by
  rw [ooIRowsSourceSet_eq]
  cases kind <;> rfl

private theorem ooIrTokenAt_sourceClear
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      ooIRowsLiveValue kind q := by
  rw [ooIRowsSourceClear_eq]
  unfold ooIRowsClearInvalid
  unfold ooIRowsLiveValue
  cases htok : tokenAt kind q with
  | none =>
      exact htok
  | some t =>
      show tokenAt kind
          (if ooIRowsLocalValid kind q t then q
            else ooIRowsSetToken kind q none) =
        (if ooIRowsLocalValid kind q t then some t else none)
      by_cases hv : ooIRowsLocalValid kind q t
      · rw [if_pos hv, if_pos hv]
        exact htok
      · rw [if_neg hv, if_neg hv]
        cases kind <;> rfl

/-- Clearing an invalid selected token changes only that token field. -/
private theorem ooIrSourceClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    And ((sourceClear kind q).last = q.last)
      (And ((sourceClear kind q).id = q.id)
        ((sourceClear kind q).dist = q.dist)) := by
  have key :
      Or (ooIRowsClearInvalid kind q = q)
        (ooIRowsClearInvalid kind q =
          ooIRowsSetToken kind q none) := by
    unfold ooIRowsClearInvalid
    cases tokenAt kind q with
    | none => exact Or.inl rfl
    | some t =>
        by_cases hv : ooIRowsLocalValid kind q t
        · exact Or.inl (if_pos hv)
        · exact Or.inr (if_neg hv)
  rw [ooIRowsSourceClear_eq]
  rcases key with h | h <;> rw [h]
  · exact ⟨rfl, rfl, rfl⟩
  · cases kind <;> exact ⟨rfl, rfl, rfl⟩

private theorem ooIrSourceClear_last
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).last = q.last :=
  (ooIrSourceClear_fields kind q).1

private theorem ooIrSourceClear_id
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).id = q.id :=
  (ooIrSourceClear_fields kind q).2.1

private theorem ooIrSourceClear_dist
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).dist = q.dist :=
  (ooIrSourceClear_fields kind q).2.2

private theorem ooIrSourceSet_id
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (x : Option (TokenData psi)) :
    (sourceSet kind q x).id = q.id := by
  rw [ooIRowsSourceSet_eq]
  cases kind <;> rfl

private theorem ooIrTokenCode_mk
    {psi : Nat} (o : Fin (2 * psi - 1)) (b c : Fin 2) :
    tokenCode (ooIRowsMkToken o b c) = o := rfl

private theorem ooIrBirthGhost_value
    {n psi : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    (ooIRowsBirthGhost hpsi kind step site idBit :
        GhostToken n psi).value =
      ooIRowsMkToken
        (offsetPsiCode psi hpsi)
        (ooIRowsBitToFin (!idBit))
        (ooIRowsBitToFin idBit) := rfl

/-- A shadow is empty whenever the physical live value is empty. -/
private theorem ooIrShadow_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hnone : ooIRowsLiveValue kind q = none) :
    ooIRowsLiveShadow kind q g = none := by
  unfold ooIRowsLiveValue at hnone
  cases g with
  | none =>
      rfl
  | some u =>
      unfold ooIRowsLiveShadow
      cases ht : tokenAt kind q with
      | none =>
          rfl
      | some t =>
          rw [ht] at hnone
          by_cases hv : ooIRowsLocalValid kind q t
          · have hbad :
                (some t : Option (TokenData psi)) = none := by
              simpa only [if_pos hv] using hnone
            cases hbad
          · show (if u.value = t ∧ ooIRowsLocalValid kind q t
                then some u else none) = none
            rw [if_neg (fun h => hv h.2)]

/-- A live shadow is the incoming ghost and carries the live value. -/
private theorem ooIrShadow_some
    {n psi kappa : Nat}
    {kind : TokenKind}
    {q : State psi kappa}
    {g : Option (GhostToken n psi)}
    {w : GhostToken n psi}
    (h : ooIRowsLiveShadow kind q g = some w) :
    g = some w ∧
      ooIRowsLiveValue kind q = some w.value := by
  cases g with
  | none =>
      cases h
  | some z =>
      unfold ooIRowsLiveShadow at h
      unfold ooIRowsLiveValue
      cases ht : tokenAt kind q with
      | none =>
          rw [ht] at h
          cases h
      | some t =>
          rw [ht] at h
          change (if z.value = t ∧ ooIRowsLocalValid kind q t
              then some z else none) = some w at h
          by_cases hc : z.value = t ∧ ooIRowsLocalValid kind q t
          · rw [if_pos hc] at h
            have hzw : z = w := Option.some.inj h
            subst hzw
            refine ⟨rfl, ?_⟩
            change (if ooIRowsLocalValid kind q t
                then some t else none) = some z.value
            rw [if_pos hc.2, hc.1]
          · rw [if_neg hc] at h
            cases h

private theorem ooIrBump_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (next : TokenData psi) :
    (ooIRowsBumpTo kind q next
        (none : Option (GhostToken n psi))).live = none := rfl

/-- A live bump output is the advanced incoming owner at the new value, and
the new value is locally valid at the destination. -/
private theorem ooIrBump_some
    {n psi kappa : Nat}
    {kind : TokenKind}
    {q : State psi kappa}
    {next : TokenData psi}
    {g : Option (GhostToken n psi)}
    {z' : GhostToken n psi}
    (h : (ooIRowsBumpTo kind q next g).live = some z') :
    ∃ w : GhostToken n psi,
      g = some w ∧
        z'.value = next ∧
          z'.lmeta = ghostStepLineageAdvance w.lmeta ∧
            ooIRowsLocalValid kind q next := by
  cases g with
  | none =>
      cases h
  | some w =>
      change (if ooIRowsLocalValid kind q next then
          some ({ value := next
                  lmeta := ghostStepLineageAdvance w.lmeta } :
            GhostToken n psi)
        else none) = some z' at h
      by_cases hv : ooIRowsLocalValid kind q next
      · rw [if_pos hv] at h
        cases h
        exact ⟨w, rfl, rfl, rfl, hv⟩
      · rw [if_neg hv] at h
        cases h

/-! ## Finite same-ID branch helpers (explicit case tree) -/

private theorem ooIRowsGhostMove_valueSound_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      (ooIRowsGhostMoveToken
          hpsi kind step site l r gl gr).left =
        some z') :
    tokenAt kind
        (moveToken hpsi kind l r).1 =
      some z'.value := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  rw [← ooIRowsMoveToken_eq hpsi kind l r]
  unfold ooIRowsMoveToken
  unfold ooIRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                ooIrShadow_none, ooIrBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost ⊢
      all_goals
        first
        | exact (ooIrShadow_some hpost).2
        | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost ⊢
        all_goals
          first
          | exact (ooIrShadow_some hpost).2
          | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
    | false =>
        cases hAv : ooIRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (ooIrShadow_some hpost).2
                    | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (ooIrShadow_some hpost).2
                    | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
        | some a =>
          cases hBv : ooIRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost ⊢
              all_goals
                first
                | exact (ooIrShadow_some hpost).2
                | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost ⊢
              all_goals
                first
                | exact (ooIrShadow_some hpost).2
                | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])


private theorem ooIRowsGhostMove_valueSound_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      (ooIRowsGhostMoveToken
          hpsi kind step site l r gl gr).right =
        some z') :
    tokenAt kind
        (moveToken hpsi kind l r).2 =
      some z'.value := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  rw [← ooIRowsMoveToken_eq hpsi kind l r]
  unfold ooIRowsMoveToken
  unfold ooIRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                ooIrShadow_none, ooIrBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost ⊢
      all_goals
        first
        | exact (ooIrShadow_some hpost).2
        | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost ⊢
        all_goals
          first
          | exact (ooIrShadow_some hpost).2
          | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
    | false =>
        cases hAv : ooIRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (ooIrShadow_some hpost).2
                    | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (ooIrShadow_some hpost).2
                    | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (ooIrShadow_some hpost).2
                      | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
        | some a =>
          cases hBv : ooIRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost ⊢
              all_goals
                first
                | exact (ooIrShadow_some hpost).2
                | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost ⊢
              all_goals
                first
                | exact (ooIrShadow_some hpost).2
                | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (ooIrShadow_some hpost).2
                  | (have h := (ooIrShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; rw [hv]; congr 1; congr 1; simp only [ooIrTokenCode_mk, decodeOffset_psi])


private theorem ooIRowsRightMoveGhost_left_false
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      2 ≤ decodeOffset psi (tokenCode z.value))
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold ooIRowsGhostMoveToken at hpost
  obtain ⟨hl1, hr1⟩ := hgate
  cases hAv : ooIRowsLiveValue kind l with
  | none =>
    by_cases hd : l.dist.val = tokenD' psi kind
    · cases hBv : ooIRowsLiveValue kind r with
      | none =>
          simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                      ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                      ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                      ooIrShadow_none, ooIrBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    · cases hBv : ooIRowsLiveValue kind r with
      | none =>
          simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                      ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                      ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                      ooIrShadow_none, ooIrBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
  | some a =>
    cases hBv : ooIRowsLiveValue kind r with
    | none =>
      by_cases h1 : decodeOffset psi (tokenCode a) = 1
      · simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, h1] at hpost
        all_goals
          first
          | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    | some b =>
      by_cases hm1 : decodeOffset psi (tokenCode b) = -1
      · simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, hm1] at hpost
        all_goals
          first
          | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := ooIrShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)


private theorem ooIRowsRightMoveGhost_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      2 ≤ decodeOffset psi (tokenCode z.value))
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z'.lmeta =
        ghostStepLineageAdvance z.lmeta ∧
      z'.value =
        ooIRowsRightNext hpsi z.value hc ∧
      ooIRowsLocalValid kind r z'.value := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold ooIRowsGhostMoveToken at hpost
  obtain ⟨hl1, hr1⟩ := hgate
  cases hAv : ooIRowsLiveValue kind l with
  | none =>
    by_cases hd : l.dist.val = tokenD' psi kind
    · cases hBv : ooIRowsLiveValue kind r with
      | none =>
          simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                      ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                      ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                      ooIrShadow_none, ooIrBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
    · cases hBv : ooIRowsLiveValue kind r with
      | none =>
          simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                      ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                      ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                      ooIrShadow_none, ooIrBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
  | some a =>
    cases hBv : ooIRowsLiveValue kind r with
    | none =>
      by_cases h1 : decodeOffset psi (tokenCode a) = 1
      · simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, h1] at hpost
        all_goals
          first
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
      · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
    | some b =>
      by_cases hm1 : decodeOffset psi (tokenCode b) = -1
      · simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, hm1] at hpost
        all_goals
          first
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
      · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
        · simp only
            [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                    ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                    ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                    ooIrShadow_none, ooIrBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)


private theorem ooIRowsTurnGhost_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0)
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z' = z := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold ooIRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                ooIrShadow_none, ooIrBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost
      all_goals
        first
        | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost
        all_goals
          first
          | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    | false =>
        cases hAv : ooIRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        | some a =>
          cases hBv : ooIRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost
              all_goals
                first
                | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost
              all_goals
                first
                | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (ooIrShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hgr, _⟩ := ooIrShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)


private theorem ooIRowsTurnGhost_right_false
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0)
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold ooIRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                ooIrShadow_none, ooIrBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost
      all_goals
        first
        | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                  ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                  ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                  ooIrShadow_none, ooIrBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost
        all_goals
          first
          | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    | false =>
        cases hAv : ooIRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · cases hBv : ooIRowsLiveValue kind r with
            | none =>
                simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                            ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                            ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                            ooIrShadow_none, ooIrBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                              ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                              ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                              ooIrShadow_none, ooIrBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        | some a =>
          cases hBv : ooIRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost
              all_goals
                first
                | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                        ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                        ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                        ooIrShadow_none, ooIrBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost
              all_goals
                first
                | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [ooIrTokenAt_sourceSet, ooIrTokenAt_sourceClear,
                          ooIrSourceClear_last, ooIrSourceClear_id, ooIrSourceClear_dist,
                          ooIrSourceSet_id, ooIrTokenCode_mk, ooIrBirthGhost_value,
                          ooIrShadow_none, ooIrBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (ooIrShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; obtain ⟨hg, h⟩ := ooIrShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := ooIrBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)



private theorem ooIRowsRightMoveClass_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      2 ≤ decodeOffset psi (tokenCode z.value))
    (z' : GhostToken n psi)
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  exact
    ooIRowsRightMoveGhost_left_false
      hpsi kind step site l r gr z z'
      hgate hNoRight hNotBirth hc hout hid

private theorem ooIRowsRightMoveClass_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      2 ≤ decodeOffset psi (tokenCode z.value))
    (z' : GhostToken n psi)
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z'.lmeta =
        ghostStepLineageAdvance z.lmeta ∧
      z'.value =
        ooIRowsRightNext hpsi z.value hc ∧
      ooIRowsLocalValid kind r z'.value ∧
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some z'.value := by
  have hg :=
    ooIRowsRightMoveGhost_right
      hpsi kind step site l r gr z z'
      hgate hNoRight hNotBirth hc hout hid
  have hv :=
    ooIRowsGhostMove_valueSound_right
      hpsi kind step site l r (some z) gr z' hout
  exact ⟨hg.1, hg.2.1, hg.2.2, hv⟩

private theorem ooIRowsTurnClass_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0)
    (z' : GhostToken n psi)
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z' = z ∧
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        some z.value := by
  have hz :=
    ooIRowsTurnGhost_left
      hpsi kind step site l r gr z z'
      hNoRight hNotBirth hneg hout hid
  have hv :=
    ooIRowsGhostMove_valueSound_left
      hpsi kind step site l r (some z) gr z' hout
  subst z'
  exact ⟨rfl, hv⟩

private theorem ooIRowsTurnClass_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0)
    (z' : GhostToken n psi)
    (hout :
      (ooIRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  exact
    ooIRowsTurnGhost_right_false
      hpsi kind step site l r gr z z'
      hNoRight hNotBirth hneg hout hid

private theorem ooIRowsRightMoveClass
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgate : l.last = false ∧ r.last = false)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hc :
      2 ≤ decodeOffset psi (tokenCode z.value)) :
    ∀ z' : GhostToken n psi,
      ((ooIRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).left =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        False) ∧
      ((ooIRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).right =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        z'.lmeta =
            ghostStepLineageAdvance z.lmeta ∧
          z'.value =
            ooIRowsRightNext hpsi z.value hc ∧
          ooIRowsLocalValid kind r z'.value ∧
          tokenAt kind
              (moveToken hpsi kind l r).2 =
            some z'.value) := by
  intro z'
  exact
    ⟨ooIRowsRightMoveClass_left
        hpsi kind step site l r gr z
        hgate hNoRight hNotBirth hc z',
      ooIRowsRightMoveClass_right
        hpsi kind step site l r gr z
        hgate hNoRight hNotBirth hc z'⟩

private theorem ooIRowsTurnClass
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoRight :
      ∀ zr : GhostToken n psi,
        gr = some zr →
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    ∀ z' : GhostToken n psi,
      ((ooIRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).left =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        z' = z ∧
          tokenAt kind
              (moveToken hpsi kind l r).1 =
            some z.value) ∧
      ((ooIRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).right =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        False) := by
  intro z'
  exact
    ⟨ooIRowsTurnClass_left
        hpsi kind step site l r gr z
        hNoRight hNotBirth hneg z',
      ooIRowsTurnClass_right
        hpsi kind step site l r gr z
        hNoRight hNotBirth hneg z'⟩

/-! ## Closed c >= 2 row -/


/-! ## Mirror family C (copied from TokenCorrectnessLemma4SweepResponderSameId, prefix ooResp) -/

private def ooRespBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def ooRespMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def ooRespLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
      target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
      target ≤ (((psi - 1 : Nat)) : Int))


private instance instDecidableOoRespLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (ooRespLocalValid kind q t) := by
  unfold ooRespLocalValid
  infer_instance


private def ooRespSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def ooRespClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if ooRespLocalValid kind q t then
        q
      else
        ooRespSetToken kind q none


private def ooRespLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


private theorem ooRespSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      ooRespSetToken kind q t := by
  cases kind <;> rfl


private theorem ooRespSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      ooRespClearInvalid kind q := by
  cases kind <;> rfl


private theorem ooRespSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = ooRespLeaderBirth q := by
  rfl


private def ooRespNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    ooRespMkToken
      (offsetPsiCode psi hpsi)
      (ooRespBitToFin (!sourceBit))
      (ooRespBitToFin sourceBit)
  else
    ooRespMkToken
      (offsetPsiCode psi hpsi)
      (ooRespBitToFin sourceBit)
      (0 : Fin 2)


private def ooRespLiveShadow
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if z.value = t ∧
              ooRespLocalValid kind q t then
            some z
          else
            none


private def ooRespLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if ooRespLocalValid kind q t then
        some t
      else
        none


private def ooRespBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      ooRespMkToken
        (offsetPsiCode psi hpsi)
        (ooRespBitToFin (!idBit))
        (ooRespBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def ooRespBumpTo
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' := ghostStepLineageAdvance z.lmeta
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if ooRespLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def ooRespGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := ooRespLiveValue kind l
  let rv0 := ooRespLiveValue kind r
  let gl0 := ooRespLiveShadow kind l gl
  let gr0 := ooRespLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ooRespBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ooRespBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if c = 1 then
          let next :=
            ooRespMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            ooRespBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            ooRespMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            ooRespBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some t =>
              let c :=
                decodeOffset psi (tokenCode t)
              if c = -1 then
                let next :=
                  ooRespNegTurnNext
                    hpsi l.id t
                let b :=
                  ooRespBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c ≤ -2 then
                have hbranch : c ≤ -2 := hm2
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  ooRespMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  ooRespBumpTo
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
            if c = -1 then
              let next :=
                ooRespNegTurnNext
                  hpsi l.id t
              let b :=
                ooRespBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                ooRespMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                ooRespBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩


/-
Literal Algorithm 3, expressed through the public sourceSet/sourceClear/
sourceBirth aliases.  This is used only to prove value soundness of the local
ghost mirror.
-/
private def ooRespMoveToken
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := sourceClear kind l
  let r := sourceClear kind r
  if l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧
          tokenAt kind l = none then
        sourceSet kind l
          (some
            (ooRespMkToken
              (offsetPsiCode psi hpsi)
              (ooRespBitToFin (!l.id))
              (ooRespBitToFin l.id)))
      else
        l
    let l :=
      if tokenAt kind l ≠ none ∧
          tokenAt kind r ≠ none then
        sourceSet kind l none
      else
        l
    let moveLeft :=
      fun (l r : State psi kappa) =>
        match tokenAt kind r with
        | none =>
            (l, r)
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if c = -1 then
              let next :=
                ooRespNegTurnNext hpsi l.id t
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                ooRespMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else
              (l, r)
    match tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if c = 1 then
          let bit := tokenBitBool t
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          (sourceSet kind l none,
            sourceSet kind r
              (some
                (ooRespMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2)))
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            ooRespMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          (sourceSet kind l none,
            sourceSet kind r (some next))
        else
          moveLeft l r
  else
    (l, r)


private theorem ooRespMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    ooRespMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl


private def ooRespPrelude
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
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
    else if r1.dist.val = 0 ∨
        r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)


private def ooRespSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := ooRespPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2


private def ooRespSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    ooRespSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  ooRespGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))


private theorem ooRespSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ooRespSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl


/-! -----------------------------------------------------------------------
    Finite ghost-row facts
------------------------------------------------------------------------ -/


/-
Every live ghost output of the local mirror has exactly the value carried by
the corresponding literal Algorithm-3 output.  No lineage assumption is
needed here.
-/
private def OoRespOptionSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) : Prop :=
  forall z : GhostToken n psi,
    g = some z ->
    And
      (tokenAt kind q = some z.value)
      (ooRespLocalValid kind q z.value)




private def OoRespAlignedSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi))
    (g : Option (GhostToken n psi)) : Prop :=
  And
    (tokenAt kind q = v)
    (OoRespOptionSound kind q g)




private theorem ooRespLocalValid_of_dist_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t : TokenData psi)
    (hdist : q'.dist = q.dist)
    (hvalid : ooRespLocalValid kind q t) :
    ooRespLocalValid kind q' t := by
  unfold ooRespLocalValid at hvalid ⊢
  unfold tokenTargetCoordinate at hvalid ⊢
  rw [hdist]
  exact hvalid




private theorem ooRespSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q t) = t := by
  rw [ooRespSourceSet_eq]
  cases kind <;> rfl




private theorem ooRespSourceSet_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).dist = q.dist := by
  rw [ooRespSourceSet_eq]
  cases kind <;> rfl




private theorem ooRespSourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).id = q.id := by
  rw [ooRespSourceSet_eq]
  cases kind <;> rfl




private theorem ooRespSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      ooRespLiveValue kind q := by
  rw [ooRespSourceClear_eq]
  unfold ooRespClearInvalid
    ooRespLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv :
          ooRespLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold ooRespSetToken
        cases kind <;> rfl




private theorem ooRespSourceClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    let q0 := sourceClear kind q
    And
      (q0.dist = q.dist)
      (And
        (q0.last = q.last)
        (q0.id = q.id)) := by
  dsimp only
  rw [ooRespSourceClear_eq]
  unfold ooRespClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      exact ⟨rfl, rfl, rfl⟩
  | some t =>
      by_cases hv :
          ooRespLocalValid kind q t
      · simp only [if_pos hv]
        refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial
      · simp only [if_neg hv]
        unfold ooRespSetToken
        cases kind <;>
          exact ⟨rfl, rfl, rfl⟩




private theorem ooRespLiveShadow_aligned
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    OoRespAlignedSound
      kind
      (sourceClear kind q)
      (ooRespLiveValue kind q)
      (ooRespLiveShadow kind q g) := by
  constructor
  · exact ooRespSourceClear_token kind q
  · unfold OoRespOptionSound
    intro z hz
    unfold ooRespLiveShadow at hz
    cases hg : g with
    | none =>
        simp only [hg] at hz
        cases hz
    | some z0 =>
        simp only [hg] at hz
        cases ht : tokenAt kind q with
        | none =>
            simp only [ht] at hz
            cases hz
        | some t =>
            simp only [ht] at hz
            by_cases hkeep :
                And
                  (z0.value = t)
                  (ooRespLocalValid kind q t)
            · simp only [if_pos hkeep] at hz
              cases hz
              constructor
              · rw [
                  ooRespSourceClear_token,
                  ooRespLiveValue,
                  ht]
                simp only [if_pos hkeep.2, hkeep.1]
              · rw [hkeep.1]
                exact
                  ooRespLocalValid_of_dist_eq
                    kind q (sourceClear kind q) t
                    (ooRespSourceClear_fields
                      kind q).1
                    hkeep.2
            · simp only [if_neg hkeep] at hz
              cases hz




/-- The liveShadow stay branch, with both endpoint soundness conjuncts. -/
private theorem ooRespGhostMoveToken_liveShadow_stay
    {n psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    And
      (OoRespOptionSound
        kind (sourceClear kind l)
        (ooRespLiveShadow kind l gl))
      (OoRespOptionSound
        kind (sourceClear kind r)
        (ooRespLiveShadow kind r gr)) := by
  exact
    And.intro
      (ooRespLiveShadow_aligned
        kind l gl).2
      (ooRespLiveShadow_aligned
        kind r gr).2




private theorem ooRespBirth_localValid
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (q : State psi kappa)
    (hdist :
      q.dist.val = tokenD' psi kind) :
    ooRespLocalValid kind q
      (ooRespBirthGhost
        hpsi kind step site idBit).value := by
  let birth :=
    ooRespBirthGhost
      hpsi kind step site idBit
  have hcode :
      decodeOffset psi (tokenCode birth.value) =
        ((psi : Nat) : Int) := by
    change
      decodeOffset psi (offsetPsiCode psi hpsi) =
        ((psi : Nat) : Int)
    exact decodeOffset_psi psi hpsi
  have htarget :
      tokenTargetCoordinate kind q birth.value =
        ((psi : Nat) : Int) := by
    unfold tokenTargetCoordinate
    rw [hcode, hdist]
    cases kind with
    | black =>
        have hmod :
            (((psi : Nat) : Int) %
                (((2 * psi : Nat)) : Int)) =
              ((psi : Nat) : Int) := by
          exact
            Int.emod_eq_of_lt
              (by omega) (by omega)
        simpa [tokenD'] using hmod
    | white =>
        have htriple :
            ((((psi : Nat) : Int) +
                  ((psi : Nat) : Int) +
                  ((psi : Nat) : Int)) %
                (((2 * psi : Nat)) : Int)) =
              ((psi : Nat) : Int) := by
          have hsum :
              ((psi : Nat) : Int) +
                  ((psi : Nat) : Int) +
                  ((psi : Nat) : Int) =
                ((psi : Nat) : Int) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right]
          exact
            Int.emod_eq_of_lt
              (by omega) (by omega)
        simpa [tokenD'] using htriple
  unfold ooRespLocalValid
  rw [hcode, htarget]
  exact
    Or.inl
      ⟨by omega, by omega, by omega⟩




private theorem ooRespBirthGhost_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (q : State psi kappa)
    (hdist :
      q.dist.val = tokenD' psi kind) :
    OoRespOptionSound kind
      (sourceSet kind q
        (some
          (ooRespBirthGhost
            hpsi kind step site idBit).value))
      (some
        (ooRespBirthGhost
          hpsi kind step site idBit)) := by
  let birth :=
    ooRespBirthGhost
      hpsi kind step site idBit
  unfold OoRespOptionSound
  intro z hz
  cases hz
  constructor
  · exact
      ooRespSourceSet_token
        kind q (some birth.value)
  · apply
      ooRespBirth_localValid
        hpsi kind step site idBit
        (q :=
          sourceSet kind q (some birth.value))
    have hframe :=
      ooRespSourceSet_dist
        kind q (some birth.value)
    have hval :=
      congrArg Fin.val hframe
    exact hval.trans hdist




/-- The birthGhost branch, with the fresh left owner and right live shadow. -/
private theorem ooRespGhostMoveToken_birthGhost
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (hdist :
      l.dist.val = tokenD' psi kind) :
    And
      (OoRespOptionSound kind
        (sourceSet kind l
          (some
            (ooRespBirthGhost
              hpsi kind step site idBit).value))
        (some
          (ooRespBirthGhost
            hpsi kind step site idBit)))
      (OoRespOptionSound kind
        (sourceClear kind r)
        (ooRespLiveShadow kind r gr)) := by
  exact
    And.intro
      (ooRespBirthGhost_sound
        hpsi kind step site idBit l hdist)
      (ooRespLiveShadow_aligned
        kind r gr).2




private theorem ooRespOptionSound_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    OoRespOptionSound
      (n := n) kind q none := by
  unfold OoRespOptionSound
  intro z hz
  cases hz




/--
The bumpTo movement branch.  The first pair is the right-moving orientation
(gone, destination), and the second pair is the left-moving orientation
(destination, gone).
-/
private theorem ooRespGhostMoveToken_bumpTo_move
    {n psi kappa : Nat}
    (kind : TokenKind)
    (base qGone qDest : State psi kappa)
    (next : TokenData psi)
    (g : Option (GhostToken n psi))
    (htok :
      tokenAt kind qDest = some next)
    (hdist :
      qDest.dist = base.dist) :
    And
      (And
        (OoRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qGone
          (none : Option (GhostToken n psi)))
        (OoRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qDest
          (ooRespBumpTo
            (n := n) (psi := psi) (kappa := kappa)
            kind base next g).live))
      (And
        (OoRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qDest
          (ooRespBumpTo
            (n := n) (psi := psi) (kappa := kappa)
            kind base next g).live)
        (OoRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qGone
          (none : Option (GhostToken n psi)))) := by
  have hnone :
      OoRespOptionSound
        (n := n) (psi := psi) (kappa := kappa)
        kind qGone
        (none : Option (GhostToken n psi)) :=
    ooRespOptionSound_none
      (n := n) (psi := psi) (kappa := kappa)
      kind qGone
  have hlive :
      OoRespOptionSound
        (n := n) (psi := psi) (kappa := kappa)
        kind qDest
        (ooRespBumpTo
          (n := n) (psi := psi) (kappa := kappa)
          kind base next g).live := by
    unfold OoRespOptionSound
    intro z' hz'
    cases hg : g with
    | none =>
        simp only
          [ooRespBumpTo, hg] at hz'
        cases hz'
    | some z =>
        by_cases hv :
            ooRespLocalValid kind base next
        · simp only
            [ooRespBumpTo,
              hg, if_pos hv] at hz'
          cases hz'
          constructor
          · exact htok
          · exact
              ooRespLocalValid_of_dist_eq
                kind base qDest next hdist hv
        · simp only
            [ooRespBumpTo,
              hg, if_neg hv] at hz'
          cases hz'
  exact
    And.intro
      (And.intro hnone hlive)
      (And.intro hlive hnone)




private def ooRespOneResponder
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) : State psi kappa :=
  if r.mode = true ∧ bit ≠ r.id then
    sourceBirth r
  else if r.mode = false then
    { r with id := bit }
  else
    r




private theorem ooRespOneResponder_dist
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) :
    (ooRespOneResponder r bit).dist =
      r.dist := by
  unfold ooRespOneResponder
  by_cases hbirth :
      r.mode = true ∧ bit ≠ r.id
  · rw [if_pos hbirth, ooRespSourceBirth_eq] <;> rfl
  · rw [if_neg hbirth]
    by_cases hmode : r.mode = false
    · rw [if_pos hmode]
    · rw [if_neg hmode]




private def ooRespPhysicalFinish
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let moveLeft :=
    fun (l r : State psi kappa) =>
      match tokenAt kind r with
      | none =>
          (l, r)
      | some t =>
          let c := decodeOffset psi (tokenCode t)
          if c = -1 then
            let next :=
              ooRespNegTurnNext
                hpsi l.id t
            let l := sourceSet kind l (some next)
            let r := sourceSet kind r none
            (l, r)
          else if hm2 : c <= -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let nextOffset :=
              encodeOffset psi (c + 1) (by
                rcases hc with hn | hp
                · left
                  omega
                · exfalso
                  omega)
            let l :=
              sourceSet kind l
                (some
                  (ooRespMkToken
                    nextOffset t.1.2 t.2))
            let r := sourceSet kind r none
            (l, r)
          else
            (l, r)
  match tokenAt kind l with
  | none =>
      moveLeft l r
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if c = 1 then
        let bit := tokenBitBool t
        let r :=
          ooRespOneResponder r bit
        let r :=
          sourceSet kind r
            (some
              (ooRespMkToken
                (offsetNegPsiPlusOneCode psi hpsi)
                t.1.2 t.2))
        let l := sourceSet kind l none
        (l, r)
      else if hc2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let nextOffset :=
          encodeOffset psi (c - 1) (by
            rcases hc with hn | hp
            · exfalso
              omega
            · right
              omega)
        let r :=
          sourceSet kind r
            (some
              (ooRespMkToken
                nextOffset t.1.2 t.2))
        let l := sourceSet kind l none
        (l, r)
      else
        moveLeft l r




private def ooRespGhostFinish
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match lv with
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if c = 1 then
        let next :=
          ooRespMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          ooRespBumpTo kind baseR next gl
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          ooRespMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          ooRespBumpTo kind baseR next gl
        ⟨none, b.live, b.done⟩
      else
        match rv with
        | none =>
            ⟨gl, gr, []⟩
        | some tr =>
            let cr :=
              decodeOffset psi (tokenCode tr)
            if cr = -1 then
              let next :=
                ooRespNegTurnNext
                  hpsi baseL.id tr
              let b :=
                ooRespBumpTo
                  kind baseL next gr
              ⟨b.live, none, b.done⟩
            else if hm2 : cr <= -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                ooRespMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                ooRespBumpTo
                  kind baseL next gr
              ⟨b.live, none, b.done⟩
            else
              ⟨gl, gr, []⟩
  | none =>
      match rv with
      | none =>
          ⟨gl, gr, []⟩
      | some tr =>
          let cr :=
            decodeOffset psi (tokenCode tr)
          if cr = -1 then
            let next :=
              ooRespNegTurnNext
                hpsi baseL.id tr
            let b :=
              ooRespBumpTo
                kind baseL next gr
            ⟨b.live, none, b.done⟩
          else if hm2 : cr <= -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              ooRespMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b :=
              ooRespBumpTo
                kind baseL next gr
            ⟨b.live, none, b.done⟩
          else
            ⟨gl, gr, []⟩




private theorem ooRespGhostMoveToken_finish_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (hleft :
      OoRespAlignedSound
        kind l lv gl)
    (hright :
      OoRespAlignedSound
        kind r rv gr)
    (hLdist : l.dist = baseL.dist)
    (hRdist : r.dist = baseR.dist)
    (hLid : l.id = baseL.id) :
    let q :=
      ooRespPhysicalFinish
        hpsi kind l r
    let g :=
      ooRespGhostFinish
        hpsi kind baseL baseR lv rv gl gr
    And
      (OoRespOptionSound
        kind q.1 g.left)
      (OoRespOptionSound
        kind q.2 g.right) := by
  cases lv with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [ooRespPhysicalFinish,
            ooRespGhostFinish,
            hleft.1, if_pos h1]
        let next :=
          ooRespMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let bit := tokenBitBool t
        let r1 := ooRespOneResponder r bit
        have hb :=
          ooRespGhostMoveToken_bumpTo_move
            (n := n) (psi := psi) (kappa := kappa)
            kind baseR
            (sourceSet kind l none)
            (sourceSet kind r1 (some next))
            next gl
            (ooRespSourceSet_token
              kind r1 (some next))
            ((ooRespSourceSet_dist
                kind r1 (some next)).trans
              ((ooRespOneResponder_dist
                  r bit).trans hRdist))
        simpa only [next, bit, r1] using hb.1
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [ooRespPhysicalFinish,
              ooRespGhostFinish,
              hleft.1,
              if_neg h1, dif_pos h2]
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            ooRespMkToken
              (encodeOffset psi
                (decodeOffset psi (tokenCode t) - 1)
                (by
                  rcases hc with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
              t.1.2 t.2
          have hb :=
            ooRespGhostMoveToken_bumpTo_move
              (n := n) (psi := psi) (kappa := kappa)
              kind baseR
              (sourceSet kind l none)
              (sourceSet kind r (some next))
              next gl
              (ooRespSourceSet_token
                kind r (some next))
              ((ooRespSourceSet_dist
                  kind r (some next)).trans hRdist)
          simpa only [next] using hb.1
        · cases rv with
          | none =>
              simp only
                [ooRespPhysicalFinish,
                  ooRespGhostFinish,
                  hleft.1, hright.1,
                  if_neg h1, dif_neg h2]
              exact ⟨hleft.2, hright.2⟩
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi
                      (tokenCode tr) = -1
              · simp only
                  [ooRespPhysicalFinish,
                    ooRespGhostFinish,
                    hleft.1, hright.1,
                    if_neg h1, dif_neg h2,
                    if_pos hm1]
                rw [hLid]
                let next :=
                  ooRespNegTurnNext
                    hpsi baseL.id tr
                have hb :=
                  ooRespGhostMoveToken_bumpTo_move
                    (n := n) (psi := psi) (kappa := kappa)
                    kind baseL
                    (sourceSet kind r none)
                    (sourceSet kind l (some next))
                    next gr
                    (ooRespSourceSet_token
                      kind l (some next))
                    ((ooRespSourceSet_dist
                        kind l (some next)).trans hLdist)
                simpa only [next] using hb.2
              · by_cases hm2 :
                  decodeOffset psi
                      (tokenCode tr) <= -2
                · simp only
                    [ooRespPhysicalFinish,
                      ooRespGhostFinish,
                      hleft.1, hright.1,
                      if_neg h1, dif_neg h2,
                      if_neg hm1, dif_pos hm2]
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    ooRespMkToken
                      (encodeOffset psi
                        (decodeOffset psi
                            (tokenCode tr) + 1)
                        (by
                          rcases hc with hn | hp
                          · left
                            omega
                          · exfalso
                            omega))
                      tr.1.2 tr.2
                  have hb :=
                    ooRespGhostMoveToken_bumpTo_move
                      (n := n) (psi := psi) (kappa := kappa)
                      kind baseL
                      (sourceSet kind r none)
                      (sourceSet kind l (some next))
                      next gr
                      (ooRespSourceSet_token
                        kind l (some next))
                      ((ooRespSourceSet_dist
                          kind l (some next)).trans hLdist)
                  simpa only [next] using hb.2
                · simp only
                    [ooRespPhysicalFinish,
                      ooRespGhostFinish,
                      hleft.1, hright.1,
                      if_neg h1, dif_neg h2,
                      if_neg hm1, dif_neg hm2]
                  exact ⟨hleft.2, hright.2⟩
  | none =>
      cases rv with
      | none =>
          simp only
            [ooRespPhysicalFinish,
              ooRespGhostFinish,
              hleft.1, hright.1]
          exact ⟨hleft.2, hright.2⟩
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [ooRespPhysicalFinish,
                ooRespGhostFinish,
                hleft.1, hright.1,
                if_pos hm1]
            rw [hLid]
            let next :=
              ooRespNegTurnNext
                hpsi baseL.id tr
            have hb :=
              ooRespGhostMoveToken_bumpTo_move
                (n := n) (psi := psi) (kappa := kappa)
                kind baseL
                (sourceSet kind r none)
                (sourceSet kind l (some next))
                next gr
                (ooRespSourceSet_token
                  kind l (some next))
                ((ooRespSourceSet_dist
                    kind l (some next)).trans hLdist)
            simpa only [next] using hb.2
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [ooRespPhysicalFinish,
                  ooRespGhostFinish,
                  hleft.1, hright.1,
                  if_neg hm1, dif_pos hm2]
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                ooRespMkToken
                  (encodeOffset psi
                    (decodeOffset psi (tokenCode tr) + 1)
                    (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                  tr.1.2 tr.2
              have hb :=
                ooRespGhostMoveToken_bumpTo_move
                  (n := n) (psi := psi) (kappa := kappa)
                  kind baseL
                  (sourceSet kind r none)
                  (sourceSet kind l (some next))
                  next gr
                  (ooRespSourceSet_token
                    kind l (some next))
                  ((ooRespSourceSet_dist
                      kind l (some next)).trans hLdist)
              simpa only [next] using hb.2
            · simp only
                [ooRespPhysicalFinish,
                  ooRespGhostFinish,
                  hleft.1, hright.1,
                  if_neg hm1, dif_neg hm2]
              exact ⟨hleft.2, hright.2⟩




private theorem ooRespGhostMoveToken_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    let q := moveToken hpsi kind l r
    let g :=
      ooRespGhostMoveToken
        hpsi kind step site l r gl gr
    And
      (OoRespOptionSound kind q.1 g.left)
      (OoRespOptionSound kind q.2 g.right) := by
  classical
  dsimp only
  rw [← ooRespMoveToken_eq hpsi kind l r]


  let l0 := sourceClear kind l
  let r0 := sourceClear kind r
  let lv0 := ooRespLiveValue kind l
  let rv0 := ooRespLiveValue kind r
  let gl0 := ooRespLiveShadow kind l gl
  let gr0 := ooRespLiveShadow kind r gr


  have hL0 :
      OoRespAlignedSound
        kind l0 lv0 gl0 := by
    simpa only [l0, lv0, gl0] using
      ooRespLiveShadow_aligned
        kind l gl
  have hR0 :
      OoRespAlignedSound
        kind r0 rv0 gr0 := by
    simpa only [r0, rv0, gr0] using
      ooRespLiveShadow_aligned
        kind r gr
  have hL0fields :=
    ooRespSourceClear_fields kind l
  have hR0fields :=
    ooRespSourceClear_fields kind r
  have hL0dist : l0.dist = l.dist := by
    simpa only [l0] using hL0fields.1
  have hR0dist : r0.dist = r.dist := by
    simpa only [r0] using hR0fields.1
  have hL0last : l0.last = l.last := by
    simpa only [l0] using hL0fields.2.1
  have hR0last : r0.last = r.last := by
    simpa only [r0] using hR0fields.2.1
  have hL0id : l0.id = l.id := by
    simpa only [l0] using hL0fields.2.2


  by_cases hlast :
      l.last = false ∧ r.last = false
  · have hlast0 :
        l0.last = false ∧ r0.last = false := by
      exact
        ⟨hL0last.trans hlast.1,
          hR0last.trans hlast.2⟩


    let hb : Prop :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      ooRespBirthGhost
        hpsi kind step site l.id
    let l1 : State psi kappa :=
      if hb then
        sourceSet kind l0 (some birth.value)
      else
        l0
    let lv1 : Option (TokenData psi) :=
      if hb then some birth.value else lv0
    let gl1 : Option (GhostToken n psi) :=
      if hb then some birth else gl0


    have hL1 :
        OoRespAlignedSound
          kind l1 lv1 gl1 := by
      by_cases hbirth : hb
      · have hdist0 :
            l0.dist.val = tokenD' psi kind := by
          have hval :=
            congrArg Fin.val hL0dist
          exact hval.trans hbirth.1
        have hpair :=
          ooRespGhostMoveToken_birthGhost
            hpsi kind step site l.id
            l0 r gr hdist0
        simp only
          [l1, lv1, gl1, if_pos hbirth]
        exact
          And.intro
            (ooRespSourceSet_token
              kind l0 (some birth.value))
            hpair.1
      · simpa only
          [l1, lv1, gl1, if_neg hbirth]
          using hL0


    have hL1dist : l1.dist = l.dist := by
      by_cases hbirth : hb
      · simp only [l1, if_pos hbirth]
        exact
          (ooRespSourceSet_dist
            kind l0 (some birth.value)).trans
            hL0dist
      · simpa only [l1, if_neg hbirth]
          using hL0dist


    have hL1id : l1.id = l.id := by
      by_cases hbirth : hb
      · simp only [l1, if_pos hbirth]
        exact
          (ooRespSourceSet_id
            kind l0 (some birth.value)).trans
            hL0id
      · simpa only [l1, if_neg hbirth]
          using hL0id


    let collide : Prop :=
      lv1 ≠ none ∧ rv0 ≠ none
    let l2 : State psi kappa :=
      if collide then
        sourceSet kind l1 none
      else
        l1
    let lv2 : Option (TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (GhostToken n psi) :=
      if collide then none else gl1


    have hL2 :
        OoRespAlignedSound
          kind l2 lv2 gl2 := by
      by_cases hcol : collide
      · simp only
          [l2, lv2, gl2, if_pos hcol]
        exact
          And.intro
            (ooRespSourceSet_token
              kind l1 none)
            (ooRespOptionSound_none
              kind (sourceSet kind l1 none))
      · simpa only
          [l2, lv2, gl2, if_neg hcol]
          using hL1


    have hL2dist : l2.dist = l.dist := by
      by_cases hcol : collide
      · simp only [l2, if_pos hcol]
        exact
          (ooRespSourceSet_dist
            kind l1 none).trans hL1dist
      · simpa only [l2, if_neg hcol]
          using hL1dist


    have hL2id : l2.id = l.id := by
      by_cases hcol : collide
      · simp only [l2, if_pos hcol]
        exact
          (ooRespSourceSet_id
            kind l1 none).trans hL1id
      · simpa only [l2, if_neg hcol]
          using hL1id


    have hBirthPhysIff :
        (l0.dist.val = tokenD' psi kind ∧
          tokenAt kind l0 = none) ↔ hb := by
      dsimp only [hb]
      have hdistVal :=
        congrArg Fin.val hL0dist
      constructor
      · intro h
        exact
          ⟨hdistVal.symm.trans h.1,
            hL0.1.symm.trans h.2⟩
      · intro h
        exact
          ⟨hdistVal.trans h.1,
            hL0.1.trans h.2⟩


    have hCollPhysIff :
        (tokenAt kind l1 ≠ none ∧
          tokenAt kind r0 ≠ none) ↔ collide := by
      dsimp only [collide]
      constructor
      · intro h
        constructor
        · intro hv
          apply h.1
          exact hL1.1.trans hv
        · intro hv
          apply h.2
          exact hR0.1.trans hv
      · intro h
        constructor
        · intro hv
          apply h.1
          exact hL1.1.symm.trans hv
        · intro hv
          apply h.2
          exact hR0.1.symm.trans hv


    have hphys :
        ooRespMoveToken hpsi kind l r =
          ooRespPhysicalFinish
            hpsi kind l2 r0 := by
      by_cases hbirth : hb
      · have hbirth0 :=
          hBirthPhysIff.mpr hbirth
        by_cases hcol : collide
        · have hcol0 :=
            hCollPhysIff.mpr hcol
          simp only
            [l1, l0, r0, birth,
              ooRespBirthGhost,
              if_pos hbirth] at hcol0
          unfold ooRespMoveToken
            ooRespPhysicalFinish
            ooRespOneResponder
          rw [if_pos hlast0, if_pos hbirth0]
          rw [hL0id]
          simp only [if_pos hcol0]
          try simp only
            [l2, l1, if_pos hcol,
              if_pos hbirth] <;> rfl
        · have hcol0 :
              ¬ (tokenAt kind l1 ≠ none ∧
                tokenAt kind r0 ≠ none) := by
            intro h
            exact hcol (hCollPhysIff.mp h)
          simp only
            [l1, l0, r0, birth,
              ooRespBirthGhost,
              if_pos hbirth] at hcol0
          unfold ooRespMoveToken
            ooRespPhysicalFinish
            ooRespOneResponder
          rw [if_pos hlast0, if_pos hbirth0]
          rw [hL0id]
          simp only [if_neg hcol0]
          try simp only
            [l2, l1, if_neg hcol,
              if_pos hbirth] <;> rfl
      · have hbirth0 :
            ¬ (l0.dist.val = tokenD' psi kind ∧
              tokenAt kind l0 = none) := by
          intro h
          exact hbirth (hBirthPhysIff.mp h)
        by_cases hcol : collide
        · have hcol0 :=
            hCollPhysIff.mpr hcol
          simp only
            [l1, l0, r0, if_neg hbirth] at hcol0
          unfold ooRespMoveToken
            ooRespPhysicalFinish
            ooRespOneResponder
          rw [if_pos hlast0, if_neg hbirth0]
          simp only [if_pos hcol0]
          try simp only
            [l2, l1, if_pos hcol,
              if_neg hbirth] <;> rfl
        · have hcol0 :
              ¬ (tokenAt kind l1 ≠ none ∧
                tokenAt kind r0 ≠ none) := by
            intro h
            exact hcol (hCollPhysIff.mp h)
          simp only
            [l1, l0, r0, if_neg hbirth] at hcol0
          unfold ooRespMoveToken
            ooRespPhysicalFinish
            ooRespOneResponder
          rw [if_pos hlast0, if_neg hbirth0]
          simp only [if_neg hcol0]
          try simp only
            [l2, l1, if_neg hcol,
              if_neg hbirth] <;> rfl


    have hghost :
        ooRespGhostMoveToken
            hpsi kind step site l r gl gr =
          ooRespGhostFinish
            hpsi kind l r lv2 rv0 gl2 gr0 := by
      unfold ooRespGhostMoveToken
        ooRespGhostFinish
      rw [if_pos hlast] <;> rfl


    have hfinish :=
      ooRespGhostMoveToken_finish_sound
        hpsi kind l r l2 r0
        lv2 rv0 gl2 gr0
        hL2 hR0 hL2dist hR0dist hL2id


    rw [hphys, hghost]
    exact hfinish


  · have hlast0 :
        ¬ (l0.last = false ∧
          r0.last = false) := by
      intro h
      apply hlast
      exact
        ⟨hL0last.symm.trans h.1,
          hR0last.symm.trans h.2⟩
    have hphys :
        ooRespMoveToken hpsi kind l r =
          (l0, r0) := by
      unfold ooRespMoveToken
      rw [if_neg hlast0] <;> rfl
    have hghost :
        ooRespGhostMoveToken
            hpsi kind step site l r gl gr =
          ⟨gl0, gr0, []⟩ := by
      unfold ooRespGhostMoveToken
      rw [if_neg hlast] <;> rfl
    have hstay :=
      ooRespGhostMoveToken_liveShadow_stay
        kind l r gl gr
    rw [hphys, hghost]
    simpa only [l0, r0, gl0, gr0]
      using hstay


private theorem ooRespGhostMove_valueSound
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    (∀ z' : GhostToken n psi,
      (ooRespGhostMoveToken
          hpsi kind step site l r gl gr).left =
        some z' →
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        some z'.value) ∧
    (∀ z' : GhostToken n psi,
      (ooRespGhostMoveToken
          hpsi kind step site l r gl gr).right =
        some z' →
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some z'.value) := by
  have hs :=
    ooRespGhostMoveToken_sound
      hpsi kind step site l r gl gr
  dsimp only at hs
  constructor
  · intro z' hpost
    exact (hs.1 z' hpost).1
  · intro z' hpost
    exact (hs.2 z' hpost).1
private theorem ooRespSameId_liveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      ooRespLiveShadow kind q g = some z') :
    ∃ z0 : GhostToken n psi,
      g = some z0 ∧ z' = z0 := by
  cases hg : g with
  | none =>
      have hbad :
          (none : Option (GhostToken n psi)) =
            some z' := by
        simpa [ooRespLiveShadow, hg] using hpost
      cases hbad
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          have hbad :
              (none : Option (GhostToken n psi)) =
                some z' := by
            simpa [ooRespLiveShadow, hg, ht] using hpost
          cases hbad
      | some t =>
          by_cases hkeep :
              z0.value = t ∧
                ooRespLocalValid kind q t
          · have hsome :
                some z0 = some z' := by
              simpa
                [ooRespLiveShadow, hg, ht,
                  if_pos hkeep]
                using hpost
            have hz : z0 = z' :=
              Option.some.inj hsome
            exact ⟨z0, rfl, hz.symm⟩
          · have hbad :
                (none : Option (GhostToken n psi)) =
                  some z' := by
              simpa
                [ooRespLiveShadow, hg, ht,
                  if_neg hkeep]
                using hpost
            cases hbad


private theorem ooRespSameId_liveShadow_oldResponder
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (z z' : GhostToken n psi)
    (hpost :
      ooRespLiveShadow kind q (some z) =
        some z') :
    z' = z ∧
      ooRespLiveValue kind q = some z.value ∧
      ooRespLocalValid kind q z.value := by
  cases ht : tokenAt kind q with
  | none =>
      have hbad :
          (none : Option (GhostToken n psi)) =
            some z' := by
        simpa
          [ooRespLiveShadow, ht]
          using hpost
      cases hbad
  | some t =>
      by_cases hkeep :
          z.value = t ∧
            ooRespLocalValid kind q t
      · have hsome :
            some z = some z' := by
          simpa
            [ooRespLiveShadow, ht,
              if_pos hkeep]
            using hpost
        have hz : z = z' :=
          Option.some.inj hsome
        have hlive :
            ooRespLiveValue kind q =
              some z.value := by
          unfold ooRespLiveValue
          rw [ht]
          dsimp only
          rw [if_pos hkeep.2]
          exact congrArg some hkeep.1.symm
        have hvalid :
            ooRespLocalValid kind q z.value := by
          rw [hkeep.1]
          exact hkeep.2
        exact ⟨hz.symm, hlive, hvalid⟩
      · have hbad :
            (none : Option (GhostToken n psi)) =
              some z' := by
          simpa
            [ooRespLiveShadow, ht,
              if_neg hkeep]
            using hpost
        cases hbad


private theorem ooRespSameId_bump_live_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (next : TokenData psi)
    (g : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      (ooRespBumpTo kind qDest next g).live =
        some z') :
    ∃ z0 : GhostToken n psi,
      g = some z0 ∧
      z'.lmeta = ghostStepLineageAdvance z0.lmeta ∧
      z'.value = next := by
  cases hg : g with
  | none =>
      have hbad :
          (none : Option (GhostToken n psi)) =
            some z' := by
        simpa [ooRespBumpTo, hg] using hpost
      cases hbad
  | some z0 =>
      by_cases hv :
          ooRespLocalValid kind qDest next
      · have hsome :
            some
                ({ value := next
                   lmeta :=
                     ghostStepLineageAdvance z0.lmeta } :
                  GhostToken n psi) =
              some z' := by
          simpa
            [ooRespBumpTo, hg, if_pos hv]
            using hpost
        have hz :
            ({ value := next
               lmeta :=
                 ghostStepLineageAdvance z0.lmeta } :
              GhostToken n psi) = z' :=
          Option.some.inj hsome
        subst z'
        exact ⟨z0, rfl, rfl, rfl⟩
      · have hbad :
            (none : Option (GhostToken n psi)) =
              some z' := by
          simpa
            [ooRespBumpTo, hg, if_neg hv]
            using hpost
        cases hbad


private theorem ooRespSameId_advance_id
    {n : Nat}
    (m : LineageMeta n) :
    (ghostStepLineageAdvance m).id = m.id := by
  rfl


private theorem ooRespSameId_negTurn_decode
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (ooRespNegTurnNext hpsi sourceBit t)) =
      ((psi : Nat) : Int) := by
  unfold ooRespNegTurnNext
  by_cases hc : t.2 = (1 : Fin 2)
  · rw [if_pos hc]
    simpa [ooRespMkToken, tokenCode]
      using decodeOffset_psi psi hpsi
  · rw [if_neg hc]
    simpa [ooRespMkToken, tokenCode]
      using decodeOffset_psi psi hpsi


private structure OoRespSameIdPrep
    (n psi : Nat) where
  lv : Option (TokenData psi)
  rv : Option (TokenData psi)
  gl : Option (GhostToken n psi)
  gr : Option (GhostToken n psi)


private def ooRespSameIdPrep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    OoRespSameIdPrep n psi :=
  let lv0 := ooRespLiveValue kind l
  let rv0 := ooRespLiveValue kind r
  let gl0 := ooRespLiveShadow kind l gl
  let gr0 := ooRespLiveShadow kind r gr
  let hb :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    ooRespBirthGhost hpsi kind step site l.id
  let lv1 :=
    if hb then some birth.value else lv0
  let gl1 :=
    if hb then some birth else gl0
  let collide := lv1 ≠ none ∧ rv0 ≠ none
  { lv := if collide then none else lv1
    rv := rv0
    gl := if collide then none else gl1
    gr := gr0 }


private theorem ooRespSameIdPrep_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    (ooRespSameIdPrep
        hpsi kind step site l r gl gr).rv =
        ooRespLiveValue kind r ∧
      (ooRespSameIdPrep
        hpsi kind step site l r gl gr).gr =
        ooRespLiveShadow kind r gr := by
  exact ⟨rfl, rfl⟩


private theorem ooRespSameIdPrep_left_id_ne
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step) :
    ∀ u : GhostToken n psi,
      (ooRespSameIdPrep
          hpsi kind step site l r gl (some z)).gl =
        some u →
      u.lmeta.id ≠ z.lmeta.id := by
  intro u hu
  cases hlv : ooRespLiveValue kind l with
  | none =>
      by_cases hdist :
          l.dist.val = tokenD' psi kind
      · cases hrv : ooRespLiveValue kind r with
        | none =>
            have hsome :
                some
                    (ooRespBirthGhost
                      hpsi kind step site l.id) =
                  some u := by
              simpa
                [ooRespSameIdPrep, hlv, hdist, hrv]
                using hu
            have hub :
                ooRespBirthGhost
                    hpsi kind step site l.id =
                  u :=
              Option.some.inj hsome
            subst u
            intro huid
            apply hNotFresh
            have hrev :
                z.lmeta.id =
                  (ooRespBirthGhost
                    hpsi kind step site l.id).lmeta.id :=
              huid.symm
            simpa [ooRespBirthGhost] using hrev
        | some tr =>
            have hbad : False := by
              simpa
                [ooRespSameIdPrep, hlv, hdist, hrv]
                using hu
            exact False.elim hbad
      · have hshadow :
            ooRespLiveShadow kind l gl =
              some u := by
          simpa
            [ooRespSameIdPrep, hlv, hdist]
            using hu
        obtain ⟨u0, hgl, hu0⟩ :=
          ooRespSameId_liveShadow_source
            kind l gl u hshadow
        rw [hu0]
        exact hNoLeft u0 hgl
  | some tl =>
      cases hrv : ooRespLiveValue kind r with
      | none =>
          have hshadow :
              ooRespLiveShadow kind l gl =
                some u := by
            simpa
              [ooRespSameIdPrep, hlv, hrv]
              using hu
          obtain ⟨u0, hgl, hu0⟩ :=
            ooRespSameId_liveShadow_source
              kind l gl u hshadow
          rw [hu0]
          exact hNoLeft u0 hgl
      | some tr =>
          have hbad : False := by
            simpa
              [ooRespSameIdPrep, hlv, hrv]
              using hu
          exact False.elim hbad


private theorem ooRespSameId_gate_eq_finish
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgate :
      l.last = false ∧ r.last = false) :
    ooRespGhostMoveToken
        hpsi kind step site l r gl gr =
      ooRespGhostFinish
        hpsi kind l r
        (ooRespSameIdPrep
          hpsi kind step site l r gl gr).lv
        (ooRespSameIdPrep
          hpsi kind step site l r gl gr).rv
        (ooRespSameIdPrep
          hpsi kind step site l r gl gr).gl
        (ooRespSameIdPrep
          hpsi kind step site l r gl gr).gr := by
  unfold ooRespGhostMoveToken
    ooRespSameIdPrep
  rw [if_pos hgate]
  rfl


private theorem ooRespSameId_gate_closed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgate :
      ¬ (l.last = false ∧ r.last = false)) :
    ooRespGhostMoveToken
        hpsi kind step site l r gl gr =
      ⟨ooRespLiveShadow kind l gl,
        ooRespLiveShadow kind r gr, []⟩ := by
  unfold ooRespGhostMoveToken
  rw [if_neg hgate]


private def ooRespSameIdMoveLeft
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match rv with
  | none =>
      ⟨gl, gr, []⟩
  | some tr =>
      let cr := decodeOffset psi (tokenCode tr)
      if cr = -1 then
        let next :=
          ooRespNegTurnNext hpsi baseL.id tr
        let b :=
          ooRespBumpTo kind baseL next gr
        ⟨b.live, none, b.done⟩
      else if hm2 : cr ≤ -2 then
        have hc : ValidOffset psi cr :=
          decodeOffset_valid
            psi (by omega) (tokenCode tr)
        let next :=
          ooRespMkToken
            (encodeOffset psi (cr + 1) (by
              rcases hc with hn | hp
              · left
                omega
              · exfalso
                omega))
            tr.1.2 tr.2
        let b :=
          ooRespBumpTo kind baseL next gr
        ⟨b.live, none, b.done⟩
      else
        ⟨gl, gr, []⟩


private theorem ooRespSameIdMoveLeft_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    ooRespSameIdMoveLeft
        hpsi kind baseL none gl gr =
      ⟨gl, gr, []⟩ := by
  rfl


private theorem ooRespSameIdMoveLeft_negTurn_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hneg :
      decodeOffset psi (tokenCode tr) = -1) :
    (ooRespSameIdMoveLeft
        hpsi kind baseL (some tr) gl gr).right =
      none := by
  unfold ooRespSameIdMoveLeft
  dsimp only
  rw [if_pos hneg]


private theorem ooRespSameIdMoveLeft_negTurn_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hneg :
      decodeOffset psi (tokenCode tr) = -1)
    (hpost :
      (ooRespSameIdMoveLeft
          hpsi kind baseL (some tr) gl gr).left =
        some z') :
    ∃ u : GhostToken n psi,
      gr = some u ∧
      z'.lmeta = ghostStepLineageAdvance u.lmeta ∧
      decodeOffset psi (tokenCode z'.value) =
        ((psi : Nat) : Int) := by
  unfold ooRespSameIdMoveLeft at hpost
  dsimp only at hpost
  rw [if_pos hneg] at hpost
  dsimp only at hpost
  obtain ⟨u, hgr, hmeta, hvalue⟩ :=
    ooRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseL)
      (g := gr)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgr, hmeta, ?_⟩
  rw [hvalue]
  exact
    ooRespSameId_negTurn_decode
      hpsi baseL.id tr


private theorem ooRespSameIdMoveLeft_negative_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hnot :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hneg :
      decodeOffset psi (tokenCode tr) ≤ -2) :
    (ooRespSameIdMoveLeft
        hpsi kind baseL (some tr) gl gr).right =
      none := by
  unfold ooRespSameIdMoveLeft
  dsimp only
  rw [if_neg hnot, dif_pos hneg]


private theorem ooRespSameIdMoveLeft_negative_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hnot :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hneg :
      decodeOffset psi (tokenCode tr) ≤ -2)
    (hpost :
      (ooRespSameIdMoveLeft
          hpsi kind baseL (some tr) gl gr).left =
        some z') :
    ∃ u : GhostToken n psi,
      gr = some u ∧
      z'.lmeta = ghostStepLineageAdvance u.lmeta ∧
      decodeOffset psi (tokenCode z'.value) =
        decodeOffset psi (tokenCode tr) + 1 := by
  unfold ooRespSameIdMoveLeft at hpost
  dsimp only at hpost
  rw [if_neg hnot, dif_pos hneg] at hpost
  dsimp only at hpost
  obtain ⟨u, hgr, hmeta, hvalue⟩ :=
    ooRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseL)
      (g := gr)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgr, hmeta, ?_⟩
  rw [hvalue]
  simp only
    [ooRespMkToken, tokenCode, decode_encode]


private theorem ooRespSameIdMoveLeft_stay
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hnot :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hnotNeg :
      ¬ decodeOffset psi (tokenCode tr) ≤ -2) :
    ooRespSameIdMoveLeft
        hpsi kind baseL (some tr) gl gr =
      ⟨gl, gr, []⟩ := by
  unfold ooRespSameIdMoveLeft
  dsimp only
  rw [if_neg hnot, dif_neg hnotNeg]


private theorem ooRespSameIdFinish_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) :
    ooRespGhostFinish
        hpsi kind baseL baseR none rv gl gr =
      ooRespSameIdMoveLeft
        hpsi kind baseL rv gl gr := by
  rfl


private theorem ooRespSameIdFinish_posOne_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 :
      decodeOffset psi (tokenCode t) = 1) :
    (ooRespGhostFinish
        hpsi kind baseL baseR
        (some t) rv gl gr).left = none := by
  unfold ooRespGhostFinish
  dsimp only
  rw [if_pos h1]


private theorem ooRespSameIdFinish_posOne_right_source
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (h1 :
      decodeOffset psi (tokenCode t) = 1)
    (hpost :
      (ooRespGhostFinish
          hpsi kind baseL baseR
          (some t) rv gl gr).right =
        some z') :
    ∃ u : GhostToken n psi,
      gl = some u ∧ z'.lmeta.id = u.lmeta.id := by
  unfold ooRespGhostFinish at hpost
  dsimp only at hpost
  rw [if_pos h1] at hpost
  dsimp only at hpost
  obtain ⟨u, hgl, hmeta, _hvalue⟩ :=
    ooRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseR)
      (g := gl)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgl, ?_⟩
  have hm :=
    congrArg (fun m : LineageMeta n => m.id) hmeta
  simpa [ghostStepLineageAdvance] using hm


private theorem ooRespSameIdFinish_positive_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      2 ≤ decodeOffset psi (tokenCode t)) :
    (ooRespGhostFinish
        hpsi kind baseL baseR
        (some t) rv gl gr).left = none := by
  unfold ooRespGhostFinish
  dsimp only
  rw [if_neg h1, dif_pos h2]


private theorem ooRespSameIdFinish_positive_right_source
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      2 ≤ decodeOffset psi (tokenCode t))
    (hpost :
      (ooRespGhostFinish
          hpsi kind baseL baseR
          (some t) rv gl gr).right =
        some z') :
    ∃ u : GhostToken n psi,
      gl = some u ∧ z'.lmeta.id = u.lmeta.id := by
  unfold ooRespGhostFinish at hpost
  dsimp only at hpost
  rw [if_neg h1, dif_pos h2] at hpost
  dsimp only at hpost
  obtain ⟨u, hgl, hmeta, _hvalue⟩ :=
    ooRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseR)
      (g := gl)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgl, ?_⟩
  have hm :=
    congrArg (fun m : LineageMeta n => m.id) hmeta
  simpa [ghostStepLineageAdvance] using hm


private theorem ooRespSameIdFinish_neutral
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 ≤ decodeOffset psi (tokenCode t)) :
    ooRespGhostFinish
        hpsi kind baseL baseR
        (some t) rv gl gr =
      ooRespSameIdMoveLeft
        hpsi kind baseL rv gl gr := by
  unfold ooRespGhostFinish
  dsimp only
  rw [if_neg h1, dif_neg h2]
  rfl


private theorem ooRespSameIdMoveLeft_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (rv : Option (TokenData psi))
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hrv :
      rv = ooRespLiveValue kind baseR)
    (hpost :
      (ooRespSameIdMoveLeft
          hpsi kind baseL rv gl
          (ooRespLiveShadow kind baseR (some z))).right =
        some z') :
    z' = z ∧
      0 < decodeOffset psi (tokenCode z.value) := by
  cases hrvCase : rv with
  | none =>
      rw [hrvCase] at hpost
      rw [ooRespSameIdMoveLeft_none] at hpost
      have hs :=
        ooRespSameId_liveShadow_oldResponder
          kind baseR z z' hpost
      have hnone :
          (none : Option (TokenData psi)) =
            some z.value :=
        hrvCase.symm.trans (hrv.trans hs.2.1)
      cases hnone
  | some tr =>
      rw [hrvCase] at hpost
      by_cases hm1 :
          decodeOffset psi (tokenCode tr) = -1
      · have hnone :=
          ooRespSameIdMoveLeft_negTurn_right
            hpsi kind baseL tr gl
            (ooRespLiveShadow kind baseR (some z))
            hm1
        rw [hnone] at hpost
        cases hpost
      · by_cases hm2 :
          decodeOffset psi (tokenCode tr) ≤ -2
        · have hnone :=
            ooRespSameIdMoveLeft_negative_right
              hpsi kind baseL tr gl
              (ooRespLiveShadow kind baseR (some z))
              hm1 hm2
          rw [hnone] at hpost
          cases hpost
        · have hstay :=
            ooRespSameIdMoveLeft_stay
              hpsi kind baseL tr gl
              (ooRespLiveShadow kind baseR (some z))
              hm1 hm2
          rw [hstay] at hpost
          have hs :=
            ooRespSameId_liveShadow_oldResponder
              kind baseR z z' hpost
          have htr :
              tr = z.value := by
            have hsome :
                some tr = some z.value :=
              hrvCase.symm.trans (hrv.trans hs.2.1)
            exact Option.some.inj hsome
          have hvalid := hs.2.2
          unfold ooRespLocalValid at hvalid
          dsimp only at hvalid
          rcases hvalid with hp | hn
          · exact ⟨hs.1, hp.1⟩
          · rw [htr] at hm1 hm2
            omega


private theorem ooRespSameIdMoveLeft_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (rv : Option (TokenData psi))
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hLeftNoId :
      ∀ u : GhostToken n psi,
        gl = some u →
        u.lmeta.id ≠ z.lmeta.id)
    (hrv :
      rv = ooRespLiveValue kind baseR)
    (hpost :
      (ooRespSameIdMoveLeft
          hpsi kind baseL rv gl
          (ooRespLiveShadow kind baseR (some z))).left =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z'.lmeta = ghostStepLineageAdvance z.lmeta ∧
      ((decodeOffset psi (tokenCode z.value) = -1 ∧
          decodeOffset psi (tokenCode z'.value) =
            ((psi : Nat) : Int)) ∨
        (decodeOffset psi (tokenCode z.value) ≤ -2 ∧
          decodeOffset psi (tokenCode z'.value) =
            decodeOffset psi (tokenCode z.value) + 1)) := by
  cases hrvCase : rv with
  | none =>
      rw [hrvCase] at hpost
      rw [ooRespSameIdMoveLeft_none] at hpost
      exact False.elim ((hLeftNoId z' hpost) hid)
  | some tr =>
      rw [hrvCase] at hpost
      by_cases hm1 :
          decodeOffset psi (tokenCode tr) = -1
      · obtain ⟨u, hshadow, hmeta, hnew⟩ :=
          ooRespSameIdMoveLeft_negTurn_left
            hpsi kind baseL tr gl
            (ooRespLiveShadow kind baseR (some z))
            z' hm1
            (by simpa [hrvCase] using hpost)
        have hs :=
          ooRespSameId_liveShadow_oldResponder
            kind baseR z u hshadow
        rw [hs.1] at hmeta
        have htr :
            tr = z.value := by
          have hsome :
              some tr = some z.value :=
            hrvCase.symm.trans (hrv.trans hs.2.1)
          exact Option.some.inj hsome
        have hold :
            decodeOffset psi (tokenCode z.value) = -1 := by
          simpa [htr] using hm1
        exact ⟨hmeta, Or.inl ⟨hold, hnew⟩⟩
      · by_cases hm2 :
          decodeOffset psi (tokenCode tr) ≤ -2
        · obtain ⟨u, hshadow, hmeta, hnew⟩ :=
            ooRespSameIdMoveLeft_negative_left
              hpsi kind baseL tr gl
              (ooRespLiveShadow kind baseR (some z))
              z' hm1 hm2
              (by simpa [hrvCase] using hpost)
          have hs :=
            ooRespSameId_liveShadow_oldResponder
              kind baseR z u hshadow
          rw [hs.1] at hmeta
          have htr :
              tr = z.value := by
            have hsome :
                some tr = some z.value :=
              hrvCase.symm.trans (hrv.trans hs.2.1)
            exact Option.some.inj hsome
          have hold :
              decodeOffset psi (tokenCode z.value) ≤ -2 := by
            simpa [htr] using hm2
          have hnew' :
              decodeOffset psi (tokenCode z'.value) =
                decodeOffset psi (tokenCode z.value) + 1 := by
            simpa [htr] using hnew
          exact ⟨hmeta, Or.inr ⟨hold, hnew'⟩⟩
        · have hstay :=
            ooRespSameIdMoveLeft_stay
              hpsi kind baseL tr gl
              (ooRespLiveShadow kind baseR (some z))
              hm1 hm2
          have hgl :
              gl = some z' := by
            simpa [hrvCase, hstay] using hpost
          exact False.elim ((hLeftNoId z' hgl) hid)


private theorem ooRespSameIdFinish_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hLeftNoId :
      ∀ u : GhostToken n psi,
        gl = some u →
        u.lmeta.id ≠ z.lmeta.id)
    (hrv :
      rv = ooRespLiveValue kind baseR)
    (hgr :
      gr = ooRespLiveShadow kind baseR (some z))
    (hpost :
      (ooRespGhostFinish
          hpsi kind baseL baseR lv rv gl gr).right =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z' = z ∧
      0 < decodeOffset psi (tokenCode z.value) := by
  rw [hgr] at hpost
  cases hlv : lv with
  | none =>
      rw [hlv] at hpost
      rw [ooRespSameIdFinish_none] at hpost
      exact
        ooRespSameIdMoveLeft_right
          hpsi kind baseL baseR rv gl
          z z' hrv hpost
  | some t =>
      rw [hlv] at hpost
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · obtain ⟨u, hgu, huid⟩ :=
          ooRespSameIdFinish_posOne_right_source
            hpsi kind baseL baseR t rv gl
            (ooRespLiveShadow kind baseR (some z))
            z' h1
            (by simpa [hlv] using hpost)
        have huz :
            u.lmeta.id = z.lmeta.id :=
          huid.symm.trans hid
        exact False.elim ((hLeftNoId u hgu) huz)
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · obtain ⟨u, hgu, huid⟩ :=
            ooRespSameIdFinish_positive_right_source
              hpsi kind baseL baseR t rv gl
              (ooRespLiveShadow kind baseR (some z))
              z' h1 h2
              (by simpa [hlv] using hpost)
          have huz :
              u.lmeta.id = z.lmeta.id :=
            huid.symm.trans hid
          exact False.elim ((hLeftNoId u hgu) huz)
        · have hneutral :=
            ooRespSameIdFinish_neutral
              hpsi kind baseL baseR t rv gl
              (ooRespLiveShadow kind baseR (some z))
              h1 h2
          have hm :
              (ooRespSameIdMoveLeft
                  hpsi kind baseL rv gl
                  (ooRespLiveShadow kind baseR (some z))).right =
                some z' := by
            simpa [hlv, hneutral] using hpost
          exact
            ooRespSameIdMoveLeft_right
              hpsi kind baseL baseR rv gl
              z z' hrv hm


private theorem ooRespSameIdFinish_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hLeftNoId :
      ∀ u : GhostToken n psi,
        gl = some u →
        u.lmeta.id ≠ z.lmeta.id)
    (hrv :
      rv = ooRespLiveValue kind baseR)
    (hgr :
      gr = ooRespLiveShadow kind baseR (some z))
    (hpost :
      (ooRespGhostFinish
          hpsi kind baseL baseR lv rv gl gr).left =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z'.lmeta = ghostStepLineageAdvance z.lmeta ∧
      ((decodeOffset psi (tokenCode z.value) = -1 ∧
          decodeOffset psi (tokenCode z'.value) =
            ((psi : Nat) : Int)) ∨
        (decodeOffset psi (tokenCode z.value) ≤ -2 ∧
          decodeOffset psi (tokenCode z'.value) =
            decodeOffset psi (tokenCode z.value) + 1)) := by
  rw [hgr] at hpost
  cases hlv : lv with
  | none =>
      rw [hlv] at hpost
      rw [ooRespSameIdFinish_none] at hpost
      exact
        ooRespSameIdMoveLeft_left
          hpsi kind baseL baseR rv gl
          z z' hLeftNoId hrv hpost hid
  | some t =>
      rw [hlv] at hpost
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · have hnone :=
          ooRespSameIdFinish_posOne_left
            hpsi kind baseL baseR t rv gl
            (ooRespLiveShadow kind baseR (some z))
            h1
        rw [hnone] at hpost
        cases hpost
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · have hnone :=
            ooRespSameIdFinish_positive_left
              hpsi kind baseL baseR t rv gl
              (ooRespLiveShadow kind baseR (some z))
              h1 h2
          rw [hnone] at hpost
          cases hpost
        · have hneutral :=
            ooRespSameIdFinish_neutral
              hpsi kind baseL baseR t rv gl
              (ooRespLiveShadow kind baseR (some z))
              h1 h2
          have hm :
              (ooRespSameIdMoveLeft
                  hpsi kind baseL rv gl
                  (ooRespLiveShadow kind baseR (some z))).left =
                some z' := by
            simpa [hlv, hneutral] using hpost
          exact
            ooRespSameIdMoveLeft_left
              hpsi kind baseL baseR rv gl
              z z' hLeftNoId hrv hm hid


private theorem ooRespRightSameId
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hpost :
      (ooRespGhostMoveToken
          hpsi kind step site l r gl (some z)).right =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z' = z := by
  classical
  by_cases hgate :
      l.last = false ∧ r.last = false
  · have hnorm :=
      ooRespSameId_gate_eq_finish
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    let P :=
      ooRespSameIdPrep
        hpsi kind step site l r gl (some z)
    have hleft :
        ∀ u : GhostToken n psi,
          P.gl = some u →
          u.lmeta.id ≠ z.lmeta.id := by
      simpa [P] using
        ooRespSameIdPrep_left_id_ne
          hpsi kind step site l r gl z
          hNoLeft hNotFresh
    have hright :=
      ooRespSameIdPrep_right
        hpsi kind step site l r gl (some z)
    have hs :=
      ooRespSameIdFinish_right
        hpsi kind l r
        P.lv P.rv P.gl P.gr z z'
        hleft
        (by simpa [P] using hright.1)
        (by simpa [P] using hright.2)
        (by simpa [P] using hpost)
        hid
    exact hs.1
  · have hnorm :=
      ooRespSameId_gate_closed
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    exact
      (ooRespSameId_liveShadow_oldResponder
        kind r z z' hpost).1


private theorem ooRespRightSameId_positive_of_gate
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hgate :
      l.last = false ∧ r.last = false)
    (hpost :
      (ooRespGhostMoveToken
          hpsi kind step site l r gl (some z)).right =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    0 < decodeOffset psi (tokenCode z.value) := by
  classical
  have hnorm :=
    ooRespSameId_gate_eq_finish
      hpsi kind step site l r gl (some z) hgate
  rw [hnorm] at hpost
  let P :=
    ooRespSameIdPrep
      hpsi kind step site l r gl (some z)
  have hleft :
      ∀ u : GhostToken n psi,
        P.gl = some u →
        u.lmeta.id ≠ z.lmeta.id := by
    simpa [P] using
      ooRespSameIdPrep_left_id_ne
        hpsi kind step site l r gl z
        hNoLeft hNotFresh
  have hright :=
    ooRespSameIdPrep_right
      hpsi kind step site l r gl (some z)
  exact
    (ooRespSameIdFinish_right
      hpsi kind l r
      P.lv P.rv P.gl P.gr z z'
      hleft
      (by simpa [P] using hright.1)
      (by simpa [P] using hright.2)
      (by simpa [P] using hpost)
      hid).2


private theorem ooRespLeftSameId
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hpost :
      (ooRespGhostMoveToken
          hpsi kind step site l r gl (some z)).left =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z'.lmeta = ghostStepLineageAdvance z.lmeta ∧
      ((decodeOffset psi (tokenCode z.value) = -1 ∧
          decodeOffset psi (tokenCode z'.value) =
            ((psi : Nat) : Int)) ∨
        (decodeOffset psi (tokenCode z.value) ≤ -2 ∧
          decodeOffset psi (tokenCode z'.value) =
            decodeOffset psi (tokenCode z.value) + 1)) := by
  classical
  by_cases hgate :
      l.last = false ∧ r.last = false
  · have hnorm :=
      ooRespSameId_gate_eq_finish
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    let P :=
      ooRespSameIdPrep
        hpsi kind step site l r gl (some z)
    have hleft :
        ∀ u : GhostToken n psi,
          P.gl = some u →
          u.lmeta.id ≠ z.lmeta.id := by
      simpa [P] using
        ooRespSameIdPrep_left_id_ne
          hpsi kind step site l r gl z
          hNoLeft hNotFresh
    have hright :=
      ooRespSameIdPrep_right
        hpsi kind step site l r gl (some z)
    exact
      ooRespSameIdFinish_left
        hpsi kind l r
        P.lv P.rv P.gl P.gr z z'
        hleft
        (by simpa [P] using hright.1)
        (by simpa [P] using hright.2)
        (by simpa [P] using hpost)
        hid
  · have hnorm :=
      ooRespSameId_gate_closed
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    obtain ⟨u, hgl, hu⟩ :=
      ooRespSameId_liveShadow_source
        kind l gl z' hpost
    rw [hu] at hid
    exact False.elim ((hNoLeft u hgl) hid)




/-! -----------------------------------------------------------------------
    Physical selected-token and last-field projections
------------------------------------------------------------------------ -/


private theorem ooRespElimTokenLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (eliminateLeaders l r).1 =
      tokenAt kind l := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left l r
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


private theorem ooRespElimTokenRight
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (eliminateLeaders l r).2 =
      tokenAt kind r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right l r
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


private theorem ooRespWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black
        (moveToken hpsi .white l r).1 =
      tokenAt .black l ∧
    tokenAt .black
        (moveToken hpsi .white l r).2 =
      tokenAt .black r := by
  have hi :=
    moveToken_initiator_fields
      hpsi .white l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  constructor
  · simpa [eraseKindToken, tokenAt]
      using hil
  · rcases
      moveToken_responder_fields
        hpsi .white l r with hr | hr
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


private theorem ooRespPplTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := ooRespSelectedInput hpsi kind l r
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).2 := by
  cases kind with
  | black =>
      let p := ooRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw :=
        ooRespWhitePreservesBlack
          hpsi b.1 b.2
      have hel :=
        ooRespElimTokenLeft .black w.1 w.2
      have her :=
        ooRespElimTokenRight .black w.1 w.2
      change
        tokenAt .black
            (eliminateLeaders w.1 w.2).1 =
              tokenAt .black b.1 ∧
          tokenAt .black
            (eliminateLeaders w.1 w.2).2 =
              tokenAt .black b.2
      exact
        ⟨hel.trans hw.1,
          her.trans hw.2⟩
  | white =>
      let p := ooRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hel :=
        ooRespElimTokenLeft .white w.1 w.2
      have her :=
        ooRespElimTokenRight .white w.1 w.2
      change
        tokenAt .white
            (eliminateLeaders w.1 w.2).1 =
              tokenAt .white w.1 ∧
          tokenAt .white
            (eliminateLeaders w.1 w.2).2 =
              tokenAt .white w.2
      exact ⟨hel, her⟩


private theorem ooRespMoveTokenLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.last = l.last ∧
      (moveToken hpsi kind l r).2.last = r.last := by
  have hi :=
    moveToken_initiator_fields hpsi kind l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.last) hi
  have hleft :
      (moveToken hpsi kind l r).1.last = l.last := by
    cases kind <;>
      simpa [eraseKindToken] using hil
  rcases
      moveToken_responder_fields hpsi kind l r
    with hr | hr
  · have hir :=
      congrArg
        (fun q : State psi kappa => q.last) hr
    have hright :
        (moveToken hpsi kind l r).2.last = r.last := by
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken]
          using hir
    exact ⟨hleft, hright⟩
  · have hir :=
      congrArg
        (fun q : State psi kappa => q.last) hr
    have hright :
        (moveToken hpsi kind l r).2.last = r.last := by
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken,
            birthFields]
          using hir
    exact ⟨hleft, hright⟩


private theorem ooRespElimLast
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (eliminateLeaders l r).1.last = l.last ∧
      (eliminateLeaders l r).2.last = r.last := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    ⟨congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hr⟩


private theorem ooRespPplLastPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := ooRespSelectedInput hpsi kind l r
    (ppl hpsi l r).1.last = p.1.last ∧
      (ppl hpsi l r).2.last = p.2.last := by
  cases kind with
  | black =>
      let p := ooRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hb := ooRespMoveTokenLast hpsi .black p.1 p.2
      have hw := ooRespMoveTokenLast hpsi .white b.1 b.2
      have he := ooRespElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            p.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            p.2.last
      exact
        ⟨he.1.trans (hw.1.trans hb.1),
          he.2.trans (hw.2.trans hb.2)⟩
  | white =>
      let p := ooRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw := ooRespMoveTokenLast hpsi .white b.1 b.2
      have he := ooRespElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            b.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            b.2.last
      exact
        ⟨he.1.trans hw.1,
          he.2.trans hw.2⟩


private theorem ooRespGhostStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      ooRespSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    tokenAt kind
        ((ghostStep hpsi ring 0 G e).phys e) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind
        ((ghostStep hpsi ring 0 G e).phys
          (ring.rightNeighbor e)) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).2 := by
  dsimp only
  rw [ghostStep_phys_export]
  have hp :=
    ooRespPplTokenPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    ⟨by rw [hl]; exact hp.1,
      by rw [hr]; exact hp.2⟩


private theorem ooRespGhostStepTokenPairAt
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      ooRespSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys e) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).2 := by
  have hphys :
      (ghostStep hpsi ring step G e).phys =
        (ghostStep hpsi ring 0 G e).phys := by
    calc
      (ghostStep hpsi ring step G e).phys =
          PopulationProtocol.step
            (protocol psi kappa) ring G.phys e :=
        ghostStep_phys_export hpsi ring step G e
      _ = (ghostStep hpsi ring 0 G e).phys :=
        (ghostStep_phys_export hpsi ring 0 G e).symm
  rw [hphys]
  exact
    ooRespGhostStepTokenPair
      hpsi ring G e kind hne


private theorem ooRespGhostStepLastPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      ooRespSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    ((ghostStep hpsi ring step G e).phys e).last =
        p.1.last ∧
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).last =
        p.2.last := by
  dsimp only
  rw [ghostStep_phys_export]
  have hp :=
    ooRespPplLastPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    ⟨by rw [hl]; exact hp.1,
      by rw [hr]; exact hp.2⟩


/-! -----------------------------------------------------------------------
    C_d geometry
------------------------------------------------------------------------ -/


private theorem ooRespCd_fit
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 * psi ≤ n := by
  by_cases hfit : 2 * psi ≤ n
  · exact hfit
  · have hnlt : n < 2 * psi := by
      omega
    have hnpos : 0 < n := ring.hn
    let x0 : Fin (2 * psi) :=
      ⟨0, by omega⟩
    let xn : Fin (2 * psi) :=
      ⟨n, hnlt⟩
    have h0 := (hCd x0).1
    have hn := (hCd xn).1
    have hs :
        shiftRight ring k x0.val =
          shiftRight ring k xn.val := by
      apply Fin.ext
      dsimp [x0, xn]
      simp [shiftRight]
    rw [hs] at h0
    dsimp only [x0, xn] at h0 hn
    cases kind with
    | black =>
        have hmn :
            n % (2 * psi) = n :=
          Nat.mod_eq_of_lt hnlt
        simp only [tokenD'] at h0 hn
        have hzero :
            0 % (2 * psi) = 0 :=
          Nat.zero_mod (by omega)
        have h0' :
            (C (shiftRight ring k n)).dist.val = 0 := by
          calc
            (C (shiftRight ring k n)).dist.val =
                0 % (2 * psi) := h0
            _ = 0 := hzero
        have hn' :
            (C (shiftRight ring k n)).dist.val = n := by
          calc
            (C (shiftRight ring k n)).dist.val =
                (n + 0) % (2 * psi) := hn
            _ = n % (2 * psi) := by rw [Nat.add_zero]
            _ = n := hmn
        omega
    | white =>
        have hmpsi :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        simp only [tokenD'] at h0 hn
        rw [Nat.zero_add, hmpsi] at h0
        have heq :
            psi =
              (n + psi) % (2 * psi) := by
          omega
        by_cases hsmall :
            n + psi < 2 * psi
        · rw [Nat.mod_eq_of_lt hsmall] at heq
          omega
        · have hge :
              2 * psi ≤ n + psi := by
            omega
          have hrem :
              n + psi - 2 * psi <
                2 * psi := by
            omega
          rw [Nat.mod_eq_sub_mod hge,
            Nat.mod_eq_of_lt hrem] at heq
          omega


private theorem ooRespRightNeighbor_ne
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
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


private theorem ooRespLeftNeighborRightNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq :
        i.val + 1 + n - 1 = n + i.val := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem ooRespRightNeighborShiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (d : Nat) :
    ring.rightNeighbor (shiftRight ring k d) =
      shiftRight ring k (d + 1) := by
  apply Fin.ext
  simp only
    [DirectedRing.rightNeighbor, shiftRight]
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem ooRespGhostSound_token
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value := by
  cases kind with
  | black =>
      exact (hsound.1 i z howner).1
  | white =>
      exact (hsound.2 i z howner).1


private theorem ooRespOwner_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2


private theorem ooRespFirstNegativeTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) <
      tokenTargetCoordinate kind q t := by
  let c :=
    decodeOffset psi (tokenCode t)
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  have hb :
      1 - ((psi : Nat) : Int) ≤ c ∧
        c ≤ -1 := by
    rcases hv with hn | hp
    · exact hn
    · exfalso
      have hnegc : c < 0 := by
        simpa only [c] using hneg
      omega
  cases kind with
  | black =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist]
      simp only
        [Int.natCast_zero, Int.zero_add, Int.add_zero]
      change
        ((psi : Nat) : Int) <
          c % (((2 * psi : Nat)) : Int)
      have hperiod :
          c % (((2 * psi : Nat)) : Int) =
            (c + (((2 * psi : Nat)) : Int)) %
              (((2 * psi : Nat)) : Int) := by
        rw [Int.add_emod_right]
      rw [hperiod]
      rw [Int.emod_eq_of_lt
        (by omega) (by omega)]
      omega
  | white =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist]
      have hsum :
          ((psi : Nat) : Int) +
                c +
                ((psi : Nat) : Int) =
            c + (((2 * psi : Nat)) : Int) := by
        omega
      change
        ((psi : Nat) : Int) <
          (((psi : Nat) : Int) +
              c +
              ((psi : Nat) : Int)) %
            (((2 * psi : Nat)) : Int)
      rw [hsum]
      rw [Int.emod_eq_of_lt
        (by omega) (by omega)]
      omega


private theorem ooRespNegative_not_first
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hsound : GhostSound G)
    (hx :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    x.val ≠ 0 := by
  intro hx0
  have htok :=
    ooRespGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hvalid :=
    ooRespOwner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner
  unfold ValidToken at hvalid
  rw [htok] at hvalid
  dsimp only at hvalid
  rcases hvalid with hp | hn
  · omega
  · have hrow := (hCd x).1
    rw [← hx] at hrow
    have hdist :
        (G.phys (ring.rightNeighbor e)).dist.val =
          tokenD' psi kind := by
      cases kind with
      | black =>
          simp only [tokenD'] at hrow ⊢
          rw [hx0, Nat.zero_add] at hrow
          first
          | exact hrow.trans (Nat.zero_mod _)
          | simpa using hrow
          | omega
      | white =>
          simp only [tokenD'] at hrow ⊢
          rw [hx0, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega)] at hrow
          exact hrow
    have ht :=
      ooRespFirstNegativeTarget
        hpsi kind
        (G.phys (ring.rightNeighbor e))
        z.value hdist hneg
    omega


private theorem ooRespPredecessorData
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hsound : GhostSound G)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    ∃ x : Fin (2 * psi), ∃ y : Fin (2 * psi),
      ring.rightNeighbor e =
          shiftRight ring k x.val ∧
        e = shiftRight ring k y.val ∧
        y.val + 1 = x.val := by
  rcases hwin with ⟨x, hx⟩
  have hx0 :=
    ooRespNegative_not_first
      hpsi ring k kind G e x z
      hCd hsound hx howner hneg
  let y : Fin (2 * psi) :=
    ⟨x.val - 1, by omega⟩
  have hstep :
      ring.rightNeighbor
          (shiftRight ring k y.val) =
        shiftRight ring k x.val := by
    calc
      ring.rightNeighbor
            (shiftRight ring k y.val) =
          shiftRight ring k (y.val + 1) :=
        ooRespRightNeighborShiftRight
          ring k y.val
      _ = shiftRight ring k x.val := by
        congr 1
        dsimp [y]
        omega
  have hrn :
      ring.rightNeighbor e =
        ring.rightNeighbor
          (shiftRight ring k y.val) :=
    hx.trans hstep.symm
  have he :=
    congrArg ring.leftNeighbor hrn
  rw [ooRespLeftNeighborRightNeighbor,
    ooRespLeftNeighborRightNeighbor] at he
  exact
    ⟨x, y, hx, he,
      by dsimp [y]; omega⟩


private theorem ooRespCd_last_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C)
    (i : Fin n)
    (hwin : Lemma4InWindow ring k psi i) :
    (C i).last = false := by
  rcases hwin with ⟨x, hx⟩
  have h := (hCd x).2
  rw [← hx] at h
  exact h


private theorem ooRespCd_dist_same
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (hCd : Cd ring k kind C)
    (hCd' : Cd ring k kind C')
    (i : Fin n)
    (hwin : Lemma4InWindow ring k psi i) :
    (C' i).dist = (C i).dist := by
  rcases hwin with ⟨x, hx⟩
  have h0 := (hCd x).1
  have h1 := (hCd' x).1
  rw [← hx] at h0 h1
  apply Fin.ext
  exact h1.trans h0.symm


private theorem ooRespProgress_dist_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t : TokenData psi)
    (hdist : q'.dist = q.dist) :
    lemma4TokenProgress kind q' t =
      lemma4TokenProgress kind q t := by
  unfold lemma4TokenProgress lemma4TokenStage
  unfold tokenTargetCoordinate
  rw [hdist]


private theorem ooRespValid_same_dist
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (i : Fin n)
    (t : TokenData psi)
    (htok :
      tokenAt kind (C i) = some t)
    (htok' :
      tokenAt kind (C' i) = some t)
    (hdist :
      (C' i).dist = (C i).dist)
    (hvalid : ValidToken kind C i) :
    ValidToken kind C' i := by
  unfold ValidToken at hvalid ⊢
  rw [htok] at hvalid
  rw [htok']
  dsimp only at hvalid ⊢
  unfold tokenTargetCoordinate at hvalid ⊢
  rw [hdist]
  exact hvalid


private theorem ooRespFresh_advance
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (z z' : GhostToken n psi)
    (hmeta :
      z'.lmeta = ghostStepLineageAdvance z.lmeta) :
    FreshAt kind k z.lmeta →
      FreshAt kind k z'.lmeta := by
  intro hfresh
  rcases hfresh with ⟨t, hid, hsite⟩
  refine ⟨t, ?_, ?_⟩
  · rw [hmeta]
    simpa [ghostStepLineageAdvance] using hid
  · rw [hmeta]
    simpa [ghostStepLineageAdvance] using hsite


private theorem ooRespNegativeAbs
    {psi : Nat}
    {c : Int}
    (hvalid : ValidOffset psi c)
    (hc : c ≤ -2) :
    (c + 1).natAbs + 1 = c.natAbs ∧
      c.natAbs ≤ psi - 1 := by
  constructor
  · cases c with
    | ofNat m =>
        omega
    | negSucc m =>
        cases m with
        | zero =>
            omega
        | succ u =>
            rfl
  · rcases hvalid with hn | hp
    · cases c with
      | ofNat m =>
          have hmnonneg : (0 : Int) ≤ Int.ofNat m := by
            first
            | exact Int.ofNat_zero_le m
            | exact Int.natCast_nonneg m
            | omega
          exfalso
          omega
      | negSucc m =>
          simp at hn ⊢
          omega
    · omega


private theorem ooRespNegativeStep_target
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (t t' : TokenData psi)
    (hCd : Cd ring k kind C)
    (hCd' : Cd ring k kind C')
    (hxr :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hye :
      e = shiftRight ring k y.val)
    (hyx :
      y.val + 1 = x.val)
    (hc :
      decodeOffset psi (tokenCode t) ≤ -2)
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) + 1) :
    tokenTargetCoordinate kind (C' e) t' =
      tokenTargetCoordinate kind
        (C (ring.rightNeighbor e)) t := by
  have hpre := (hCd x).1
  have hpost := (hCd' y).1
  rw [← hxr] at hpre
  rw [← hye] at hpost
  cases kind with
  | black =>
      simp only [tokenD'] at hpre hpost
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt x.isLt] at hpre
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt y.isLt] at hpost
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hpre, hpost, hc']
      congr 1
      omega
  | white =>
      simp only [tokenD'] at hpre hpost
      by_cases hxlt : x.val < psi
      · have hylt : y.val + psi < 2 * psi := by
          omega
        have hxl :
            x.val + psi < 2 * psi := by
          omega
        rw [Nat.mod_eq_of_lt hxl] at hpre
        rw [Nat.mod_eq_of_lt hylt] at hpost
        unfold tokenTargetCoordinate
        simp only [tokenD']
        rw [hpre, hpost, hc']
        congr 1
        omega
      · by_cases hxeq : x.val = psi
        · have hyval :
              y.val = psi - 1 := by
            omega
          have hpreSum :
              x.val + psi = 2 * psi := by
            omega
          have hpostSum :
              y.val + psi = 2 * psi - 1 := by
            omega
          rw [hpreSum, Nat.mod_self] at hpre
          rw [hpostSum,
            Nat.mod_eq_of_lt (by omega)] at hpost
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpre, hpost, hc']
          have hsum :
              (((2 * psi - 1 : Nat) : Int) +
                    (decodeOffset psi
                        (tokenCode t) + 1) +
                    ((psi : Nat) : Int)) =
                ((0 : Int) +
                    decodeOffset psi (tokenCode t) +
                    ((psi : Nat) : Int)) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right]
          first
          | rfl
          | simp
        · have hxgt : psi < x.val := by
            omega
          have hpreGe :
              2 * psi ≤ x.val + psi := by
            omega
          have hpostGe :
              2 * psi ≤ y.val + psi := by
            omega
          have hpreLt :
              x.val + psi - 2 * psi <
                2 * psi := by
            omega
          have hpostLt :
              y.val + psi - 2 * psi <
                2 * psi := by
            omega
          rw [Nat.mod_eq_sub_mod hpreGe,
            Nat.mod_eq_of_lt hpreLt] at hpre
          rw [Nat.mod_eq_sub_mod hpostGe,
            Nat.mod_eq_of_lt hpostLt] at hpost
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpre, hpost, hc']
          congr 1
          omega


private theorem ooRespNegativeStep_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (i j : Fin n)
    (t t' : TokenData psi)
    (htok :
      tokenAt kind (C i) = some t)
    (htok' :
      tokenAt kind (C' j) = some t')
    (hvalid :
      ValidToken kind C i)
    (hc :
      decodeOffset psi (tokenCode t) ≤ -2)
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) + 1)
    (htarget :
      tokenTargetCoordinate kind (C' j) t' =
        tokenTargetCoordinate kind (C i) t) :
    ValidToken kind C' j := by
  unfold ValidToken at hvalid ⊢
  rw [htok] at hvalid
  rw [htok']
  dsimp only at hvalid ⊢
  rcases hvalid with hp | hn
  · omega
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [hc']
      omega
    · rw [htarget]
      exact hn.2.1
    · rw [htarget]
      exact hn.2.2


private theorem ooRespNegativeStep_progress
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) ≤ -2)
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) + 1)
    (htarget :
      tokenTargetCoordinate kind q' t' =
        tokenTargetCoordinate kind q t) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  let c :=
    decodeOffset psi (tokenCode t)
  have hpsi0 : 0 < psi := by
    have hcode := (tokenCode t).isLt
    omega
  have hv :=
    decodeOffset_valid
      psi hpsi0 (tokenCode t)
  have habs :=
    ooRespNegativeAbs
      hv (by simpa [c] using hc)
  have hnot :
      ¬ 0 < decodeOffset psi (tokenCode t) := by
    omega
  have hcnew :
      decodeOffset psi (tokenCode t') ≤ -1 := by
    rw [hc']
    omega
  have hnot' :
      ¬ 0 < decodeOffset psi (tokenCode t') := by
    omega
  unfold lemma4TokenProgress lemma4TokenStage
  simp only [hnot, hnot', if_false]
  rw [hc', htarget]
  generalize
    ((tokenTargetCoordinate kind q t).toNat +
        psi - 1 - psi) *
      (2 * psi - 1) = B
  omega


private theorem ooRespServiceEdge_negative
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    e =
      lemma4ServiceEdge
        ring kind G (ring.rightNeighbor e) z := by
  unfold lemma4ServiceEdge
  rw [if_neg (by omega)]
  exact
    (ooRespLeftNeighborRightNeighbor
      ring e).symm


/-! -----------------------------------------------------------------------
    Main reduction
------------------------------------------------------------------------ -/



/-! ## Restated same-ID rows (no kinematics premise, no completion escape) -/

private def OoInitPremises
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi) : Prop :=
  Cd ring k kind G.phys ∧
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ∧
    Lemma4GhostCoveredWindow ring k kind G ∧
    GhostSound G ∧
    GhostIdsUniqueAt step G ∧
    Lemma4InWindow ring k psi e ∧
    ghostTokenAt kind G e = some z ∧
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id))

private def OoInitConclusion
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi) : Prop :=
  ∃ j : Fin n, ∃ z' : GhostToken n psi,
    Lemma4InWindow ring k psi j ∧
      ((j = e ∧
          (ghostStepSelectedPair
              hpsi ring step G e kind).left =
            some z') ∨
        (j = ring.rightNeighbor e ∧
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some z')) ∧
      z'.lmeta.id = z.lmeta.id ∧
      (FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta) ∧
      ValidToken kind
        (ghostStep hpsi ring step G e).phys j ∧
      lemma4TokenProgress
          kind (G.phys e) z.value ≤
        lemma4TokenProgress
          kind
          ((ghostStep hpsi ring step G e).phys j)
          z'.value ∧
      (e = lemma4ServiceEdge ring kind G e z →
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys j)
            z'.value =
          lemma4TokenProgress
              kind (G.phys e) z.value +
            1)

private def OoInitArrivalRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    OoInitPremises
        hpsi ring k kind step G e z →
    decodeOffset psi (tokenCode z.value) = 1 →
    OoInitConclusion
      hpsi ring k kind step G e z

private def OoInitRightMoveRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    OoInitPremises
        hpsi ring k kind step G e z →
    2 ≤ decodeOffset psi (tokenCode z.value) →
    OoInitConclusion
      hpsi ring k kind step G e z

private def OoInitTurnCoreRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    OoInitPremises
        hpsi ring k kind step G e z →
    decodeOffset psi (tokenCode z.value) < 0 →
    ∃ j : Fin n, ∃ z' : GhostToken n psi,
      Lemma4InWindow ring k psi j ∧
        ((j = e ∧
            (ghostStepSelectedPair
                hpsi ring step G e kind).left =
              some z') ∨
          (j = ring.rightNeighbor e ∧
            (ghostStepSelectedPair
                hpsi ring step G e kind).right =
              some z')) ∧
        z'.lmeta.id = z.lmeta.id ∧
        (FreshAt kind k z.lmeta →
          FreshAt kind k z'.lmeta) ∧
        ValidToken kind
          (ghostStep hpsi ring step G e).phys j ∧
        lemma4TokenProgress
            kind (G.phys e) z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys j)
            z'.value

private def OoRespSameIdBranch : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) →
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z →
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id)) →
    ∃ j : Fin n, ∃ z' : GhostToken n psi,
      Lemma4InWindow ring k psi j ∧
        ((j = e ∧
            (ghostStepSelectedPair
                hpsi ring step G e kind).left =
              some z') ∨
          (j = ring.rightNeighbor e ∧
            (ghostStepSelectedPair
                hpsi ring step G e kind).right =
              some z')) ∧
        z'.lmeta.id = z.lmeta.id ∧
        (FreshAt kind k z.lmeta →
          FreshAt kind k z'.lmeta) ∧
        ValidToken kind
          (ghostStep hpsi ring step G e).phys j ∧
        lemma4TokenProgress
            kind
            (G.phys (ring.rightNeighbor e))
            z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys j)
            z'.value ∧
        (e =
            lemma4ServiceEdge
              ring kind G (ring.rightNeighbor e) z →
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1)


private theorem ooInitArrivalRow_proved :
    OoInitArrivalRow := by
  unfold OoInitArrivalRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hc

  rcases hp with
    ⟨hCd, hCd', _hcovered, hsound,
      huniq, hwin, howner, hsame⟩

  have hn2 :
      2 ≤ n :=
    ooArrCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    ooArrRightNeighbor_ne ring hn2 e

  have hNoRight :
      ∀ zr : GhostToken n psi,
        ghostTokenAt kind G
            (ring.rightNeighbor e) =
          some zr →
        zr.lmeta.id ≠ z.lmeta.id := by
    intro zr hr hid
    have heq :=
      huniq.1 kind e (ring.rightNeighbor e)
        z zr howner hr hid.symm
    exact hne heq.symm

  have hNotBirth :
      z.lmeta.id ≠ .born kind step := by
    intro hid
    have hs :=
      huniq.2 kind e z kind step howner hid
    omega

  have hpre :=
    ooArrGhostSoundAt
      G kind e z hsound howner

  rcases hwin with ⟨x, hx⟩

  have hnext :
      x.val + 1 < 2 * psi := by
    by_cases hlt : x.val + 1 < 2 * psi
    · exact hlt
    · have hxlast :
          x.val = 2 * psi - 1 := by
        have hxlt := x.isLt
        omega
      have hrow := hCd x
      dsimp only at hrow
      have hdistLast :
          (G.phys e).dist.val =
            (2 * psi - 1 +
                tokenD' psi kind) %
              (2 * psi) := by
        calc
          (G.phys e).dist.val =
              (x.val + tokenD' psi kind) %
                (2 * psi) := by
            rw [hx]
            exact hrow.1
          _ =
              (2 * psi - 1 +
                  tokenD' psi kind) %
                (2 * psi) := by
            rw [hxlast]
      exact
        False.elim
          (ooArrPositiveNotLast
            hpsi kind (G.phys e) z.value
            hdistLast hpre.2 (by omega))

  let y : Fin (2 * psi) :=
    ⟨x.val + 1, hnext⟩

  have hr :
      ring.rightNeighbor e =
        shiftRight ring k y.val := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor
            (shiftRight ring k x.val) :=
        congrArg ring.rightNeighbor hx
      _ = shiftRight ring k (x.val + 1) :=
        ooArrRightNeighbor_shiftRight
          ring k x.val
      _ = shiftRight ring k y.val := by
        rfl

  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hr⟩

  let p :=
    ooArrSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  let s :=
    ooArrSelectedOutput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hmoveDL :
      s.1.dist = p.1.dist ∧
        s.1.last = p.1.last ∧
        s.2.dist = p.2.dist ∧
        s.2.last = p.2.last := by
    simpa [s, p, ooArrSelectedOutput]
      using
        ooArrMoveTokenDistLast
          hpsi kind p.1 p.2

  have hstepDL :=
    ooArrStepDistLast
      hpsi ring step G e kind hne
  have hstepTok :=
    ooArrStepTokenPair
      hpsi ring step G e kind hne

  have hpostLastE :
      ((ghostStep hpsi ring step G e).phys e).last =
        false := by
    have h := (hCd' x).2
    rw [← hx] at h
    exact h

  have hpostLastR :
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).last =
        false := by
    have h := (hCd' y).2
    rw [← hr] at h
    exact h

  have hgate :
      p.1.last = false ∧ p.2.last = false := by
    constructor
    · have hsLast : s.1.last = false :=
        hstepDL.2.1.symm.trans hpostLastE
      exact hmoveDL.2.1.symm.trans hsLast
    · have hsLast : s.2.last = false :=
        hstepDL.2.2.2.symm.trans hpostLastR
      exact hmoveDL.2.2.2.symm.trans hsLast

  have hsameLocal :
      ((∃ zL : GhostToken n psi,
          (ooArrGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (ooArrGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id)) := by
    have hs := hsame
    rw [← ooArrSelectedPair_eq_export
      hpsi ring step G e kind] at hs
    simpa
      [ooArrSelectedPair, p, howner]
      using hs

  have hclass :=
    ooArrClass
      hpsi kind step e p.1 p.2
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z hgate hNoRight hNotBirth hc

  rcases hsameLocal with hleft | hright
  · rcases hleft with ⟨zL, hL, hidL⟩
    exact False.elim ((hclass zL).1 hL hidL)
  · rcases hright with ⟨z', hR, hid⟩
    rcases (hclass z').2 hR hid with
      ⟨hmeta, hvalue, hlocal, htokMove⟩

    have hRSelected :
        (ooArrSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      simpa
        [ooArrSelectedPair, p, howner]
        using hR

    have hRExport :
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      rw [← ooArrSelectedPair_eq_export
        hpsi ring step G e kind]
      exact hRSelected

    have _hpostOwner :
        ghostTokenAt kind
            (ghostStep hpsi ring step G e)
            (ring.rightNeighbor e) =
          some z' := by
      rw [ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e kind hne]
      exact hRExport

    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
          some z'.value := by
      have hs :
          tokenAt kind s.2 = some z'.value := by
        simpa [s, p, ooArrSelectedOutput]
          using htokMove
      exact hstepTok.2.trans hs

    have hdestDist :
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
          p.2.dist := by
      exact
        hstepDL.2.2.1.trans hmoveDL.2.2.1

    have hvalidPost :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) :=
      ooArrValidToken_of_local
        kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        p.2 z'.value
        htokPost hdestDist hlocal

    have hdecode :
        decodeOffset psi (tokenCode z'.value) =
          1 - ((psi : Nat) : Int) := by
      rw [hvalue]
      unfold ooArrBounceNext
      dsimp [ooArrMkToken, tokenCode]
      exact decodeOffset_negPsiPlusOne psi hpsi

    have hpreDist :
        (G.phys e).dist.val =
          (x.val + tokenD' psi kind) %
            (2 * psi) := by
      have h := (hCd x).1
      simpa [hx] using h

    have hpostDist :
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val =
          (x.val + 1 + tokenD' psi kind) %
            (2 * psi) := by
      have h := (hCd' y).1
      rw [← hr] at h
      simpa [y] using h

    have holdTarget :
        tokenTargetCoordinate kind
            (G.phys e) z.value =
          (((x.val + 1 : Nat)) : Int) :=
      ooArrOldTarget
        hpsi kind (G.phys e) z.value
        x.val x.isLt hnext hpreDist hc

    have hlowTarget :
        ((psi : Nat) : Int) ≤
          tokenTargetCoordinate kind
            (G.phys e) z.value := by
      have hlocalPre := hpre.2
      unfold ooArrLocalValid at hlocalPre
      dsimp only at hlocalPre
      rw [hc] at hlocalPre
      rcases hlocalPre with hp | hn
      · exact hp.2.1
      · omega

    have hlow :
        psi ≤ x.val + 1 := by
      rw [holdTarget] at hlowTarget
      exact_mod_cast hlowTarget

    have hnewTarget :
        tokenTargetCoordinate kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z'.value =
          (((x.val + 2 - psi : Nat)) : Int) :=
      ooArrBounceTarget
        hpsi kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z'.value x.val hnext hlow
        hpostDist hdecode

    have hstage :
        lemma4TokenStage kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z'.value =
          lemma4TokenStage kind
              (G.phys e) z.value :=
      ooArrStage_eq
        hpsi kind
        (G.phys e)
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value z'.value x.val hlow
        hc hdecode holdTarget hnewTarget

    have hprogress :
        lemma4TokenProgress kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z'.value =
          lemma4TokenProgress kind
              (G.phys e) z.value + 1 :=
      ooArrProgress_eq
        hpsi kind
        (G.phys e)
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value z'.value
        hc hdecode hstage

    have hfresh :
        FreshAt kind k z.lmeta →
          FreshAt kind k z'.lmeta := by
      intro hf
      rw [hmeta]
      exact
        ooArrFresh_advance
          (psi := psi) kind k z.lmeta hf

    unfold OoInitConclusion
    exact
      ⟨ring.rightNeighbor e, z',
          hwinR,
          Or.inr ⟨rfl, hRExport⟩,
          hid,
          hfresh,
          hvalidPost,
          by omega,
          fun _hservice => hprogress⟩

private theorem ooInitRightMoveRow_proved :
    OoInitRightMoveRow := by
  unfold OoInitRightMoveRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hc

  rcases hp with
    ⟨hCd, hCd', _hcovered, hsound,
      huniq, hwin, howner, hsame⟩

  have hn2 :
      2 ≤ n :=
    ooIRowsCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    ooIRowsRightNeighbor_ne ring hn2 e

  have hNoRight :
      ∀ zr : GhostToken n psi,
        ghostTokenAt kind G
            (ring.rightNeighbor e) =
          some zr →
        zr.lmeta.id ≠ z.lmeta.id := by
    intro zr hr hid
    have heq :=
      huniq.1 kind e (ring.rightNeighbor e)
        z zr howner hr hid.symm
    exact hne heq.symm

  have hNotBirth :
      z.lmeta.id ≠ .born kind step := by
    intro hid
    have hs :=
      huniq.2 kind e z kind step howner hid
    omega

  have hpre :=
    ooIRowsGhostSoundAt
      G kind e z hsound howner

  rcases hwin with ⟨x, hx⟩

  have hnext :
      x.val + 1 < 2 * psi := by
    by_cases hlt : x.val + 1 < 2 * psi
    · exact hlt
    · have hxlast :
          x.val = 2 * psi - 1 := by
        have hxlt := x.isLt
        omega
      have hrow := hCd x
      dsimp only at hrow
      have hdistLast :
          (G.phys e).dist.val =
            (2 * psi - 1 +
                tokenD' psi kind) %
              (2 * psi) := by
        calc
          (G.phys e).dist.val =
              (x.val + tokenD' psi kind) %
                (2 * psi) := by
            rw [hx]
            exact hrow.1
          _ =
              (2 * psi - 1 +
                  tokenD' psi kind) %
                (2 * psi) := by
            rw [hxlast]
      exact
        False.elim
          (ooIRowsPositiveNotLast
            hpsi kind (G.phys e) z.value
            hdistLast hpre.2 (by omega))

  let y : Fin (2 * psi) :=
    ⟨x.val + 1, hnext⟩

  have hr :
      ring.rightNeighbor e =
        shiftRight ring k y.val := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor
            (shiftRight ring k x.val) :=
        congrArg ring.rightNeighbor hx
      _ = shiftRight ring k (x.val + 1) :=
        ooIRowsRightNeighbor_shiftRight
          ring k x.val
      _ = shiftRight ring k y.val := by
        rfl

  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hr⟩

  let p :=
    ooIRowsSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  let s :=
    ooIRowsSelectedOutput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hmoveDL :
      s.1.dist = p.1.dist ∧
        s.1.last = p.1.last ∧
        s.2.dist = p.2.dist ∧
        s.2.last = p.2.last := by
    simpa [s, p, ooIRowsSelectedOutput]
      using
        ooIRowsMoveTokenDistLast
          hpsi kind p.1 p.2

  have hstepDL :=
    ooIRowsStepDistLast
      hpsi ring step G e kind hne
  have hstepTok :=
    ooIRowsStepTokenPair
      hpsi ring step G e kind hne

  have hpostLastE :
      ((ghostStep hpsi ring step G e).phys e).last =
        false := by
    have h := (hCd' x).2
    try dsimp only at h
    rw [← hx] at h
    exact h

  have hpostLastR :
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).last =
        false := by
    have h := (hCd' y).2
    try dsimp only at h
    rw [← hr] at h
    exact h

  have hgate :
      p.1.last = false ∧ p.2.last = false := by
    constructor
    · have hsLast : s.1.last = false :=
        hstepDL.2.1.symm.trans hpostLastE
      exact hmoveDL.2.1.symm.trans hsLast
    · have hsLast : s.2.last = false :=
        hstepDL.2.2.2.symm.trans hpostLastR
      exact hmoveDL.2.2.2.symm.trans hsLast

  have hsameLocal :
      ((∃ zL : GhostToken n psi,
          (ooIRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (ooIRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id)) := by
    have hs := hsame
    rw [← ooIRowsSelectedPair_eq_export
      hpsi ring step G e kind] at hs
    simpa
      [ooIRowsSelectedPair, p, howner]
      using hs

  have hclass :=
    ooIRowsRightMoveClass
      hpsi kind step e p.1 p.2
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z hgate hNoRight hNotBirth hc

  rcases hsameLocal with hleft | hright
  · rcases hleft with ⟨zL, hL, hidL⟩
    exact False.elim ((hclass zL).1 hL hidL)
  · rcases hright with ⟨z', hR, hid⟩
    rcases (hclass z').2 hR hid with
      ⟨hmeta, hvalue, hlocal, htokMove⟩

    have hRSelected :
        (ooIRowsSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      simpa
        [ooIRowsSelectedPair, p, howner]
        using hR

    have hRExport :
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      rw [← ooIRowsSelectedPair_eq_export
        hpsi ring step G e kind]
      exact hRSelected

    have _hpostOwner :
        ghostTokenAt kind
            (ghostStep hpsi ring step G e)
            (ring.rightNeighbor e) =
          some z' := by
      rw [ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e kind hne]
      exact hRExport

    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
          some z'.value := by
      have hs :
          tokenAt kind s.2 = some z'.value := by
        simpa [s, p, ooIRowsSelectedOutput]
          using htokMove
      exact hstepTok.2.trans hs

    have hdestDist :
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
          p.2.dist := by
      exact
        hstepDL.2.2.1.trans hmoveDL.2.2.1

    have hvalidPost :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) :=
      ooIRowsValidToken_of_local
        kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        p.2 z'.value
        htokPost hdestDist hlocal

    have hdecode :
        decodeOffset psi (tokenCode z'.value) =
          decodeOffset psi (tokenCode z.value) - 1 := by
      rw [hvalue]
      unfold ooIRowsRightNext
      dsimp [ooIRowsMkToken, tokenCode]
      exact decode_encode _ _ _

    have hpreDist :
        (G.phys e).dist.val =
          (x.val + tokenD' psi kind) %
            (2 * psi) := by
      have h := (hCd x).1
      try dsimp only at h
      simpa [hx] using h

    have hpostDist :
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val =
          (x.val + 1 + tokenD' psi kind) %
            (2 * psi) := by
      have h := (hCd' y).1
      try dsimp only at h
      rw [← hr] at h
      simpa [y] using h

    have hsucc :
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val =
          ((G.phys e).dist.val + 1) %
            (2 * psi) :=
      ooIRowsCanonicalSucc
        hpsi x.val (tokenD' psi kind)
        (G.phys e).dist.val
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val
        hpreDist hpostDist

    have htarget :=
      ooIRowsRightMoveTarget
        hpsi kind
        (G.phys e)
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value z'.value
        hsucc hc hdecode

    have hprogress :
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z'.value =
          lemma4TokenProgress
              kind (G.phys e) z.value + 1 :=
      ooIRowsRightMoveProgress
        kind
        (G.phys e)
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value z'.value
        hc hdecode htarget

    have hfresh :
        FreshAt kind k z.lmeta →
          FreshAt kind k z'.lmeta := by
      intro hf
      rw [hmeta]
      exact
        ooIRowsFresh_advance
          (psi := psi) kind k z.lmeta hf

    unfold OoInitConclusion
    exact
      ⟨ring.rightNeighbor e, z',
          hwinR,
          Or.inr ⟨rfl, hRExport⟩,
          hid,
          hfresh,
          hvalidPost,
          by omega,
          fun _hservice => hprogress⟩


private theorem ooInitTurnCoreRow_proved :
    OoInitTurnCoreRow := by
  unfold OoInitTurnCoreRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hneg

  rcases hp with
    ⟨hCd, hCd', _hcovered, hsound,
      huniq, hwin, howner, hsame⟩

  have hn2 :
      2 ≤ n :=
    ooIRowsCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    ooIRowsRightNeighbor_ne ring hn2 e

  have hNoRight :
      ∀ zr : GhostToken n psi,
        ghostTokenAt kind G
            (ring.rightNeighbor e) =
          some zr →
        zr.lmeta.id ≠ z.lmeta.id := by
    intro zr hr hid
    have heq :=
      huniq.1 kind e (ring.rightNeighbor e)
        z zr howner hr hid.symm
    exact hne heq.symm

  have hNotBirth :
      z.lmeta.id ≠ .born kind step := by
    intro hid
    have hs :=
      huniq.2 kind e z kind step howner hid
    omega

  let p :=
    ooIRowsSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hsameLocal :
      ((∃ zL : GhostToken n psi,
          (ooIRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (ooIRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id)) := by
    have hs := hsame
    rw [← ooIRowsSelectedPair_eq_export
      hpsi ring step G e kind] at hs
    simpa
      [ooIRowsSelectedPair, p, howner]
      using hs

  have hclass :=
    ooIRowsTurnClass
      hpsi kind step e p.1 p.2
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z hNoRight hNotBirth hneg

  rcases hsameLocal with hleft | hright
  · rcases hleft with ⟨z', hL, hid⟩
    rcases (hclass z').1 hL hid with
      ⟨hzz, htokMove⟩
    subst z'

    have hLSelected :
        (ooIRowsSelectedPair
          hpsi ring step G e kind).left =
          some z := by
      simpa
        [ooIRowsSelectedPair, p, howner]
        using hL

    have hLExport :
        (ghostStepSelectedPair
          hpsi ring step G e kind).left =
          some z := by
      rw [← ooIRowsSelectedPair_eq_export
        hpsi ring step G e kind]
      exact hLSelected

    have _hpostOwner :
        ghostTokenAt kind
            (ghostStep hpsi ring step G e) e =
          some z := by
      rw [ghostTokenAt_ghostStep_initiator
        hpsi ring step G e kind]
      exact hLExport

    have hstepTok :=
      ooIRowsStepTokenPair
        hpsi ring step G e kind hne

    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys e) =
          some z.value := by
      have hs :
          tokenAt kind
              (ooIRowsSelectedOutput
                hpsi kind
                (G.phys e)
                (G.phys (ring.rightNeighbor e))).1 =
            some z.value := by
        simpa
          [ooIRowsSelectedOutput, p]
          using htokMove
      exact hstepTok.1.trans hs

    have hpre :=
      ooIRowsGhostSoundAt
        G kind e z hsound howner

    rcases hwin with ⟨x, hx⟩
    have h0 := (hCd x).1
    have h1 := (hCd' x).1
    try dsimp only at h0 h1
    have hpreDist :
        (G.phys e).dist.val =
          (x.val + tokenD' psi kind) %
            (2 * psi) := by
      simpa [hx] using h0
    have hpostDist :
        ((ghostStep hpsi ring step G e).phys e).dist.val =
          (x.val + tokenD' psi kind) %
            (2 * psi) := by
      simpa [hx] using h1
    have hdist :
        ((ghostStep hpsi ring step G e).phys e).dist =
          (G.phys e).dist := by
      apply Fin.ext
      exact hpostDist.trans hpreDist.symm

    have hvalidPre :
        ValidToken kind G.phys e := by
      unfold ValidToken
      rw [hpre.1]
      exact hpre.2

    have hvalidPost :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys e :=
      ooIRowsValidToken_transfer
        kind G.phys
        (ghostStep hpsi ring step G e).phys
        e z.value
        hpre.1 htokPost hdist hvalidPre

    have hprogress :
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys e)
            z.value =
          lemma4TokenProgress
              kind (G.phys e) z.value := by
      unfold lemma4TokenProgress lemma4TokenStage
      unfold tokenTargetCoordinate
      rw [hdist]

    exact
      ⟨e, z, ⟨x, hx⟩,
          Or.inl ⟨rfl, hLExport⟩,
          rfl,
          (fun hf => hf),
          hvalidPost,
          by omega⟩

  · rcases hright with ⟨zR, hR, hidR⟩
    exact False.elim ((hclass zR).2 hR hidR)


private theorem ooRespSameIdBranch_of_negTurnRow
    (hturn : Lemma4SweepResponderNegTurnProgressRowStmt) :
    OoRespSameIdBranch := by
  unfold OoRespSameIdBranch
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' _hcovered hsound huniq
  intro hwin howner hsame


  have hfit :
      2 * psi ≤ n :=
    ooRespCd_fit
      hpsi ring k kind G.phys hCd
  have hn2 : 2 ≤ n := by
    omega
  have hne :
      ring.rightNeighbor e ≠ e :=
    ooRespRightNeighbor_ne ring hn2 e


  let p :=
    ooRespSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))


  have hpair :
      ooRespSelectedPair
          hpsi ring step G e kind =
        ghostStepSelectedPair
          hpsi ring step G e kind :=
    ooRespSelectedPair_eq_export
      hpsi ring step G e kind


  have htokStep :=
    ooRespGhostStepTokenPairAt
      hpsi ring step G e kind hne


  have hlastStep :=
    ooRespGhostStepLastPair
      hpsi ring step G e kind hne


  have hNoLeft :
      ∀ zl : GhostToken n psi,
        ghostTokenAt kind G e = some zl →
        zl.lmeta.id ≠ z.lmeta.id := by
    intro zl hl hid
    have heq :=
      huniq.1
        kind e (ring.rightNeighbor e)
        zl z hl howner hid
    exact hne heq.symm


  have hNotFresh :
      z.lmeta.id ≠ .born kind step := by
    intro hz
    have hs :=
      huniq.2
        kind (ring.rightNeighbor e) z
        kind step howner hz
    exact (Nat.lt_irrefl step) hs


  have htok0 :
      tokenAt kind
          (G.phys (ring.rightNeighbor e)) =
        some z.value :=
    ooRespGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner


  have hvalid0 :
      ValidToken kind G.phys
        (ring.rightNeighbor e) :=
    ooRespOwner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner


  rcases hsame with hleft | hright
  · rcases hleft with ⟨zL, hL, hidL⟩
    have hLmirror :
        (ooRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (some z)).left =
        some zL := by
      have hL' :
          (ooRespSelectedPair
            hpsi ring step G e kind).left =
          some zL := by
        rw [hpair]
        exact hL
      change
        (ooRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).left =
          some zL at hL'
      rw [howner] at hL'
      exact hL'


    have hshape :=
      ooRespLeftSameId
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        z zL hNoLeft hNotFresh
        hLmirror hidL


    have htokSelected :=
      (ooRespGhostMove_valueSound
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        (some z)).1 zL hLmirror


    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys e) =
          some zL.value := by
      exact htokStep.1.trans htokSelected


    rcases hshape with ⟨hmeta, hturnClass | hord⟩
    · have hrow :=
        hturn
          hpsi ring k kind step G e z zL
          hCd hCd' hsound hwin howner
          hL hidL hmeta
          hturnClass.1 htokPost hturnClass.2
      rcases hrow with
        ⟨hwinE, hfresh, hvalid,
          hmono, hservice⟩
      exact
        ⟨e, zL, hwinE,
            Or.inl ⟨rfl, hL⟩,
            hidL, hfresh, hvalid,
            hmono, hservice⟩


    · rcases hord with ⟨hc, hc'⟩
      have hneg :
          decodeOffset psi (tokenCode z.value) < 0 := by
        omega
      rcases
        ooRespPredecessorData
          hpsi ring k kind G e z
          hCd hsound hwin howner hneg
        with ⟨x, y, hxr, hye, hyx⟩


      have hwinE :
          Lemma4InWindow ring k psi e :=
        ⟨y, hye⟩


      have htarget :=
        ooRespNegativeStep_target
          hpsi ring k kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          e x y z.value zL.value
          hCd hCd'
          hxr hye hyx hc hc'


      have hvalid :
          ValidToken kind
            (ghostStep hpsi ring step G e).phys e :=
        ooRespNegativeStep_valid
          kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) e
          z.value zL.value
          htok0 htokPost hvalid0 hc hc' htarget


      have hprog :
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              zL.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1 :=
        ooRespNegativeStep_progress
          kind
          (G.phys (ring.rightNeighbor e))
          ((ghostStep hpsi ring step G e).phys e)
          z.value zL.value hc hc' htarget


      have hfresh :
          FreshAt kind k z.lmeta →
            FreshAt kind k zL.lmeta :=
        ooRespFresh_advance
          kind k z zL hmeta


      have hmono :
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value ≤
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              zL.value := by
        rw [hprog]
        omega


      exact
        ⟨e, zL, hwinE,
            Or.inl ⟨rfl, hL⟩,
            hidL, hfresh, hvalid,
            hmono,
            fun _ => hprog⟩


  · rcases hright with ⟨zR, hR, hidR⟩
    have hRmirror :
        (ooRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (some z)).right =
        some zR := by
      have hR' :
          (ooRespSelectedPair
            hpsi ring step G e kind).right =
          some zR := by
        rw [hpair]
        exact hR
      change
        (ooRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).right =
          some zR at hR'
      rw [howner] at hR'
      exact hR'


    have hzz :
        zR = z :=
      ooRespRightSameId
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        z zR hNoLeft hNotFresh
        hRmirror hidR
    subst zR


    have htokSelected :=
      (ooRespGhostMove_valueSound
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        (some z)).2 z hRmirror


    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
          some z.value := by
      exact htokStep.2.trans htokSelected


    have hdist :
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          (G.phys (ring.rightNeighbor e)).dist :=
      ooRespCd_dist_same
        ring k kind
        G.phys
        (ghostStep hpsi ring step G e).phys
        hCd hCd'
        (ring.rightNeighbor e) hwin


    have hvalid :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) :=
      ooRespValid_same_dist
        kind
        G.phys
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        z.value htok0 htokPost hdist hvalid0


    have hprogEq :
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z.value =
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value :=
      ooRespProgress_dist_eq
        kind
        (G.phys (ring.rightNeighbor e))
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value hdist


    have hservice :
        e =
            lemma4ServiceEdge
              ring kind G (ring.rightNeighbor e) z →
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys
                (ring.rightNeighbor e))
              z.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1 := by
      intro hs
      by_cases hpos :
          0 < decodeOffset psi (tokenCode z.value)
      · unfold lemma4ServiceEdge at hs
        rw [if_pos hpos] at hs
        exact False.elim (hne hs.symm)
      · have hv :=
          decodeOffset_valid
            psi (by omega) (tokenCode z.value)
        have hneg :
            decodeOffset psi (tokenCode z.value) < 0 := by
          rcases hv with hn | hp
          · omega
          · omega


        have hwinE :
            Lemma4InWindow ring k psi e := by
          rcases
            ooRespPredecessorData
              hpsi ring k kind G e z
              hCd hsound hwin howner hneg
            with ⟨_x, y, _hxr, hye, _hyx⟩
          exact ⟨y, hye⟩


        have hlastE :
            ((ghostStep hpsi ring step G e).phys e).last =
              false :=
          ooRespCd_last_false
            ring k kind
            (ghostStep hpsi ring step G e).phys
            hCd' e hwinE
        have hlastR :
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)).last =
              false :=
          ooRespCd_last_false
            ring k kind
            (ghostStep hpsi ring step G e).phys
            hCd' (ring.rightNeighbor e) hwin


        have hpLast :
            p.1.last = false ∧ p.2.last = false := by
          constructor
          · rw [← hlastStep.1]
            exact hlastE
          · rw [← hlastStep.2]
            exact hlastR


        have hpositive :=
          ooRespRightSameId_positive_of_gate
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            z z
            hNoLeft hNotFresh
            hpLast hRmirror rfl
        exact False.elim (hpos hpositive)


    have hmono :
        lemma4TokenProgress
            kind
            (G.phys (ring.rightNeighbor e))
            z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z.value := by
      exact Nat.le_of_eq hprogEq.symm


    exact
      ⟨ring.rightNeighbor e, z,
          hwin,
          Or.inr ⟨rfl, hR⟩,
          rfl,
          (fun hfresh => hfresh),
          hvalid, hmono, hservice⟩


private theorem ooRespSameIdBranch_proved :
    OoRespSameIdBranch :=
  ooRespSameIdBranch_of_negTurnRow
    lemma4SweepResponderNegTurnProgressRow_proved

/-! ## The two interacted old-owner rows -/

/--
Initiator old owner.  If a selected-pair output carries the tracked lineage,
the restated same-ID rows (c = 1, c ≥ 2, c < 0) give the survivor; otherwise
the lineage is deleted.
-/
theorem lemma4SweepOldOwnerInitiatorRow_proved :
    Lemma4SweepOldOwnerInitiatorRow := by
  unfold Lemma4SweepOldOwnerInitiatorRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' hcovered hsound huniq
  intro hwin howner _hnonfresh

  have hn2 :
      2 ≤ n :=
    ooIRowsCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    ooIRowsRightNeighbor_ne ring hn2 e

  unfold Lemma4SweepOldOwnerOutcome
  rcases Classical.em
      ((∃ zL : GhostToken n psi,
          (ghostStepSelectedPair
              hpsi ring step G e kind).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id))
    with hsame | hsame
  · have hp :
        OoInitPremises
          hpsi ring k kind step G e z :=
      ⟨hCd, hCd', hcovered, hsound,
        huniq, hwin, howner, hsame⟩
    have hconc :
        OoInitConclusion
          hpsi ring k kind step G e z := by
      rcases
        lemma4SweepInitiatorOffsetCases
          hpsi z.value
        with h1 | hge | hneg
      · exact
          ooInitArrivalRow_proved
            hpsi ring k kind step G e z hp h1
      · exact
          ooInitRightMoveRow_proved
            hpsi ring k kind step G e z hp hge
      · have hnot :
            e ≠ lemma4ServiceEdge ring kind G e z :=
          lemma4SweepInitiatorNegative_not_service
            hpsi ring k kind G e z hCd hneg
        rcases
          ooInitTurnCoreRow_proved
            hpsi ring k kind step G e z hp hneg
          with
            ⟨j, z', hwinJ, hsite, hid,
              hfresh, hvalid, hprog⟩
        exact
          ⟨j, z', hwinJ, hsite, hid,
            hfresh, hvalid, hprog,
            fun hs => False.elim (hnot hs)⟩
    unfold OoInitConclusion at hconc
    rcases hconc with
      ⟨j, z', hwinJ, hsite, hid,
        _hfresh, hvalid, hprog, hserv⟩
    have hpost :
        ghostTokenAt kind
            (ghostStep hpsi ring step G e) j =
          some z' := by
      rcases hsite with ⟨hj, hL⟩ | ⟨hj, hR⟩
      · rw [hj,
          ghostTokenAt_ghostStep_initiator
            hpsi ring step G e kind]
        exact hL
      · rw [hj,
          ghostTokenAt_ghostStep_responder_of_ne
            hpsi ring step G e kind hne]
        exact hR
    exact
      Or.inr
        ⟨j, z', hwinJ, hpost, hid,
          hvalid, hprog, hserv⟩
  · refine Or.inl ?_
    intro j z' hj hid
    by_cases hje : j = e
    · rw [hje,
        ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind] at hj
      exact hsame (Or.inl ⟨z', hj, hid⟩)
    · by_cases hjr : j = ring.rightNeighbor e
      · rw [hjr,
          ghostTokenAt_ghostStep_responder_of_ne
            hpsi ring step G e kind hne] at hj
        exact hsame (Or.inr ⟨z', hj, hid⟩)
      · rw [ghostTokenAt_ghostStep_frame
          hpsi ring step G e j kind hje hjr] at hj
        have heq :=
          huniq.1 kind e j z z' howner hj hid.symm
        exact hje heq.symm

/--
Responder old owner.  Same split: a same-ID survivor comes from the restated
responder same-ID branch; otherwise the lineage is deleted.
-/
theorem lemma4SweepOldOwnerResponderRow_proved :
    Lemma4SweepOldOwnerResponderRow := by
  unfold Lemma4SweepOldOwnerResponderRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' hcovered hsound huniq
  intro hwin howner _hnonfresh

  have hn2 :
      2 ≤ n :=
    ooIRowsCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    ooIRowsRightNeighbor_ne ring hn2 e

  unfold Lemma4SweepOldOwnerOutcome
  rcases Classical.em
      ((∃ zL : GhostToken n psi,
          (ghostStepSelectedPair
              hpsi ring step G e kind).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id))
    with hsame | hsame
  · rcases
      ooRespSameIdBranch_proved
        hpsi ring k kind step G e z
        hCd hCd' hcovered hsound huniq
        hwin howner hsame
      with
        ⟨j, z', hwinJ, hsite, hid,
          _hfresh, hvalid, hprog, hserv⟩
    have hpost :
        ghostTokenAt kind
            (ghostStep hpsi ring step G e) j =
          some z' := by
      rcases hsite with ⟨hj, hL⟩ | ⟨hj, hR⟩
      · rw [hj,
          ghostTokenAt_ghostStep_initiator
            hpsi ring step G e kind]
        exact hL
      · rw [hj,
          ghostTokenAt_ghostStep_responder_of_ne
            hpsi ring step G e kind hne]
        exact hR
    exact
      Or.inr
        ⟨j, z', hwinJ, hpost, hid,
          hvalid, hprog, hserv⟩
  · refine Or.inl ?_
    intro j z' hj hid
    by_cases hje : j = e
    · rw [hje,
        ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind] at hj
      exact hsame (Or.inl ⟨z', hj, hid⟩)
    · by_cases hjr : j = ring.rightNeighbor e
      · rw [hjr,
          ghostTokenAt_ghostStep_responder_of_ne
            hpsi ring step G e kind hne] at hj
        exact hsame (Or.inr ⟨z', hj, hid⟩)
      · rw [ghostTokenAt_ghostStep_frame
          hpsi ring step G e j kind hje hjr] at hj
        have heq :=
          huniq.1 kind (ring.rightNeighbor e) j
            z z' howner hj hid.symm
        exact hjr heq.symm

/-- The unmasked old-owner progress step, all three owner-role rows closed. -/
theorem lemma4SweepOldOwnerProgressStep_proved :
    Lemma4SweepOldOwnerProgressStep :=
  lemma4SweepOldOwnerProgressStep_of_interacted_rows
    lemma4SweepOldOwnerInitiatorRow_proved
    lemma4SweepOldOwnerResponderRow_proved

end PPL

#print axioms PPL.lemma4SweepOldOwnerInitiatorRow_proved
#print axioms PPL.lemma4SweepOldOwnerResponderRow_proved
#print axioms PPL.lemma4SweepOldOwnerProgressStep_proved
