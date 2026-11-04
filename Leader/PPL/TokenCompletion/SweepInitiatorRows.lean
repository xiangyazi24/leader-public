import Leader.PPL.TokenCompletion.SweepInitiatorSameId
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Public-name mirrors for the selected colour -/

private def initiatorRowsBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def initiatorRowsMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def initiatorRowsLocalValid
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

private instance instDecidableInitiatorRowsLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (initiatorRowsLocalValid kind q t) := by
  unfold initiatorRowsLocalValid
  infer_instance

private def initiatorRowsSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def initiatorRowsClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if initiatorRowsLocalValid kind q t then
        q
      else
        initiatorRowsSetToken kind q none

private def initiatorRowsLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private theorem initiatorRowsSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      initiatorRowsSetToken kind q t := by
  cases kind <;> rfl

private theorem initiatorRowsSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      initiatorRowsClearInvalid kind q := by
  cases kind <;> rfl

private theorem initiatorRowsSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = initiatorRowsLeaderBirth q := by
  rfl

private def initiatorRowsNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    initiatorRowsMkToken
      (offsetPsiCode psi hpsi)
      (initiatorRowsBitToFin (!sourceBit))
      (initiatorRowsBitToFin sourceBit)
  else
    initiatorRowsMkToken
      (offsetPsiCode psi hpsi)
      (initiatorRowsBitToFin sourceBit)
      (0 : Fin 2)

private def initiatorRowsMoveToken
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
            (initiatorRowsMkToken
              (offsetPsiCode psi hpsi)
              (initiatorRowsBitToFin (!l.id))
              (initiatorRowsBitToFin l.id)))
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
                initiatorRowsNegTurnNext hpsi l.id t
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
                    (initiatorRowsMkToken
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
                (initiatorRowsMkToken
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
                (initiatorRowsMkToken
                  nextOffset t.1.2 t.2)))
        else
          moveLeft l r
  else
    (l, r)

private theorem initiatorRowsMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    initiatorRowsMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl

private def initiatorRowsLiveShadow
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
              initiatorRowsLocalValid kind q t then
            some z
          else
            none

private def initiatorRowsLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if initiatorRowsLocalValid kind q t then
        some t
      else
        none

private def initiatorRowsBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      initiatorRowsMkToken
        (offsetPsiCode psi hpsi)
        (initiatorRowsBitToFin (!idBit))
        (initiatorRowsBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def initiatorRowsBumpTo
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
        if initiatorRowsLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def initiatorRowsGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := initiatorRowsLiveValue kind l
  let rv0 := initiatorRowsLiveValue kind r
  let gl0 := initiatorRowsLiveShadow kind l gl
  let gr0 := initiatorRowsLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (initiatorRowsBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (initiatorRowsBirthGhost
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
            initiatorRowsMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            initiatorRowsBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            initiatorRowsMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            initiatorRowsBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some tr =>
              let cr := decodeOffset psi (tokenCode tr)
              if hm1 : cr = -1 then
                let next :=
                  initiatorRowsNegTurnNext hpsi l.id tr
                let b :=
                  initiatorRowsBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : cr ≤ -2 then
                have hc : ValidOffset psi cr :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode tr)
                let next :=
                  initiatorRowsMkToken
                    (encodeOffset psi (cr + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    tr.1.2 tr.2
                let b :=
                  initiatorRowsBumpTo kind l next gr0
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
                initiatorRowsNegTurnNext hpsi l.id tr
              let b :=
                initiatorRowsBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                initiatorRowsMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                initiatorRowsBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def initiatorRowsPrelude
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

private def initiatorRowsSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := initiatorRowsPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2

private def initiatorRowsSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := initiatorRowsSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2

private def initiatorRowsSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    initiatorRowsSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  initiatorRowsGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem initiatorRowsSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    initiatorRowsSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

/-! ## Physical suffix frames -/

private theorem initiatorRowsMoveTokenDistLast
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

private theorem initiatorRowsElimTokenPair
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

private theorem initiatorRowsElimDistLast
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

private theorem initiatorRowsWhitePreservesBlack
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

private theorem initiatorRowsPplSelectedTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind
          (initiatorRowsSelectedOutput
            hpsi kind l r).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind
          (initiatorRowsSelectedOutput
            hpsi kind l r).2 := by
  cases kind with
  | black =>
      let p := initiatorRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        initiatorRowsWhitePreservesBlack
          hpsi b.1 b.2
      have he :=
        initiatorRowsElimTokenPair .black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          initiatorRowsSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact ⟨he.1.trans hw.1, he.2.trans hw.2⟩
  | white =>
      let p := initiatorRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        initiatorRowsElimTokenPair .white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          initiatorRowsSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem initiatorRowsPplSelectedDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (ppl hpsi l r).1.dist =
        (initiatorRowsSelectedOutput
          hpsi kind l r).1.dist ∧
      (ppl hpsi l r).1.last =
        (initiatorRowsSelectedOutput
          hpsi kind l r).1.last ∧
      (ppl hpsi l r).2.dist =
        (initiatorRowsSelectedOutput
          hpsi kind l r).2.dist ∧
      (ppl hpsi l r).2.last =
        (initiatorRowsSelectedOutput
          hpsi kind l r).2.last := by
  cases kind with
  | black =>
      let p := initiatorRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        initiatorRowsMoveTokenDistLast
          hpsi .white b.1 b.2
      have he :=
        initiatorRowsElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          initiatorRowsSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact
        ⟨he.1.trans hw.1,
          he.2.1.trans hw.2.1,
          he.2.2.1.trans hw.2.2.1,
          he.2.2.2.trans hw.2.2.2⟩
  | white =>
      let p := initiatorRowsPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        initiatorRowsElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          initiatorRowsSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem initiatorRowsStepTokenPair
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
        (initiatorRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 ∧
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)) =
      tokenAt kind
        (initiatorRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
  have hp :=
    initiatorRowsPplSelectedTokenPair
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

private theorem initiatorRowsStepDistLast
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ((ghostStep hpsi ring step G e).phys e).dist =
        (initiatorRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.dist ∧
      ((ghostStep hpsi ring step G e).phys e).last =
        (initiatorRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.last ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        (initiatorRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.dist ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).last =
        (initiatorRowsSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.last := by
  have hp :=
    initiatorRowsPplSelectedDistLast
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

private theorem initiatorRowsCd_two_le_n
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

private theorem initiatorRowsRightNeighbor_ne
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

private theorem initiatorRowsRightNeighbor_shiftRight
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

private theorem initiatorRowsGhostSoundAt
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧
      initiatorRowsLocalValid
        kind (G.phys i) z.value := by
  cases kind with
  | black =>
      exact hsound.1 i z howner
  | white =>
      exact hsound.2 i z howner

private theorem initiatorRowsLastDistPlusD
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

private theorem initiatorRowsLastPositiveTargetBelow
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
    initiatorRowsLastDistPlusD
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

private theorem initiatorRowsPositiveNotLast
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
      initiatorRowsLocalValid kind q t)
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    False := by
  have ht :=
    initiatorRowsLastPositiveTargetBelow
      hpsi kind q t hdist hpos
  unfold initiatorRowsLocalValid at hlocal
  dsimp only at hlocal
  rcases hlocal with hp | hn <;> omega

private theorem initiatorRowsCanonicalSucc
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

private theorem initiatorRowsRightMoveTarget
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

private theorem initiatorRowsRightMoveProgress
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

private theorem initiatorRowsValidToken_of_local
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
      initiatorRowsLocalValid kind q t) :
    ValidToken kind C i := by
  unfold ValidToken
  rw [htok]
  unfold initiatorRowsLocalValid at hlocal
  unfold tokenTargetCoordinate at hlocal ⊢
  rw [hdist]
  exact hlocal

private theorem initiatorRowsValidToken_transfer
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

private theorem initiatorRowsFresh_advance
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

private def initiatorRowsRightNext
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
  initiatorRowsMkToken
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
signs.  In every branch the physical `initiatorRowsMoveToken` and the ghost
`initiatorRowsGhostMoveToken` take the same branch; the lemmas in this block
normalise the token projections, the cleared fields, and the shadow/bump
constructors so that one fixed `simp only` set decides every branch. -/

private theorem irTokenAt_sourceSet
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q x) = x := by
  rw [initiatorRowsSourceSet_eq]
  cases kind <;> rfl

private theorem irTokenAt_sourceClear
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      initiatorRowsLiveValue kind q := by
  rw [initiatorRowsSourceClear_eq]
  unfold initiatorRowsClearInvalid
  unfold initiatorRowsLiveValue
  cases htok : tokenAt kind q with
  | none =>
      exact htok
  | some t =>
      show tokenAt kind
          (if initiatorRowsLocalValid kind q t then q
            else initiatorRowsSetToken kind q none) =
        (if initiatorRowsLocalValid kind q t then some t else none)
      by_cases hv : initiatorRowsLocalValid kind q t
      · rw [if_pos hv, if_pos hv]
        exact htok
      · rw [if_neg hv, if_neg hv]
        cases kind <;> rfl

/-- Clearing an invalid selected token changes only that token field. -/
private theorem irSourceClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    And ((sourceClear kind q).last = q.last)
      (And ((sourceClear kind q).id = q.id)
        ((sourceClear kind q).dist = q.dist)) := by
  have key :
      Or (initiatorRowsClearInvalid kind q = q)
        (initiatorRowsClearInvalid kind q =
          initiatorRowsSetToken kind q none) := by
    unfold initiatorRowsClearInvalid
    cases tokenAt kind q with
    | none => exact Or.inl rfl
    | some t =>
        by_cases hv : initiatorRowsLocalValid kind q t
        · exact Or.inl (if_pos hv)
        · exact Or.inr (if_neg hv)
  rw [initiatorRowsSourceClear_eq]
  rcases key with h | h <;> rw [h]
  · exact ⟨rfl, rfl, rfl⟩
  · cases kind <;> exact ⟨rfl, rfl, rfl⟩

private theorem irSourceClear_last
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).last = q.last :=
  (irSourceClear_fields kind q).1

private theorem irSourceClear_id
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).id = q.id :=
  (irSourceClear_fields kind q).2.1

private theorem irSourceClear_dist
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).dist = q.dist :=
  (irSourceClear_fields kind q).2.2

private theorem irSourceSet_id
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (x : Option (TokenData psi)) :
    (sourceSet kind q x).id = q.id := by
  rw [initiatorRowsSourceSet_eq]
  cases kind <;> rfl

private theorem irTokenCode_mk
    {psi : Nat} (o : Fin (2 * psi - 1)) (b c : Fin 2) :
    tokenCode (initiatorRowsMkToken o b c) = o := rfl

private theorem irBirthGhost_value
    {n psi : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    (initiatorRowsBirthGhost hpsi kind step site idBit :
        GhostToken n psi).value =
      initiatorRowsMkToken
        (offsetPsiCode psi hpsi)
        (initiatorRowsBitToFin (!idBit))
        (initiatorRowsBitToFin idBit) := rfl

/-- A shadow is empty whenever the physical live value is empty. -/
private theorem irShadow_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hnone : initiatorRowsLiveValue kind q = none) :
    initiatorRowsLiveShadow kind q g = none := by
  unfold initiatorRowsLiveValue at hnone
  cases g with
  | none =>
      rfl
  | some u =>
      unfold initiatorRowsLiveShadow
      cases ht : tokenAt kind q with
      | none =>
          rfl
      | some t =>
          rw [ht] at hnone
          by_cases hv : initiatorRowsLocalValid kind q t
          · have hbad :
                (some t : Option (TokenData psi)) = none := by
              simpa only [if_pos hv] using hnone
            cases hbad
          · show (if u.value = t ∧ initiatorRowsLocalValid kind q t
                then some u else none) = none
            rw [if_neg (fun h => hv h.2)]

/-- A live shadow is the incoming ghost and carries the live value. -/
private theorem irShadow_some
    {n psi kappa : Nat}
    {kind : TokenKind}
    {q : State psi kappa}
    {g : Option (GhostToken n psi)}
    {w : GhostToken n psi}
    (h : initiatorRowsLiveShadow kind q g = some w) :
    g = some w ∧
      initiatorRowsLiveValue kind q = some w.value := by
  cases g with
  | none =>
      cases h
  | some z =>
      unfold initiatorRowsLiveShadow at h
      unfold initiatorRowsLiveValue
      cases ht : tokenAt kind q with
      | none =>
          rw [ht] at h
          cases h
      | some t =>
          rw [ht] at h
          change (if z.value = t ∧ initiatorRowsLocalValid kind q t
              then some z else none) = some w at h
          by_cases hc : z.value = t ∧ initiatorRowsLocalValid kind q t
          · rw [if_pos hc] at h
            have hzw : z = w := Option.some.inj h
            subst hzw
            refine ⟨rfl, ?_⟩
            change (if initiatorRowsLocalValid kind q t
                then some t else none) = some z.value
            rw [if_pos hc.2, hc.1]
          · rw [if_neg hc] at h
            cases h

private theorem irBump_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (next : TokenData psi) :
    (initiatorRowsBumpTo kind q next
        (none : Option (GhostToken n psi))).live = none := rfl

/-- A live bump output is the advanced incoming owner at the new value, and
the new value is locally valid at the destination. -/
private theorem irBump_some
    {n psi kappa : Nat}
    {kind : TokenKind}
    {q : State psi kappa}
    {next : TokenData psi}
    {g : Option (GhostToken n psi)}
    {z' : GhostToken n psi}
    (h : (initiatorRowsBumpTo kind q next g).live = some z') :
    ∃ w : GhostToken n psi,
      g = some w ∧
        z'.value = next ∧
          z'.lmeta = ghostStepLineageAdvance w.lmeta ∧
            initiatorRowsLocalValid kind q next := by
  cases g with
  | none =>
      cases h
  | some w =>
      change (if initiatorRowsLocalValid kind q next then
          some ({ value := next
                  lmeta := ghostStepLineageAdvance w.lmeta } :
            GhostToken n psi)
        else none) = some z' at h
      by_cases hv : initiatorRowsLocalValid kind q next
      · rw [if_pos hv] at h
        cases h
        exact ⟨w, rfl, rfl, rfl, hv⟩
      · rw [if_neg hv] at h
        cases h

/-! ## Finite same-ID branch helpers (explicit case tree) -/

private theorem initiatorRowsGhostMove_valueSound_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      (initiatorRowsGhostMoveToken
          hpsi kind step site l r gl gr).left =
        some z') :
    tokenAt kind
        (moveToken hpsi kind l r).1 =
      some z'.value := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  rw [← initiatorRowsMoveToken_eq hpsi kind l r]
  unfold initiatorRowsMoveToken
  unfold initiatorRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [irTokenAt_sourceSet, irTokenAt_sourceClear,
                irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                irShadow_none, irBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost ⊢
      all_goals
        first
        | exact (irShadow_some hpost).2
        | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost ⊢
        all_goals
          first
          | exact (irShadow_some hpost).2
          | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
    | false =>
        cases hAv : initiatorRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (irShadow_some hpost).2
                    | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (irShadow_some hpost).2
                    | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
        | some a =>
          cases hBv : initiatorRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost ⊢
              all_goals
                first
                | exact (irShadow_some hpost).2
                | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost ⊢
              all_goals
                first
                | exact (irShadow_some hpost).2
                | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])


private theorem initiatorRowsGhostMove_valueSound_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      (initiatorRowsGhostMoveToken
          hpsi kind step site l r gl gr).right =
        some z') :
    tokenAt kind
        (moveToken hpsi kind l r).2 =
      some z'.value := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  rw [← initiatorRowsMoveToken_eq hpsi kind l r]
  unfold initiatorRowsMoveToken
  unfold initiatorRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [irTokenAt_sourceSet, irTokenAt_sourceClear,
                irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                irShadow_none, irBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost ⊢
      all_goals
        first
        | exact (irShadow_some hpost).2
        | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost ⊢
        all_goals
          first
          | exact (irShadow_some hpost).2
          | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
    | false =>
        cases hAv : initiatorRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (irShadow_some hpost).2
                    | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost ⊢
                  all_goals
                    first
                    | exact (irShadow_some hpost).2
                    | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost ⊢
                    all_goals
                      first
                      | exact (irShadow_some hpost).2
                      | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
        | some a =>
          cases hBv : initiatorRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost ⊢
              all_goals
                first
                | exact (irShadow_some hpost).2
                | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost ⊢
              all_goals
                first
                | exact (irShadow_some hpost).2
                | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost ⊢
                all_goals
                  first
                  | exact (irShadow_some hpost).2
                  | (have h := (irShadow_some hpost).2; simp only [hAv, hBv, Option.some.injEq] at h; first | exact h | exact h.symm)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; first | exact hv.symm | exact hv)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; rw [hv]; congr 1; congr 1; simp only [irTokenCode_mk, decodeOffset_psi])


private theorem initiatorRowsRightMoveGhost_left_false
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold initiatorRowsGhostMoveToken at hpost
  obtain ⟨hl1, hr1⟩ := hgate
  cases hAv : initiatorRowsLiveValue kind l with
  | none =>
    by_cases hd : l.dist.val = tokenD' psi kind
    · cases hBv : initiatorRowsLiveValue kind r with
      | none =>
          simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [irTokenAt_sourceSet, irTokenAt_sourceClear,
                      irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                      irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                      irShadow_none, irBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    · cases hBv : initiatorRowsLiveValue kind r with
      | none =>
          simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [irTokenAt_sourceSet, irTokenAt_sourceClear,
                      irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                      irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                      irShadow_none, irBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
  | some a =>
    cases hBv : initiatorRowsLiveValue kind r with
    | none =>
      by_cases h1 : decodeOffset psi (tokenCode a) = 1
      · simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, h1] at hpost
        all_goals
          first
          | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    | some b =>
      by_cases hm1 : decodeOffset psi (tokenCode b) = -1
      · simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, hm1] at hpost
        all_goals
          first
          | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
      · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨hg, h⟩ := irShadow_some hpost; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)


private theorem initiatorRowsRightMoveGhost_right
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z'.lmeta =
        ghostStepLineageAdvance z.lmeta ∧
      z'.value =
        initiatorRowsRightNext hpsi z.value hc ∧
      initiatorRowsLocalValid kind r z'.value := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold initiatorRowsGhostMoveToken at hpost
  obtain ⟨hl1, hr1⟩ := hgate
  cases hAv : initiatorRowsLiveValue kind l with
  | none =>
    by_cases hd : l.dist.val = tokenD' psi kind
    · cases hBv : initiatorRowsLiveValue kind r with
      | none =>
          simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [irTokenAt_sourceSet, irTokenAt_sourceClear,
                      irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                      irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                      irShadow_none, irBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
    · cases hBv : initiatorRowsLiveValue kind r with
      | none =>
          simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hd] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
      | some b =>
          by_cases hm1 : decodeOffset psi (tokenCode b) = -1
          · simp only
              [irTokenAt_sourceSet, irTokenAt_sourceClear,
                      irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                      irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                      irShadow_none, irBump_none,
                      decodeOffset_psi, hpsi1, hpsi2,
                      ne_eq, not_true_eq_false, not_false_eq_true,
                      and_true, true_and, and_false, false_and, and_self,
                      eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                      ↓reduceIte, ↓reduceDIte,
               hl1, hr1, hAv, hBv, hd, hm1] at hpost
            all_goals
              first
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
              | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
          · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
              all_goals
                first
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
  | some a =>
    cases hBv : initiatorRowsLiveValue kind r with
    | none =>
      by_cases h1 : decodeOffset psi (tokenCode a) = 1
      · simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, h1] at hpost
        all_goals
          first
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
      · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, h1, h2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
    | some b =>
      by_cases hm1 : decodeOffset psi (tokenCode b) = -1
      · simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1, hAv, hBv, hm1] at hpost
        all_goals
          first
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
      · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
        · simp only
            [irTokenAt_sourceSet, irTokenAt_sourceClear,
                    irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                    irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                    irShadow_none, irBump_none,
                    decodeOffset_psi, hpsi1, hpsi2,
                    ne_eq, not_true_eq_false, not_false_eq_true,
                    and_true, true_and, and_false, false_and, and_self,
                    eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                    ↓reduceIte, ↓reduceDIte,
             hl1, hr1, hAv, hBv, hm1, hm2] at hpost
          all_goals
            first
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; exact ⟨hm, hv, hv ▸ hval⟩)
            | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | exact absurd hid (hNoRight z' (irShadow_some hpost).1)


private theorem initiatorRowsTurnGhost_left
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z' = z := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold initiatorRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [irTokenAt_sourceSet, irTokenAt_sourceClear,
                irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                irShadow_none, irBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost
      all_goals
        first
        | exact (Option.some.inj (irShadow_some hpost).1).symm
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost
        all_goals
          first
          | exact (Option.some.inj (irShadow_some hpost).1).symm
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    | false =>
        cases hAv : initiatorRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (irShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact (Option.some.inj (irShadow_some hpost).1).symm
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (irShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (irShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (irShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact (Option.some.inj (irShadow_some hpost).1).symm
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (irShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact (Option.some.inj (irShadow_some hpost).1).symm
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        | some a =>
          cases hBv : initiatorRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost
              all_goals
                first
                | exact (Option.some.inj (irShadow_some hpost).1).symm
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (irShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (irShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost
              all_goals
                first
                | exact (Option.some.inj (irShadow_some hpost).1).symm
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (irShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact (Option.some.inj (irShadow_some hpost).1).symm
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hgr, _⟩ := irShadow_some hw; have hwid : z'.lmeta.id = (ghostStepLineageAdvance w.lmeta).id := congrArg LineageMeta.id hm; have hwid2 : (ghostStepLineageAdvance w.lmeta).id = w.lmeta.id := rfl; exact absurd (hwid2.symm.trans (hwid.symm.trans hid)) (hNoRight w hgr))
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)


private theorem initiatorRowsTurnGhost_right_false
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  have hpost := hout
  clear hout
  unfold initiatorRowsGhostMoveToken at hpost
  cases hl1 : l.last with
  | true =>
      simp only
        [irTokenAt_sourceSet, irTokenAt_sourceClear,
                irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                irShadow_none, irBump_none,
                decodeOffset_psi, hpsi1, hpsi2,
                ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, true_and, and_false, false_and, and_self,
                eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                ↓reduceIte, ↓reduceDIte,
         hl1] at hpost
      all_goals
        first
        | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
        | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [irTokenAt_sourceSet, irTokenAt_sourceClear,
                  irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                  irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                  irShadow_none, irBump_none,
                  decodeOffset_psi, hpsi1, hpsi2,
                  ne_eq, not_true_eq_false, not_false_eq_true,
                  and_true, true_and, and_false, false_and, and_self,
                  eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                  ↓reduceIte, ↓reduceDIte,
           hl1, hr1] at hpost
        all_goals
          first
          | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
          | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
    | false =>
        cases hAv : initiatorRowsLiveValue kind l with
        | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          · cases hBv : initiatorRowsLiveValue kind r with
            | none =>
                simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hd] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [irTokenAt_sourceSet, irTokenAt_sourceClear,
                            irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                            irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                            irShadow_none, irBump_none,
                            decodeOffset_psi, hpsi1, hpsi2,
                            ne_eq, not_true_eq_false, not_false_eq_true,
                            and_true, true_and, and_false, false_and, and_self,
                            eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                            ↓reduceIte, ↓reduceDIte,
                     hl1, hr1, hAv, hBv, hd, hm1] at hpost
                  all_goals
                    first
                    | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                    | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
                  · simp only
                      [irTokenAt_sourceSet, irTokenAt_sourceClear,
                              irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                              irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                              irShadow_none, irBump_none,
                              decodeOffset_psi, hpsi1, hpsi2,
                              ne_eq, not_true_eq_false, not_false_eq_true,
                              and_true, true_and, and_false, false_and, and_self,
                              eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                              ↓reduceIte, ↓reduceDIte,
                       hl1, hr1, hAv, hBv, hd, hm1, hm2] at hpost
                    all_goals
                      first
                      | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                      | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
        | some a =>
          cases hBv : initiatorRowsLiveValue kind r with
          | none =>
            by_cases h1 : decodeOffset psi (tokenCode a) = 1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, h1] at hpost
              all_goals
                first
                | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, h1, h2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
          | some b =>
            by_cases hm1 : decodeOffset psi (tokenCode b) = -1
            · simp only
                [irTokenAt_sourceSet, irTokenAt_sourceClear,
                        irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                        irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                        irShadow_none, irBump_none,
                        decodeOffset_psi, hpsi1, hpsi2,
                        ne_eq, not_true_eq_false, not_false_eq_true,
                        and_true, true_and, and_false, false_and, and_self,
                        eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                        ↓reduceIte, ↓reduceDIte,
                 hl1, hr1, hAv, hBv, hm1] at hpost
              all_goals
                first
                | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
            · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)
              · simp only
                  [irTokenAt_sourceSet, irTokenAt_sourceClear,
                          irSourceClear_last, irSourceClear_id, irSourceClear_dist,
                          irSourceSet_id, irTokenCode_mk, irBirthGhost_value,
                          irShadow_none, irBump_none,
                          decodeOffset_psi, hpsi1, hpsi2,
                          ne_eq, not_true_eq_false, not_false_eq_true,
                          and_true, true_and, and_false, false_and, and_self,
                          eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                          ↓reduceIte, ↓reduceDIte,
                   hl1, hr1, hAv, hBv, hm1, hm2] at hpost
                all_goals
                  first
                  | exact absurd hid (hNoRight z' (irShadow_some hpost).1)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; obtain ⟨hg, h⟩ := irShadow_some hw; simp only [hAv, Option.some.injEq] at h hg; subst hg; subst h; omega)
                  | (obtain ⟨w, hw, hv, hm, hval⟩ := irBump_some hpost; simp only [Option.some.injEq] at hw; subst hw; have hwid : z'.lmeta.id = LineageId.born kind step := congrArg LineageMeta.id hm; exact absurd (hid.symm.trans hwid) hNotBirth)



private theorem initiatorRowsRightMoveClass_left
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  exact
    initiatorRowsRightMoveGhost_left_false
      hpsi kind step site l r gr z z'
      hgate hNoRight hNotBirth hc hout hid

private theorem initiatorRowsRightMoveClass_right
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z'.lmeta =
        ghostStepLineageAdvance z.lmeta ∧
      z'.value =
        initiatorRowsRightNext hpsi z.value hc ∧
      initiatorRowsLocalValid kind r z'.value ∧
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some z'.value := by
  have hg :=
    initiatorRowsRightMoveGhost_right
      hpsi kind step site l r gr z z'
      hgate hNoRight hNotBirth hc hout hid
  have hv :=
    initiatorRowsGhostMove_valueSound_right
      hpsi kind step site l r (some z) gr z' hout
  exact ⟨hg.1, hg.2.1, hg.2.2, hv⟩

private theorem initiatorRowsTurnClass_left
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z' = z ∧
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        some z.value := by
  have hz :=
    initiatorRowsTurnGhost_left
      hpsi kind step site l r gr z z'
      hNoRight hNotBirth hneg hout hid
  have hv :=
    initiatorRowsGhostMove_valueSound_left
      hpsi kind step site l r (some z) gr z' hout
  subst z'
  exact ⟨rfl, hv⟩

private theorem initiatorRowsTurnClass_right
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
      (initiatorRowsGhostMoveToken
          hpsi kind step site
          l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  exact
    initiatorRowsTurnGhost_right_false
      hpsi kind step site l r gr z z'
      hNoRight hNotBirth hneg hout hid

private theorem initiatorRowsRightMoveClass
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
      ((initiatorRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).left =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        False) ∧
      ((initiatorRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).right =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        z'.lmeta =
            ghostStepLineageAdvance z.lmeta ∧
          z'.value =
            initiatorRowsRightNext hpsi z.value hc ∧
          initiatorRowsLocalValid kind r z'.value ∧
          tokenAt kind
              (moveToken hpsi kind l r).2 =
            some z'.value) := by
  intro z'
  exact
    ⟨initiatorRowsRightMoveClass_left
        hpsi kind step site l r gr z
        hgate hNoRight hNotBirth hc z',
      initiatorRowsRightMoveClass_right
        hpsi kind step site l r gr z
        hgate hNoRight hNotBirth hc z'⟩

private theorem initiatorRowsTurnClass
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
      ((initiatorRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).left =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        z' = z ∧
          tokenAt kind
              (moveToken hpsi kind l r).1 =
            some z.value) ∧
      ((initiatorRowsGhostMoveToken
            hpsi kind step site
            l r (some z) gr).right =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        False) := by
  intro z'
  exact
    ⟨initiatorRowsTurnClass_left
        hpsi kind step site l r gr z
        hNoRight hNotBirth hneg z',
      initiatorRowsTurnClass_right
        hpsi kind step site l r gr z
        hNoRight hNotBirth hneg z'⟩

/-! ## Closed c >= 2 row -/

theorem lemma4SweepInitiatorRightMoveRow_proved :
    Lemma4SweepInitiatorRightMoveRow := by
  unfold Lemma4SweepInitiatorRightMoveRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hc

  rcases hp with
    ⟨hCd, hCd', _hcovered, hsound,
      huniq, _hkin, hwin, howner, hsame⟩

  have hn2 :
      2 ≤ n :=
    initiatorRowsCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    initiatorRowsRightNeighbor_ne ring hn2 e

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
    initiatorRowsGhostSoundAt
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
          (initiatorRowsPositiveNotLast
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
        initiatorRowsRightNeighbor_shiftRight
          ring k x.val
      _ = shiftRight ring k y.val := by
        rfl

  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hr⟩

  let p :=
    initiatorRowsSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  let s :=
    initiatorRowsSelectedOutput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hmoveDL :
      s.1.dist = p.1.dist ∧
        s.1.last = p.1.last ∧
        s.2.dist = p.2.dist ∧
        s.2.last = p.2.last := by
    simpa [s, p, initiatorRowsSelectedOutput]
      using
        initiatorRowsMoveTokenDistLast
          hpsi kind p.1 p.2

  have hstepDL :=
    initiatorRowsStepDistLast
      hpsi ring step G e kind hne
  have hstepTok :=
    initiatorRowsStepTokenPair
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
          (initiatorRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (initiatorRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id)) := by
    have hs := hsame
    rw [← initiatorRowsSelectedPair_eq_export
      hpsi ring step G e kind] at hs
    simpa
      [initiatorRowsSelectedPair, p, howner]
      using hs

  have hclass :=
    initiatorRowsRightMoveClass
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
        (initiatorRowsSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      simpa
        [initiatorRowsSelectedPair, p, howner]
        using hR

    have hRExport :
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      rw [← initiatorRowsSelectedPair_eq_export
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
        simpa [s, p, initiatorRowsSelectedOutput]
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
      initiatorRowsValidToken_of_local
        kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        p.2 z'.value
        htokPost hdestDist hlocal

    have hdecode :
        decodeOffset psi (tokenCode z'.value) =
          decodeOffset psi (tokenCode z.value) - 1 := by
      rw [hvalue]
      unfold initiatorRowsRightNext
      dsimp [initiatorRowsMkToken, tokenCode]
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
      initiatorRowsCanonicalSucc
        hpsi x.val (tokenD' psi kind)
        (G.phys e).dist.val
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val
        hpreDist hpostDist

    have htarget :=
      initiatorRowsRightMoveTarget
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
      initiatorRowsRightMoveProgress
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
        initiatorRowsFresh_advance
          (psi := psi) kind k z.lmeta hf

    unfold Lemma4SweepInitiatorSameIdConclusion
    exact
      Or.inr
        ⟨ring.rightNeighbor e, z',
          hwinR,
          Or.inr ⟨rfl, hRExport⟩,
          hid,
          hfresh,
          hvalidPost,
          by omega,
          fun _hservice => hprogress⟩

/-! ## Closed c < 0 turn/stay core -/

theorem lemma4SweepInitiatorTurnCoreRow_proved :
    Lemma4SweepInitiatorTurnCoreRow := by
  unfold Lemma4SweepInitiatorTurnCoreRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hneg

  rcases hp with
    ⟨hCd, hCd', _hcovered, hsound,
      huniq, _hkin, hwin, howner, hsame⟩

  have hn2 :
      2 ≤ n :=
    initiatorRowsCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    initiatorRowsRightNeighbor_ne ring hn2 e

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
    initiatorRowsSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hsameLocal :
      ((∃ zL : GhostToken n psi,
          (initiatorRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (initiatorRowsGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id)) := by
    have hs := hsame
    rw [← initiatorRowsSelectedPair_eq_export
      hpsi ring step G e kind] at hs
    simpa
      [initiatorRowsSelectedPair, p, howner]
      using hs

  have hclass :=
    initiatorRowsTurnClass
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
        (initiatorRowsSelectedPair
          hpsi ring step G e kind).left =
          some z := by
      simpa
        [initiatorRowsSelectedPair, p, howner]
        using hL

    have hLExport :
        (ghostStepSelectedPair
          hpsi ring step G e kind).left =
          some z := by
      rw [← initiatorRowsSelectedPair_eq_export
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
      initiatorRowsStepTokenPair
        hpsi ring step G e kind hne

    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys e) =
          some z.value := by
      have hs :
          tokenAt kind
              (initiatorRowsSelectedOutput
                hpsi kind
                (G.phys e)
                (G.phys (ring.rightNeighbor e))).1 =
            some z.value := by
        simpa
          [initiatorRowsSelectedOutput, p]
          using htokMove
      exact hstepTok.1.trans hs

    have hpre :=
      initiatorRowsGhostSoundAt
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
      initiatorRowsValidToken_transfer
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
      Or.inr
        ⟨e, z, ⟨x, hx⟩,
          Or.inl ⟨rfl, hLExport⟩,
          rfl,
          (fun hf => hf),
          hvalidPost,
          by omega⟩

  · rcases hright with ⟨zR, hR, hidR⟩
    exact False.elim ((hclass zR).2 hR hidR)

/-!
The c = 1 row remains the sole bounded-round residual.

Truth audit:
* same-ID survival rules out collision deletion and the invalid terminal
  bounce;
* the survivor is the responder bump with lineage metadata advanced once;
* its new decoded offset is 1 - psi;
* pre/post C_d give the adjacent canonical dist values;
* the missing arithmetic identity is that the new negative stage equals the
  old positive stage, so lemma4TokenProgress rises by exactly one.

No second residual is introduced here.
-/

theorem lemma4SweepInitiatorSameIdBranch_of_arrivalRow
    (hArrival : Lemma4SweepInitiatorArrivalRow) :
    Lemma4SweepInitiatorSameIdBranch := by
  exact
    lemma4SweepInitiatorSameIdBranch_of_positiveRows_and_turnCore
      hArrival
      lemma4SweepInitiatorRightMoveRow_proved
      lemma4SweepInitiatorTurnCoreRow_proved

end PPL

#print axioms PPL.lemma4SweepInitiatorRightMoveRow_proved
#print axioms PPL.lemma4SweepInitiatorTurnCoreRow_proved
#print axioms PPL.lemma4SweepInitiatorSameIdBranch_of_arrivalRow
