import Leader.PPL.TokenCompletion.SweepInitiatorSameId
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Public-name mirrors for the selected colour -/

private def arrivalBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def arrivalMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def arrivalLocalValid
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

private instance instDecidableArrivalLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (arrivalLocalValid kind q t) := by
  unfold arrivalLocalValid
  infer_instance

private def arrivalSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def arrivalClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if arrivalLocalValid kind q t then
        q
      else
        arrivalSetToken kind q none

private def arrivalLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private theorem arrivalSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      arrivalSetToken kind q t := by
  cases kind <;> rfl

private theorem arrivalSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      arrivalClearInvalid kind q := by
  cases kind <;> rfl

private theorem arrivalSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = arrivalLeaderBirth q := by
  rfl

private def arrivalNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    arrivalMkToken
      (offsetPsiCode psi hpsi)
      (arrivalBitToFin (!sourceBit))
      (arrivalBitToFin sourceBit)
  else
    arrivalMkToken
      (offsetPsiCode psi hpsi)
      (arrivalBitToFin sourceBit)
      (0 : Fin 2)

private def arrivalMoveToken
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
            (arrivalMkToken
              (offsetPsiCode psi hpsi)
              (arrivalBitToFin (!l.id))
              (arrivalBitToFin l.id)))
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
                arrivalNegTurnNext hpsi l.id t
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
                    (arrivalMkToken
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
                (arrivalMkToken
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
                (arrivalMkToken
                  nextOffset t.1.2 t.2)))
        else
          moveLeft l r
  else
    (l, r)

private theorem arrivalMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    arrivalMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl

private def arrivalLiveShadow
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
              arrivalLocalValid kind q t then
            some z
          else
            none

private def arrivalLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if arrivalLocalValid kind q t then
        some t
      else
        none

private def arrivalBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      arrivalMkToken
        (offsetPsiCode psi hpsi)
        (arrivalBitToFin (!idBit))
        (arrivalBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def arrivalBumpTo
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
        if arrivalLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def arrivalGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := arrivalLiveValue kind l
  let rv0 := arrivalLiveValue kind r
  let gl0 := arrivalLiveShadow kind l gl
  let gr0 := arrivalLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (arrivalBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (arrivalBirthGhost
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
            arrivalMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            arrivalBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            arrivalMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            arrivalBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some tr =>
              let cr := decodeOffset psi (tokenCode tr)
              if hm1 : cr = -1 then
                let next :=
                  arrivalNegTurnNext hpsi l.id tr
                let b :=
                  arrivalBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : cr ≤ -2 then
                have hc : ValidOffset psi cr :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode tr)
                let next :=
                  arrivalMkToken
                    (encodeOffset psi (cr + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    tr.1.2 tr.2
                let b :=
                  arrivalBumpTo kind l next gr0
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
                arrivalNegTurnNext hpsi l.id tr
              let b :=
                arrivalBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                arrivalMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                arrivalBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def arrivalPrelude
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

private def arrivalSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := arrivalPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2

private def arrivalSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := arrivalSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2

private def arrivalSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    arrivalSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  arrivalGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem arrivalSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    arrivalSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

/-! ## Physical suffix frames -/

private theorem arrivalMoveTokenDistLast
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

private theorem arrivalElimTokenPair
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

private theorem arrivalElimDistLast
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

private theorem arrivalWhitePreservesBlack
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

private theorem arrivalPplSelectedTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind
          (arrivalSelectedOutput
            hpsi kind l r).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind
          (arrivalSelectedOutput
            hpsi kind l r).2 := by
  cases kind with
  | black =>
      let p := arrivalPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        arrivalWhitePreservesBlack
          hpsi b.1 b.2
      have he :=
        arrivalElimTokenPair .black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          arrivalSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact ⟨he.1.trans hw.1, he.2.trans hw.2⟩
  | white =>
      let p := arrivalPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        arrivalElimTokenPair .white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          arrivalSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem arrivalPplSelectedDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (ppl hpsi l r).1.dist =
        (arrivalSelectedOutput
          hpsi kind l r).1.dist ∧
      (ppl hpsi l r).1.last =
        (arrivalSelectedOutput
          hpsi kind l r).1.last ∧
      (ppl hpsi l r).2.dist =
        (arrivalSelectedOutput
          hpsi kind l r).2.dist ∧
      (ppl hpsi l r).2.last =
        (arrivalSelectedOutput
          hpsi kind l r).2.last := by
  cases kind with
  | black =>
      let p := arrivalPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        arrivalMoveTokenDistLast
          hpsi .white b.1 b.2
      have he :=
        arrivalElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          arrivalSelectedOutput
              hpsi .black l r = b := by
        rfl
      rw [hfull, hsel]
      exact
        ⟨he.1.trans hw.1,
          he.2.1.trans hw.2.1,
          he.2.2.1.trans hw.2.2.1,
          he.2.2.2.trans hw.2.2.2⟩
  | white =>
      let p := arrivalPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        arrivalElimDistLast w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hsel :
          arrivalSelectedOutput
              hpsi .white l r = w := by
        rfl
      rw [hfull, hsel]
      exact he

private theorem arrivalStepTokenPair
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
        (arrivalSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 ∧
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)) =
      tokenAt kind
        (arrivalSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
  have hp :=
    arrivalPplSelectedTokenPair
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

private theorem arrivalStepDistLast
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ((ghostStep hpsi ring step G e).phys e).dist =
        (arrivalSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.dist ∧
      ((ghostStep hpsi ring step G e).phys e).last =
        (arrivalSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.last ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        (arrivalSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.dist ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).last =
        (arrivalSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.last := by
  have hp :=
    arrivalPplSelectedDistLast
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

private theorem arrivalCd_two_le_n
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

private theorem arrivalRightNeighbor_ne
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

private theorem arrivalRightNeighbor_shiftRight
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

private theorem arrivalGhostSoundAt
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧
      arrivalLocalValid
        kind (G.phys i) z.value := by
  cases kind with
  | black =>
      exact hsound.1 i z howner
  | white =>
      exact hsound.2 i z howner

private theorem arrivalLastDistPlusD
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

private theorem arrivalLastPositiveTargetBelow
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
    arrivalLastDistPlusD
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

private theorem arrivalPositiveNotLast
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
      arrivalLocalValid kind q t)
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    False := by
  have ht :=
    arrivalLastPositiveTargetBelow
      hpsi kind q t hdist hpos
  unfold arrivalLocalValid at hlocal
  dsimp only at hlocal
  rcases hlocal with hp | hn <;> omega

private theorem arrivalValidToken_of_local
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
      arrivalLocalValid kind q t) :
    ValidToken kind C i := by
  unfold ValidToken
  rw [htok]
  unfold arrivalLocalValid at hlocal
  unfold tokenTargetCoordinate at hlocal ⊢
  rw [hdist]
  exact hlocal

private theorem arrivalFresh_advance
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

private def arrivalBounceNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) : TokenData psi :=
  arrivalMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2

private theorem arrivalClass
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
      ((arrivalGhostMoveToken
            hpsi kind step site
            l r (some z) gr).left =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        False) ∧
      ((arrivalGhostMoveToken
            hpsi kind step site
            l r (some z) gr).right =
          some z' →
        z'.lmeta.id = z.lmeta.id →
        z'.lmeta =
            ghostStepLineageAdvance z.lmeta ∧
          z'.value =
            arrivalBounceNext hpsi z.value ∧
          arrivalLocalValid kind r z'.value ∧
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
              arrivalMkToken
                (offsetNegPsiPlusOneCode psi hpsi)
                t.1.2 t.2
            let b :=
              arrivalBumpTo kind r next gl2
            ⟨none, b.live, b.done⟩
          else if h2 : 2 ≤ c then
            have hvalid : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              arrivalMkToken
                (encodeOffset psi (c - 1) (by
                  rcases hvalid with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
                t.1.2 t.2
            let b :=
              arrivalBumpTo kind r next gl2
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
                    arrivalNegTurnNext hpsi l.id tr
                  let b :=
                    arrivalBumpTo kind l next gr0
                  ⟨b.live, none, b.done⟩
                else if hm2 : cr ≤ -2 then
                  have hvalid : ValidOffset psi cr :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    arrivalMkToken
                      (encodeOffset psi (cr + 1) (by
                        rcases hvalid with hn | hp
                        · left
                          omega
                        · exfalso
                          omega))
                      tr.1.2 tr.2
                  let b :=
                    arrivalBumpTo kind l next gr0
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
                  arrivalNegTurnNext hpsi l.id tr
                let b :=
                  arrivalBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : cr ≤ -2 then
                have hvalid : ValidOffset psi cr :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode tr)
                let next :=
                  arrivalMkToken
                    (encodeOffset psi (cr + 1) (by
                      rcases hvalid with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    tr.1.2 tr.2
                let b :=
                  arrivalBumpTo kind l next gr0
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
        noId (arrivalLiveShadow kind q g) := by
    intro q g hg u hu hid
    cases g with
    | none =>
        simp [arrivalLiveShadow] at hu
    | some g0 =>
        cases ht : tokenAt kind q with
        | none =>
            simp [arrivalLiveShadow, ht] at hu
        | some t =>
            by_cases hv :
                g0.value = t ∧
                  arrivalLocalValid kind q t
            · have hgu : g0 = u := by
                simpa [arrivalLiveShadow, ht, hv]
                  using hu
              subst u
              exact hg g0 rfl hid
            · simp [arrivalLiveShadow, ht, hv] at hu

  have hSourceShadow :
      ∀ u : GhostToken n psi,
        arrivalLiveShadow kind l (some z) = some u →
        u = z ∧
          arrivalLiveValue kind l = some z.value := by
    intro u hu
    cases ht : tokenAt kind l with
    | none =>
        simp [arrivalLiveShadow, ht] at hu
    | some t =>
        by_cases hv :
            z.value = t ∧
              arrivalLocalValid kind l t
        · have hzu : z = u := by
            simpa [arrivalLiveShadow, ht, hv]
              using hu
          subst u
          constructor
          · rfl
          · unfold arrivalLiveValue
            simp [ht, hv.1, hv.2]
        · simp [arrivalLiveShadow, ht, hv] at hu

  have hBumpNoId :
      ∀ (q : State psi kappa)
        (v : TokenData psi)
        (g : Option (GhostToken n psi)),
        noId g →
        noId (arrivalBumpTo kind q v g).live := by
    intro q v g hg u hu hid
    cases g with
    | none =>
        simp [arrivalBumpTo] at hu
    | some g0 =>
        by_cases hv :
            arrivalLocalValid kind q v
        · simp only
            [arrivalBumpTo, if_pos hv,
              Option.some.injEq] at hu
          subst u
          have hid0 :
              g0.lmeta.id = z.lmeta.id := by
            simpa [ghostStepLineageAdvance]
              using hid
          exact hg g0 rfl hid0
        · simp [arrivalBumpTo, hv] at hu

  have hBumpSome :
      ∀ (q : State psi kappa)
        (v : TokenData psi)
        (g u : GhostToken n psi),
        (arrivalBumpTo kind q v (some g)).live =
            some u →
        u.lmeta =
            ghostStepLineageAdvance g.lmeta ∧
          u.value = v ∧
          arrivalLocalValid kind q v := by
    intro q v g u hu
    by_cases hv :
        arrivalLocalValid kind q v
    · simp only
        [arrivalBumpTo, if_pos hv,
          Option.some.injEq] at hu
      subst u
      exact ⟨rfl, rfl, hv⟩
    · simp [arrivalBumpTo, hv] at hu

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
                    (arrivalNegTurnNext hpsi l.id t)
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
                        (arrivalNegTurnNext
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
    rw [arrivalSourceSet_eq]
    cases kind <;> rfl

  have hClearToken :
      ∀ q : State psi kappa,
        tokenAt kind (sourceClear kind q) =
          arrivalLiveValue kind q := by
    intro q
    rw [arrivalSourceClear_eq]
    unfold arrivalClearInvalid arrivalLiveValue
    cases ht : tokenAt kind q with
    | none =>
        simp only [ht]
    | some t =>
        by_cases hv :
            arrivalLocalValid kind q t
        · simp only [ht, if_pos hv]
        · simp only [ht, if_neg hv]
          unfold arrivalSetToken
          cases kind <;> rfl

  have hClearLast :
      ∀ q : State psi kappa,
        (sourceClear kind q).last = q.last := by
    intro q
    rw [arrivalSourceClear_eq]
    unfold arrivalClearInvalid
    cases ht : tokenAt kind q with
    | none =>
        simp only [ht]
    | some t =>
        by_cases hv :
            arrivalLocalValid kind q t
        · simp only [ht, if_pos hv]
        · simp only [ht, if_neg hv]
          unfold arrivalSetToken
          cases kind <;> rfl

  let lv0 := arrivalLiveValue kind l
  let rv0 := arrivalLiveValue kind r
  let gl0 := arrivalLiveShadow kind l (some z)
  let gr0 := arrivalLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    arrivalBirthGhost
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
    simpa [birth, arrivalBirthGhost]
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
              arrivalLiveShadow kind l (some z) =
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
      arrivalGhostMoveToken
          hpsi kind step site
          l r (some z) gr =
        finish lv2 rv0 gl2 gr0 := by
    unfold arrivalGhostMoveToken
    simp only [dif_pos hgate]
    rfl

  have hPhysical :
      lv0 = some z.value →
      rv0 = none →
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some (arrivalBounceNext hpsi z.value) := by
    intro hlv hrv
    have hlv' :
        arrivalLiveValue kind l =
          some z.value := by
      simpa [lv0] using hlv
    have hrv' :
        arrivalLiveValue kind r = none := by
      simpa [rv0] using hrv
    rw [← arrivalMoveToken_eq hpsi kind l r]
    unfold arrivalMoveToken
    simp
      [hClearToken, hClearLast, hSetToken,
        hlv', hrv', hgate.1, hgate.2, hc,
        arrivalBounceNext]

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
              arrivalBounceNext hpsi z.value ∧
            arrivalLocalValid kind r u.value ∧
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
          (arrivalBumpTo
              kind r
              (arrivalBounceNext hpsi z.value)
              (some z)).live =
            some u := by
        simpa
          [finish, hc, arrivalBounceNext]
          using hu
      have hs :=
        hBumpSome
          r (arrivalBounceNext hpsi z.value)
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

private theorem arrivalClass_left
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
      (arrivalGhostMoveToken
          hpsi kind step site
          l r (some z) gr).left =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    False := by
  exact
    (arrivalClass
      hpsi kind step site l r gr z
      hgate hNoRight hNotBirth hc z').1
      hout hid

private theorem arrivalClass_right
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
      (arrivalGhostMoveToken
          hpsi kind step site
          l r (some z) gr).right =
        some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    z'.lmeta =
        ghostStepLineageAdvance z.lmeta ∧
      z'.value =
        arrivalBounceNext hpsi z.value ∧
      arrivalLocalValid kind r z'.value ∧
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some z'.value := by
  exact
    (arrivalClass
      hpsi kind step site l r gr z
      hgate hNoRight hNotBirth hc z').2
      hout hid

/-! ## Arrival-stage arithmetic -/

private theorem arrivalOldTarget
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

private theorem arrivalBounceTarget
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

private theorem arrivalStage_eq
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

private theorem arrivalProgress_eq
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

theorem lemma4SweepInitiatorArrivalRow_proved :
    Lemma4SweepInitiatorArrivalRow := by
  unfold Lemma4SweepInitiatorArrivalRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hc

  rcases hp with
    ⟨hCd, hCd', _hcovered, hsound,
      huniq, _hkin, hwin, howner, hsame⟩

  have hn2 :
      2 ≤ n :=
    arrivalCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    arrivalRightNeighbor_ne ring hn2 e

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
    arrivalGhostSoundAt
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
          (arrivalPositiveNotLast
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
        arrivalRightNeighbor_shiftRight
          ring k x.val
      _ = shiftRight ring k y.val := by
        rfl

  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hr⟩

  let p :=
    arrivalSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  let s :=
    arrivalSelectedOutput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hmoveDL :
      s.1.dist = p.1.dist ∧
        s.1.last = p.1.last ∧
        s.2.dist = p.2.dist ∧
        s.2.last = p.2.last := by
    simpa [s, p, arrivalSelectedOutput]
      using
        arrivalMoveTokenDistLast
          hpsi kind p.1 p.2

  have hstepDL :=
    arrivalStepDistLast
      hpsi ring step G e kind hne
  have hstepTok :=
    arrivalStepTokenPair
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
          (arrivalGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).left =
            some zL ∧
          zL.lmeta.id = z.lmeta.id) ∨
        (∃ zR : GhostToken n psi,
          (arrivalGhostMoveToken
              hpsi kind step e
              p.1 p.2 (some z)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id)) := by
    have hs := hsame
    rw [← arrivalSelectedPair_eq_export
      hpsi ring step G e kind] at hs
    simpa
      [arrivalSelectedPair, p, howner]
      using hs

  have hclass :=
    arrivalClass
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
        (arrivalSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      simpa
        [arrivalSelectedPair, p, howner]
        using hR

    have hRExport :
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
      rw [← arrivalSelectedPair_eq_export
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
        simpa [s, p, arrivalSelectedOutput]
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
      arrivalValidToken_of_local
        kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        p.2 z'.value
        htokPost hdestDist hlocal

    have hdecode :
        decodeOffset psi (tokenCode z'.value) =
          1 - ((psi : Nat) : Int) := by
      rw [hvalue]
      unfold arrivalBounceNext
      dsimp [arrivalMkToken, tokenCode]
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
      arrivalOldTarget
        hpsi kind (G.phys e) z.value
        x.val x.isLt hnext hpreDist hc

    have hlowTarget :
        ((psi : Nat) : Int) ≤
          tokenTargetCoordinate kind
            (G.phys e) z.value := by
      have hlocalPre := hpre.2
      unfold arrivalLocalValid at hlocalPre
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
      arrivalBounceTarget
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
      arrivalStage_eq
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
      arrivalProgress_eq
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
        arrivalFresh_advance
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

end PPL

#print axioms PPL.lemma4SweepInitiatorArrivalRow_proved
