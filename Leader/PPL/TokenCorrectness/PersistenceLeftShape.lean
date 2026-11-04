import Leader.PPL.TokenCorrectness.PersistenceLeftRow

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Remark 2 left selected shape: private-row reduction

The upstream private ghost row cannot be unfolded by name from this module.
The definitions below mirror exactly the private TokenCorrectness row, in the
same style as the local mirrors used elsewhere.

Everything except the final finite selected-color pair split is discharged
here. The only residual is Remark2LeftSelectedMirrorRow.
-/

/-! ## Definitionally mirrored private ghost row -/

private def leftShapeBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def leftShapeMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def leftShapeLocalValid {psi kappa : Nat}
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

private instance instDecidableLeftShapeLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (leftShapeLocalValid kind q t) := by
  unfold leftShapeLocalValid
  infer_instance

private def leftShapePrelude {psi kappa : Nat}
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

private def leftShapeLiveShadow
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
              (leftShapeLocalValid kind q t) then
            some z
          else
            none

private def leftShapeLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if leftShapeLocalValid kind q t then
        some t
      else
        none

private def leftShapeBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      leftShapeMkToken
        (offsetPsiCode psi hpsi)
        (leftShapeBitToFin (!idBit))
        (leftShapeBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def leftShapeBumpTo
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
        if leftShapeLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def leftShapeGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := leftShapeLiveValue kind l
  let rv0 := leftShapeLiveValue kind r
  let gl0 := leftShapeLiveShadow kind l gl
  let gr0 := leftShapeLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (leftShapeBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (leftShapeBirthGhost
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
            leftShapeMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            leftShapeBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            leftShapeMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            leftShapeBumpTo
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
                    leftShapeMkToken
                      (offsetPsiCode psi hpsi)
                      (leftShapeBitToFin (!l.id))
                      (leftShapeBitToFin l.id)
                  else
                    leftShapeMkToken
                      (offsetPsiCode psi hpsi)
                      (leftShapeBitToFin l.id)
                      (0 : Fin 2)
                let b :=
                  leftShapeBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  leftShapeMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  leftShapeBumpTo
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
                  leftShapeMkToken
                    (offsetPsiCode psi hpsi)
                    (leftShapeBitToFin (!l.id))
                    (leftShapeBitToFin l.id)
                else
                  leftShapeMkToken
                    (offsetPsiCode psi hpsi)
                    (leftShapeBitToFin l.id)
                    (0 : Fin 2)
              let b :=
                leftShapeBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                leftShapeMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                leftShapeBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def leftShapeSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def leftShapeSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := leftShapePrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2

private def leftShapeSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre :=
    leftShapeSelectedInput hpsi kind l r
  moveToken hpsi kind pre.1 pre.2

private def leftShapeMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let pre :=
    leftShapeSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  leftShapeGhostMoveToken
    hpsi kind step e
    pre.1 pre.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

/-- Definitional bridge to the private selected-color row inside ghostStep. -/
private def leftShapeGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      leftShapeSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (leftShapeMovedPair
          hpsi ring step G e kind).left
        (leftShapeMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl

/-! ## Full physical-row projections -/

private def leftShapeRightNeighborNe
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt
  rcases Nat.lt_or_ge (e.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    omega
  · have h2 : e.val + 1 = n := by omega
    rw [h2, Nat.mod_self] at hv
    omega

private def leftShapeDetermineModeLeftId
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (determineMode l r).1.id = l.id := by
  simp only [determineMode]
  repeat' (first
    | split <;> try dsimp only
    | rfl)
  all_goals rfl

private def leftShapePreludeLeftId
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    (leftShapePrelude hpsi l r).1.id = l.id := by
  let s := createLeaderThroughLine6 hpsi l r
  have hs : s.left.id = l.id := by
    dsimp only [s, createLeaderThroughLine6]
    have hd :=
      leftShapeDetermineModeLeftId l r
    first
      | exact hd
      | (split <;> simpa using hd)
  dsimp only [leftShapePrelude]
  repeat' (first
    | split <;> try dsimp only
    | rfl)
  all_goals simpa [s] using hs

private def leftShapeSelectedInputLeftId
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (leftShapeSelectedInput
      hpsi kind l r).1.id = l.id := by
  cases kind with
  | black =>
      exact leftShapePreludeLeftId
        hpsi l r
  | white =>
      let p := leftShapePrelude hpsi l r
      have hi :=
        remark2Row_moveToken_initiator_fields
          hpsi TokenKind.black p.1 p.2
      have hid :=
        congrArg
          (fun q : State psi kappa => q.id) hi
      have hmid :
          (moveToken hpsi
            TokenKind.black p.1 p.2).1.id =
            p.1.id := by
        simpa [eraseKindToken] using hid
      exact hmid.trans
        (leftShapePreludeLeftId hpsi l r)

private def leftShapeElimTokenLeft
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

private def leftShapeElimTokenRight
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

private def leftShapeWhitePreservesBlack
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
    remark2Row_moveToken_initiator_fields
      hpsi TokenKind.white l r
  have hir :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  refine And.intro ?_ ?_
  · simpa [eraseKindToken, tokenAt]
      using hir
  · rcases
      remark2Row_moveToken_responder_fields
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

private def leftShapePplTokenPair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      (tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind
          (leftShapeSelectedOutput
            hpsi kind l r).1)
      (tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind
          (leftShapeSelectedOutput
            hpsi kind l r).2) := by
  cases kind with
  | black =>
      let p := leftShapePrelude hpsi l r
      let b :=
        moveToken hpsi TokenKind.black
          p.1 p.2
      let w :=
        moveToken hpsi TokenKind.white
          b.1 b.2
      have hw :=
        leftShapeWhitePreservesBlack
          hpsi b.1 b.2
      have hel :=
        leftShapeElimTokenLeft
          TokenKind.black w.1 w.2
      have her :=
        leftShapeElimTokenRight
          TokenKind.black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          leftShapeSelectedOutput
              hpsi TokenKind.black l r =
            b := by
        rfl
      rw [hfull, hselected]
      exact
        And.intro
          (hel.trans hw.1)
          (her.trans hw.2)
  | white =>
      let p := leftShapePrelude hpsi l r
      let b :=
        moveToken hpsi TokenKind.black
          p.1 p.2
      let w :=
        moveToken hpsi TokenKind.white
          b.1 b.2
      have hel :=
        leftShapeElimTokenLeft
          TokenKind.white w.1 w.2
      have her :=
        leftShapeElimTokenRight
          TokenKind.white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          leftShapeSelectedOutput
              hpsi TokenKind.white l r =
            w := by
        rfl
      rw [hfull, hselected]
      exact And.intro hel her

private def leftShapeStepTokenPair
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
          (leftShapeSelectedOutput
            hpsi kind
            (C e)
            (C (ring.rightNeighbor e))).1)
      (tokenAt kind
          ((PopulationProtocol.step
            (protocol psi kappa)
            ring C e)
            (ring.rightNeighbor e)) =
        tokenAt kind
          (leftShapeSelectedOutput
            hpsi kind
            (C e)
            (C (ring.rightNeighbor e))).2) := by
  have hne :
      ring.rightNeighbor e ≠ e :=
    leftShapeRightNeighborNe hn3 ring e
  have hp :=
    leftShapePplTokenPair
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

/-! ## The only remaining finite selected-color row

This is strictly smaller than Remark2LeftSelectedShape:

* no configuration;
* no ghostStep;
* no source/root/segment predicates;
* no correctness transport;
* the old responder ghost is literally some z;
* the only anti-alias hypotheses are exactly the old-left and fresh-birth
  exclusions supplied by GhostIdsUniqueAt.

Its proof is the finite expansion of leftShapeGhostMoveToken against the
public physical moveToken projections: responder stay, c <= -2 left move,
or c = -1 turn.
-/

def Remark2LeftSelectedMirrorRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi),
    (forall (zl : GhostToken n psi),
      gl = some zl ->
      zl.lmeta.id ≠ z.lmeta.id) ->
    z.lmeta.id ≠ .born kind step ->
    forall (z' : GhostToken n psi),
      And
        ((leftShapeGhostMoveToken
              hpsi kind step e
              l r gl (some z)).right =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).2 =
              some z.value))
        ((leftShapeGhostMoveToken
              hpsi kind step e
              l r gl (some z)).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          Or
            (And
              (tokenAt kind
                  (moveToken hpsi kind l r).1 =
                some z'.value)
              (And
                (decodeOffset psi
                    (tokenCode z.value) < 0)
                (And
                  (decodeOffset psi
                      (tokenCode z'.value) < 0)
                  (And
                    (tokenTargetSite ring e
                        z'.value =
                      tokenTargetSite ring
                        (ring.rightNeighbor e)
                        z.value)
                    (And
                      (tokenBitBool z'.value =
                        tokenBitBool z.value)
                      (tokenCarryBool z'.value =
                        tokenCarryBool z.value))))))
            (And
              (decodeOffset psi
                  (tokenCode z.value) = -1)
              (And
                (tokenAt kind
                    (moveToken hpsi kind l r).1 =
                  some z'.value)
                (z'.value =
                  remark2NegTurnValue
                    hpsi l.id z.value))))

/-! ## Lift the local mirror row to the residual -/

theorem remark2LeftSelectedShape_of_mirror
    (hrow : Remark2LeftSelectedMirrorRow) :
    Remark2LeftSelectedShape := by
  unfold Remark2LeftSelectedShape
  intro n psi kappa hpsi hn3
  intro ring step C e G kind z
  intro hphys _hG huniq howner
  subst C
  intro j z' hpost hid hj

  have hne :
      ring.rightNeighbor e ≠ e :=
    leftShapeRightNeighborNe hn3 ring e

  have hNoLeft :
      forall (zl : GhostToken n psi),
        ghostTokenAt kind G e = some zl ->
        zl.lmeta.id ≠ z.lmeta.id := by
    intro zl hl hzid
    have heq :=
      huniq.1
        kind e (ring.rightNeighbor e)
        zl z hl howner hzid
    exact hne heq.symm

  have hOldNotFresh :
      z.lmeta.id ≠ .born kind step := by
    intro hz
    have hs :=
      huniq.2
        kind (ring.rightNeighbor e) z
        kind step howner hz
    exact (Nat.lt_irrefl step) hs

  let p :=
    leftShapeSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))

  have hleftId :
      p.1.id = (G.phys e).id := by
    simpa [p] using
      leftShapeSelectedInputLeftId
        hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))

  have hstep :=
    leftShapeStepTokenPair
      hpsi hn3 ring G.phys e kind

  have hselected :
      leftShapeSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e)) =
        moveToken hpsi kind p.1 p.2 := by
    rfl

  rw [hselected] at hstep

  rw [leftShapeGhostTokenAtStep
    hpsi ring step G e kind j] at hpost

  have hlocal :=
    hrow hpsi ring step e kind
      p.1 p.2
      (ghostTokenAt kind G e)
      z hNoLeft hOldNotFresh z'

  rcases hj with hje | hjr
  · subst j
    have hlive :
        (leftShapeGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (some z)).left =
        some z' := by
      have hp := hpost
      simp only [leftShapeSetTwo, if_pos rfl]
        at hp
      change
        (leftShapeMovedPair
          hpsi ring step G e kind).left =
          some z' at hp
      change
        (leftShapeGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).left =
          some z' at hp
      rw [howner] at hp
      exact hp

    have hshape :=
      hlocal.2 hlive hid

    rcases hshape with hord | hturn
    · rcases hord with
        ⟨htok, hneg0, hneg1,
          htarget, hbit, hcarry⟩
      have htok' :
          tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa)
                ring G.phys e) e) =
            some z'.value := by
        rw [hstep.1]
        exact htok
      exact
        Or.inr
          (Or.inl
            ⟨rfl, htok', hneg0, hneg1,
              htarget, hbit, hcarry⟩)

    · rcases hturn with
        ⟨hcneg, htok, hzval⟩
      have htok' :
          tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa)
                ring G.phys e) e) =
            some z'.value := by
        rw [hstep.1]
        exact htok
      have hzval' :
          z'.value =
            remark2NegTurnValue
              hpsi (G.phys e).id z.value := by
        rw [← hleftId]
        exact hzval
      exact
        Or.inr
          (Or.inr
            ⟨rfl, hcneg, htok', hzval'⟩)

  · subst j
    have hlive :
        (leftShapeGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (some z)).right =
        some z' := by
      have hp := hpost
      simp only
        [leftShapeSetTwo, if_neg hne,
          if_pos rfl] at hp
      change
        (leftShapeMovedPair
          hpsi ring step G e kind).right =
          some z' at hp
      change
        (leftShapeGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).right =
          some z' at hp
      rw [howner] at hp
      exact hp

    have hstay :=
      hlocal.1 hlive hid
    rcases hstay with ⟨hzz, htok⟩
    subst z'

    have htok' :
        tokenAt kind
            ((PopulationProtocol.step
              (protocol psi kappa)
              ring G.phys e)
              (ring.rightNeighbor e)) =
          some z.value := by
      rw [hstep.2]
      exact htok

    exact
      Or.inl
        ⟨rfl, rfl, htok'⟩

#print axioms PPL.remark2LeftSelectedShape_of_mirror
#check PPL.Remark2LeftSelectedMirrorRow

end PPL
