import Leader.PPL.TokenCorrectness.PersistenceClosed

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Remark 2 survivor frame

Truth audit:

* the old duplicate-owner counterexample is excluded by
  `GhostIdsUniqueAt step G`;
* `GhostIdsBefore step G` excludes a fresh `.born kind step` owner from
  aliasing an older tracked lineage ID;
* after `ghostIdsUnique_step`, any live same-ID post owner is unique;
* off-pair owners are definitionally unchanged by `ghostStep`;
* on the interacted pair, the selected-color row has exactly the ordinary
  stay/move/turn cases plus the c = -1 turn already isolated by
  `Remark2NegTurnCarry`.

This bounded file proves the global uniqueness/locality reduction and leaves
one local selected-color pair row, `Remark2InteractedPairRow`.  That Prop is
the literal Algorithm-3 row only; it carries no scheduler, reachability, or
paper-level assumption.
-/

/-! ## Definitionally mirrored selected-color ghost row

These are copied from TokenCorrectnessRemark2.lean under new private names
because the originals are private.
-/

private def frameBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def frameMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def frameLocalValid {psi kappa : Nat}
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

private instance instDecidableFrameLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (frameLocalValid kind q t) := by
  unfold frameLocalValid
  infer_instance

private def frameTokenPrelude {psi kappa : Nat}
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
    else if Or (r1.dist.val = 0) (r1.dist.val = psi) then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def frameLiveShadow
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
          if And (z.value = t) (frameLocalValid kind q t) then
            some z
          else
            none

private def frameLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if frameLocalValid kind q t then
        some t
      else
        none

private def frameBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      frameMkToken (offsetPsiCode psi hpsi)
        (frameBitToFin (!idBit))
        (frameBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def frameBumpTo
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
        { z.lmeta with moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi :=
        { value := newValue, lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if frameLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def frameFinishMove
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match lv2 with
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let next :=
          frameMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := frameBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          frameMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := frameBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                if t.2 = (1 : Fin 2) then
                  frameMkToken
                    (offsetPsiCode psi hpsi)
                    (frameBitToFin (!l.id))
                    (frameBitToFin l.id)
                else
                  frameMkToken
                    (offsetPsiCode psi hpsi)
                    (frameBitToFin l.id)
                    (0 : Fin 2)
              let b := frameBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid psi (by omega) (tokenCode t)
              let next :=
                frameMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b := frameBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  | none =>
      match rv0 with
      | none =>
          ⟨gl2, gr0, []⟩
      | some t =>
          let c := decodeOffset psi (tokenCode t)
          if hm1 : c = -1 then
            let next :=
              if t.2 = (1 : Fin 2) then
                frameMkToken
                  (offsetPsiCode psi hpsi)
                  (frameBitToFin (!l.id))
                  (frameBitToFin l.id)
              else
                frameMkToken
                  (offsetPsiCode psi hpsi)
                  (frameBitToFin l.id)
                  (0 : Fin 2)
            let b := frameBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c <= -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid psi (by omega) (tokenCode t)
            let next :=
              frameMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b := frameBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def frameGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := frameLiveValue kind l
  let rv0 := frameLiveValue kind r
  let gl0 := frameLiveShadow kind l gl
  let gr0 := frameLiveShadow kind r gr
  if And (l.last = false) (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some (frameBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some (frameBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := And (lv1 ≠ none) (rv0 ≠ none)
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    frameFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def frameSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def frameMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let pre :=
    frameTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      frameGhostMoveToken hpsi .black step e
        pre.1 pre.2
        (G.black e) (G.black rsite)
  | .white =>
      let qb :=
        moveToken hpsi .black pre.1 pre.2
      frameGhostMoveToken hpsi .white step e
        qb.1 qb.2
        (G.white e) (G.white rsite)

private theorem frameGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      frameSetTwo (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (frameMovedPair
          hpsi ring step G e kind).left
        (frameMovedPair
          hpsi ring step G e kind).right i := by
  cases kind <;> rfl

/-! ## TransitionFacts projections needed by the remaining pair row -/

private theorem frameMoveTokenInitiatorId
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.id = l.id := by
  have h :=
    congrArg
      (fun q : State psi kappa => q.id)
      (moveToken_initiator_fields
        hpsi kind l r)
  cases kind <;>
    simpa [eraseKindToken] using h

private theorem frameMoveTokenResponderDistLast
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    ((moveToken hpsi kind l r).2.dist,
        (moveToken hpsi kind l r).2.last) =
      (r.dist, r.last) := by
  rcases
      moveToken_responder_fields
        hpsi kind l r with h | h
  · have h' :=
      congrArg
        (fun q : State psi kappa =>
          (q.dist, q.last)) h
    cases kind <;>
      simpa [eraseKindTokenId,
        eraseKindToken] using h'
  · have h' :=
      congrArg
        (fun q : State psi kappa =>
          (q.dist, q.last)) h
    cases kind <;>
      simpa [eraseKindTokenId,
        eraseKindToken, birthFields] using h'

private theorem frameMoveTokenView4
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      (PPL.Elim.view4
          (moveToken hpsi kind l r).1 =
        PPL.Elim.view4 l)
      (Or
        (PPL.Elim.view4
            (moveToken hpsi kind l r).2 =
          PPL.Elim.view4 r)
        (PPL.Elim.view4
            (moveToken hpsi kind l r).2 =
          (⟨true, (2 : Fin 3), true, false⟩ :
            PPL.Elim.Cell4))) := by
  exact
    moveToken_view4_cases
      hpsi kind l r

/-! ## Source-Iota transport for an unchanged occurrence -/

private theorem frameSourceIotaBit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg : Nat)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg)
    (x : Fin psi) :
    (C
        (shiftRight ring
          (sourceStart psi ring root seg)
          x.val)).id =
      (C'
        (shiftRight ring
          (sourceStart psi ring root seg)
          x.val)).id := by
  exact congrFun hsrc x

private theorem frameFirstZeroAuxSourceCongr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg fuel j : Nat)
    (hbound : j + fuel <= psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    firstZeroAux ring C
        (sourceStart psi ring root seg)
        fuel j =
      firstZeroAux ring C'
        (sourceStart psi ring root seg)
        fuel j := by
  induction fuel generalizing j with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold firstZeroAux
      have hj : j < psi := by
        omega
      let x : Fin psi := ⟨j, hj⟩
      have hb :=
        frameSourceIotaBit
          ring root C C' seg hsrc x
      change
        (C
          (shiftRight ring
            (sourceStart psi ring root seg)
            j)).id =
        (C'
          (shiftRight ring
            (sourceStart psi ring root seg)
            j)).id at hb
      rw [hb]
      split
      · rfl
      · exact
          ih (j := j + 1)
            (by omega)

private theorem frameFirstZeroSourceCongr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg : Nat)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    firstZeroBit ring C
        (sourceStart psi ring root seg) =
      firstZeroBit ring C'
        (sourceStart psi ring root seg) := by
  unfold firstZeroBit
  exact
    frameFirstZeroAuxSourceCongr
      ring root C C' seg psi 0
      (by omega) hsrc

private theorem framePayloadCorrectSourceCongr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg x : Nat) (hx : x < psi)
    (t : TokenData psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    Iff
      (payloadCorrect ring C
        (sourceStart psi ring root seg) x t)
      (payloadCorrect ring C'
        (sourceStart psi ring root seg) x t) := by
  unfold payloadCorrect
  have hj :=
    frameFirstZeroSourceCongr
      ring root C C' seg hsrc
  let ix : Fin psi := ⟨x, hx⟩
  have hb :=
    frameSourceIotaBit
      ring root C C' seg hsrc ix
  change
    (C
      (shiftRight ring
        (sourceStart psi ring root seg)
        x)).id =
      (C'
        (shiftRight ring
          (sourceStart psi ring root seg)
          x)).id at hb
  rw [hj, hb]

private theorem frameCorrectSameOccurrence
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (i : Fin n) (kind : TokenKind)
    (t : TokenData psi)
    (ht : tokenAt kind (C i) = some t)
    (ht' : tokenAt kind (C' i) = some t)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val) :
    CorrectToken ring root C' i kind seg.val := by
  unfold CorrectToken at hcorr ⊢
  rw [ht] at hcorr
  rw [ht']
  dsimp only at hcorr ⊢
  rcases hcorr with ⟨hparity, hrest⟩
  refine ⟨hparity, ?_⟩
  by_cases hpos :
      0 < decodeOffset psi (tokenCode t)
  · rw [if_pos hpos] at hrest ⊢
    rcases hrest with
      ⟨hrel, hx, hpay⟩
    exact
      ⟨hrel, hx,
        (framePayloadCorrectSourceCongr
          ring root C C' seg.val
          _ hx t hsrc).mp hpay⟩
  · rw [if_neg hpos] at hrest ⊢
    rcases hrest with
      ⟨hneg, hrel, hx, hpay⟩
    exact
      ⟨hneg, hrel, hx,
        (framePayloadCorrectSourceCongr
          ring root C C' seg.val
          _ hx t hsrc).mp hpay⟩

private theorem frameGhostSoundToken
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi)
    (hphys : G.phys = C)
    (hG : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    tokenAt kind (C i) = some z.value := by
  cases kind with
  | black =>
      have hs := hG.1 i z howner
      rw [hphys] at hs
      exact hs.1
  | white =>
      have hs := hG.2 i z howner
      rw [hphys] at hs
      exact hs.1

/-! ## The single remaining literal interacted-pair row -/

/--
Only residual in this bounded round.

Both the tracked pre owner and the selected same-ID post owner are on the
interacted pair.  The mirrored selected-color MoveToken row, together with the
three TransitionFacts projections above, must give either:

* an already-correct ordinary survivor; or
* exactly the responder c = -1 to initiator line-29 turn.

This is one Algorithm-3 row, not a global protocol hypothesis.
-/
def Remark2InteractedPairRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G i = some z ->
    ValidToken kind C i ->
    WorkingFor ring root C i kind seg.val ->
    CorrectToken ring root C i kind seg.val ->
    CDLAt ring root C ->
    CDLAt ring root
      (PopulationProtocol.step
        (protocol psi kappa) ring C e) ->
    forall (j : Fin n) (z' : GhostToken n psi),
      sourceIota ring root C seg.val =
        sourceIota ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          seg.val ->
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z' ->
      z'.lmeta.id = z.lmeta.id ->
      Or (i = e) (i = ring.rightNeighbor e) ->
      Or (j = e) (j = ring.rightNeighbor e) ->
      Or
        (CorrectToken ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          j kind seg.val)
        (And (j = e)
          (And (ring.rightNeighbor e = i)
            (And
              (tokenAt kind (C i) =
                some z.value)
              (And
                (decodeOffset psi
                    (tokenCode z.value) = -1)
                (And
                  (tokenAt kind
                      ((PopulationProtocol.step
                        (protocol psi kappa)
                        ring C e) e) =
                    some z'.value)
                  (z'.value =
                    remark2NegTurnValue
                      hpsi (C e).id
                      z.value))))))

/-! ## Global uniqueness/locality reduction -/

private theorem frameOldEndpointOfPostEndpoint
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi)
    (j : Fin n) (z' : GhostToken n psi)
    (huniq : GhostIdsUniqueAt step G)
    (howner :
      ghostTokenAt kind G i = some z)
    (hpost :
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z')
    (hid : z'.lmeta.id = z.lmeta.id)
    (hj :
      Or (j = e)
        (j = ring.rightNeighbor e)) :
    Or (i = e)
      (i = ring.rightNeighbor e) := by
  have hn2 : 2 <= n := by
    omega
  have hpostUnique :=
    (ghostIdsUnique_step
      hpsi hn2 ring step G e huniq).1
  by_cases hie : i = e
  · exact Or.inl hie
  · by_cases hir :
      i = ring.rightNeighbor e
    · exact Or.inr hir
    · have hiPost :
          ghostTokenAt kind
              (ghostStep hpsi ring step G e) i =
            some z := by
        rw [frameGhostTokenAtStep
          hpsi ring step G e kind i]
        simp [frameSetTwo, hie, hir, howner]
      have hij :
          i = j :=
        hpostUnique
          kind i j z z'
          hiPost hpost hid.symm
      rcases hj with hje | hjr
      · exact
          False.elim
            (hie (hij.trans hje))
      · exact
          False.elim
            (hir (hij.trans hjr))

theorem remark2SurvivorFrame
    (hrow : Remark2InteractedPairRow) :
    Remark2SurvivorFrame := by
  intro n psi kappa hpsi hn3
  intro ring root seg step C e G kind i z
  intro hphys hG huniq howner
  intro hvalid hwork hcorr hC hC'
  intro j z' hsrc hpost hid

  by_cases hje : j = e
  · have hiEnd :=
      frameOldEndpointOfPostEndpoint
        hpsi hn3 ring step G e kind
        i z j z' huniq howner hpost hid
        (Or.inl hje)
    exact
      hrow hpsi hn3 ring root seg
        step C e G kind i z
        hphys hG huniq howner
        hvalid hwork hcorr hC hC'
        j z' hsrc hpost hid
        hiEnd (Or.inl hje)

  · by_cases hjr :
      j = ring.rightNeighbor e
    · have hiEnd :=
        frameOldEndpointOfPostEndpoint
          hpsi hn3 ring step G e kind
          i z j z' huniq howner hpost hid
          (Or.inr hjr)
      exact
        hrow hpsi hn3 ring root seg
          step C e G kind i z
          hphys hG huniq howner
          hvalid hwork hcorr hC hC'
          j z' hsrc hpost hid
          hiEnd (Or.inr hjr)

    · have hjPre :
        ghostTokenAt kind G j = some z' := by
        rw [frameGhostTokenAtStep
          hpsi ring step G e kind j] at hpost
        simpa [frameSetTwo, hje, hjr]
          using hpost

      have hij : i = j :=
        huniq.1
          kind i j z z'
          howner hjPre hid.symm
      have hji : j = i := hij.symm
      subst j

      have hzz : z = z' := by
        rw [howner] at hjPre
        cases hjPre
        rfl
      subst z'

      have hstate :
          PopulationProtocol.step
              (protocol psi kappa)
              ring C e i =
            C i := by
        simp [PopulationProtocol.step,
          hje, hjr]

      have htok0 :
          tokenAt kind (C i) =
            some z.value :=
        frameGhostSoundToken
          C G kind i z
          hphys hG howner

      have htok1 :
          tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa)
                ring C e) i) =
            some z.value := by
        rw [hstate]
        exact htok0

      exact
        Or.inl
          (frameCorrectSameOccurrence
            ring root seg
            C
            (PopulationProtocol.step
              (protocol psi kappa)
              ring C e)
            i kind z.value
            htok0 htok1 hsrc hcorr)

/-- The closed assembly now needs only the literal interacted-pair row. -/
theorem remark2_one_step_unique_proved
    (hrow : Remark2InteractedPairRow) :
    remark2_one_step_unique :=
  remark2_one_step_unique_of_survivorFrame
    (remark2SurvivorFrame hrow)

#print axioms PPL.frameMoveTokenInitiatorId
#print axioms PPL.frameMoveTokenResponderDistLast
#print axioms PPL.frameMoveTokenView4
#print axioms PPL.remark2SurvivorFrame
#print axioms PPL.remark2_one_step_unique_proved

end PPL
