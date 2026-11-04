import Leader.PPL.TokenCorrectness.PersistenceRightRow

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Remark 2 right-owner row: truth audit and concrete refutation

The current Remark2RightOwnerRow is false.

Its c = 1 branch puts a source-relative cyclic-offset equation inside the
pure Algorithm-3 owner row, even though that row has no WorkingFor,
CorrectToken, or CDLAt premise.  A legal c = 1 turn across the ring wrap
violates that equation.

The local ghost mirror below is definitionally equal to the inaccessible
private selected-color row used by ghostStep.  It is included so the concrete
post-owner fact is checked against the literal ghost transition rather than a
shadow semantic assumption.
-/

/-! ## Definitionally mirrored private selected-color ghost row -/

private def rightOwnerBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def rightOwnerMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def rightOwnerLocalValid {psi kappa : Nat}
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

private instance instDecidableRightOwnerLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (rightOwnerLocalValid kind q t) := by
  unfold rightOwnerLocalValid
  infer_instance

private def rightOwnerPrelude {psi kappa : Nat}
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

private def rightOwnerLiveShadow
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
              (rightOwnerLocalValid kind q t) then
            some z
          else
            none

private def rightOwnerLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if rightOwnerLocalValid kind q t then
        some t
      else
        none

private def rightOwnerBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      rightOwnerMkToken
        (offsetPsiCode psi hpsi)
        (rightOwnerBitToFin (!idBit))
        (rightOwnerBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def rightOwnerBumpTo
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
        if rightOwnerLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def rightOwnerGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := rightOwnerLiveValue kind l
  let rv0 := rightOwnerLiveValue kind r
  let gl0 := rightOwnerLiveShadow kind l gl
  let gr0 := rightOwnerLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (rightOwnerBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (rightOwnerBirthGhost
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
            rightOwnerMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            rightOwnerBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            rightOwnerMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            rightOwnerBumpTo
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
                    rightOwnerMkToken
                      (offsetPsiCode psi hpsi)
                      (rightOwnerBitToFin (!l.id))
                      (rightOwnerBitToFin l.id)
                  else
                    rightOwnerMkToken
                      (offsetPsiCode psi hpsi)
                      (rightOwnerBitToFin l.id)
                      (0 : Fin 2)
                let b :=
                  rightOwnerBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  rightOwnerMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  rightOwnerBumpTo
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
                  rightOwnerMkToken
                    (offsetPsiCode psi hpsi)
                    (rightOwnerBitToFin (!l.id))
                    (rightOwnerBitToFin l.id)
                else
                  rightOwnerMkToken
                    (offsetPsiCode psi hpsi)
                    (rightOwnerBitToFin l.id)
                    (0 : Fin 2)
              let b :=
                rightOwnerBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                rightOwnerMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                rightOwnerBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def rightOwnerSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def rightOwnerSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := rightOwnerPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2

private def rightOwnerMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let pre :=
    rightOwnerSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  rightOwnerGhostMoveToken
    hpsi kind step e
    pre.1 pre.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

/-- Definitional bridge to the private selected-color branch of ghostStep. -/
private def rightOwnerGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      rightOwnerSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (rightOwnerMovedPair
          hpsi ring step G e kind).left
        (rightOwnerMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl

/-! ## Minimal corrected literal row -/

def remark2RightTurnValue
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi) : TokenData psi :=
  rightOwnerMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2

/--
This is the information the pure selected-color row can state without any
source-segment premise.

For c >= 2 the right move preserves the physical target.  For c = 1 the
literal fact is the exact Algorithm-3 turn value.  The source-relative
cyclic-offset equation belongs in the semantic assembly, where CorrectToken
and WorkingFor are available.
-/
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

/-! ## Concrete c = 1 wrap counterexample -/

private abbrev qRing : DirectedRing 5 :=
  ⟨by omega⟩

private abbrev q0 : Fin 5 :=
  ⟨0, by omega⟩

private abbrev q4 : Fin 5 :=
  ⟨4, by omega⟩

private def qHpsi : 2 <= 2 := by
  decide

private def qSeg :
    Fin (segmentCount 5 2 - 2) :=
  ⟨0, by decide⟩

private def qOldToken : TokenData 2 :=
  ((offsetOneCode 2 qHpsi, (0 : Fin 2)),
    (0 : Fin 2))

private def qTurnToken : TokenData 2 :=
  ((offsetNegPsiPlusOneCode 2 qHpsi,
      (0 : Fin 2)),
    (0 : Fin 2))

private def qMeta : LineageMeta 5 :=
  { id := .initial .black q4
    birthSite := q4
    birthStep := 0
    moves := 0 }

private def qTurnMeta : LineageMeta 5 :=
  { qMeta with
    moves := qMeta.moves + 1 }

private def qZ : GhostToken 5 2 :=
  { value := qOldToken
    lmeta := qMeta }

private def qZTurn : GhostToken 5 2 :=
  { value := qTurnToken
    lmeta := qTurnMeta }

private def qLeft : State 2 0 :=
  { leader := false
    id := false
    dist := (1 : Fin 4)
    last := false
    tokenB := some qOldToken
    tokenW := none
    mode := true
    clock := (0 : Fin 1)
    signalR := (0 : Fin 1)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

private def qRight : State 2 0 :=
  { leader := false
    id := false
    dist := (2 : Fin 4)
    last := false
    tokenB := none
    tokenW := none
    mode := true
    clock := (0 : Fin 1)
    signalR := (0 : Fin 1)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

private def qOther : State 2 0 :=
  { leader := false
    id := false
    dist := (0 : Fin 4)
    last := false
    tokenB := none
    tokenW := none
    mode := true
    clock := (0 : Fin 1)
    signalR := (0 : Fin 1)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

private def qConfig : Config 5 2 0 :=
  fun i =>
    if i = q4 then qLeft
    else if i = q0 then qRight
    else qOther

private def qGhost : GhostConfig 5 2 0 :=
  { phys := qConfig
    black := fun i =>
      if i = q4 then some qZ else none
    white := fun _ => none
    completed := [] }

private def qRightNeighbor :
    qRing.rightNeighbor q4 = q0 := by
  decide

private def qOwner :
    ghostTokenAt TokenKind.black qGhost q4 =
      some qZ := by
  simp [qGhost, ghostTokenAt]

private def qBlackOwnerShape
    (i : Fin 5) (z : GhostToken 5 2)
    (h :
      ghostTokenAt TokenKind.black qGhost i =
        some z) :
    And (i = q4) (z = qZ) := by
  by_cases hi : i = q4
  · subst i
    have hz : qZ = z := by
      simpa [qGhost, ghostTokenAt] using h
    exact And.intro rfl hz.symm
  · have hf : False := by
      simpa [qGhost, ghostTokenAt, hi] using h
    exact hf.elim

private def qWhiteOwnerFalse
    (i : Fin 5) (z : GhostToken 5 2)
    (h :
      ghostTokenAt TokenKind.white qGhost i =
        some z) :
    False := by
  simpa [qGhost, ghostTokenAt] using h

private def qGhostSound :
    GhostSound qGhost := by
  change
    And
      (forall i z,
        ghostTokenAt TokenKind.black qGhost i =
            some z ->
          And
            (tokenAt TokenKind.black
                (qGhost.phys i) =
              some z.value)
            (rightOwnerLocalValid
              TokenKind.black
              (qGhost.phys i) z.value))
      (forall i z,
        ghostTokenAt TokenKind.white qGhost i =
            some z ->
          And
            (tokenAt TokenKind.white
                (qGhost.phys i) =
              some z.value)
            (rightOwnerLocalValid
              TokenKind.white
              (qGhost.phys i) z.value))
  refine And.intro ?_ ?_
  · intro i z hz
    have hs := qBlackOwnerShape i z hz
    rcases hs with ⟨rfl, rfl⟩
    exact And.intro (by decide)
      (by unfold rightOwnerLocalValid; decide)
  · intro i z hz
    exact False.elim
      (qWhiteOwnerFalse i z hz)

private def qGhostIdsUnique :
    GhostIdsUniqueAt 0 qGhost := by
  refine And.intro ?_ ?_
  · intro kind i j zi zj hi hj _hid
    cases kind with
    | black =>
        have hsi :=
          qBlackOwnerShape i zi hi
        have hsj :=
          qBlackOwnerShape j zj hj
        exact hsi.1.trans hsj.1.symm
    | white =>
        exact False.elim
          (qWhiteOwnerFalse i zi hi)
  · intro kind i z bornKind s hi hid
    cases kind with
    | black =>
        have hs :=
          qBlackOwnerShape i z hi
        rw [hs.2] at hid
        cases hid
    | white =>
        exact False.elim
          (qWhiteOwnerFalse i z hi)

private def qPostOwner :
    ghostTokenAt TokenKind.black
        (ghostStep qHpsi qRing 0 qGhost q4) q0 =
      some qZTurn := by
  rw [rightOwnerGhostTokenAtStep
    qHpsi qRing 0 qGhost q4
    TokenKind.black q0]
  decide

private def qMotionFalse :
    Not
      (Remark2RightMotionData
        qRing q0 qSeg.val
        q4 q0 qOldToken qTurnToken) := by
  unfold Remark2RightMotionData
  decide

/--
Kernel-level refutation of the current residual.

The tracked black token is at site 4 with c = 1.  The literal selected-color
row turns it to site 0 with c = -1.  Both local-validity tests pass, so the
same lineage remains live.  But with root 0 and seg 0 the old target is site 0
(relative coordinate 0) while the new target is site 4 (relative coordinate
4).  Remark2RightMotionData asks for 4 = 0 - 2 + 1, i.e. 4 = 1.
-/
theorem remark2RightOwnerRow_false :
    Not Remark2RightOwnerRow := by
  intro hrow
  have hout :=
    hrow
      (n := 5) (psi := 2) (kappa := 0)
      qHpsi (by decide)
      qRing q0 qSeg
      0 qConfig q4 qGhost
      TokenKind.black qZ
      rfl qGhostSound qGhostIdsUnique qOwner
      q0 qZTurn
      qPostOwner rfl
      (Or.inr qRightNeighbor.symm)
  rcases hout with hstay | hmove
  · have hne : q0 ≠ q4 := by
      decide
    exact hne hstay.1
  · exact qMotionFalse hmove.2.2

end PPL

#print axioms PPL.remark2RightOwnerRow_false
#check PPL.Remark2RightOwnerRowCorrected

