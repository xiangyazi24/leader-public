import Leader.PPL.TokenCorrectness.PersistenceRightOwnerCorrected

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Definitionally equal local mirrors -/

private def rightMirrorBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def rightMirrorMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def rightMirrorLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
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

private instance instDecidableRightMirrorLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (rightMirrorLocalValid kind q t) := by
  unfold rightMirrorLocalValid
  infer_instance

private def rightMirrorSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def rightMirrorClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if rightMirrorLocalValid kind q t then
        q
      else
        rightMirrorSetToken kind q none

private def rightMirrorLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private theorem rightMirrorSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      rightMirrorSetToken kind q t := by
  cases kind <;> rfl

private theorem rightMirrorSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      rightMirrorClearInvalid kind q := by
  cases kind <;> rfl

private theorem rightMirrorSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = rightMirrorLeaderBirth q := by
  rfl

private def rightMirrorNegTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    rightMirrorMkToken
      (offsetPsiCode psi hpsi)
      (rightMirrorBitToFin (!sourceBit))
      (rightMirrorBitToFin sourceBit)
  else
    rightMirrorMkToken
      (offsetPsiCode psi hpsi)
      (rightMirrorBitToFin sourceBit)
      (0 : Fin 2)

private def rightMirrorLiveShadow
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
          if And
              (z.value = t)
              (rightMirrorLocalValid kind q t) then
            some z
          else
            none

private def rightMirrorLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if rightMirrorLocalValid kind q t then
        some t
      else
        none

private def rightMirrorBirthGhost
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      rightMirrorMkToken
        (offsetPsiCode psi hpsi)
        (rightMirrorBitToFin (!idBit))
        (rightMirrorBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def rightMirrorBumpTo
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
        if rightMirrorLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def rightMirrorGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := rightMirrorLiveValue kind l
  let rv0 := rightMirrorLiveValue kind r
  let gl0 := rightMirrorLiveShadow kind l gl
  let gr0 := rightMirrorLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (rightMirrorBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (rightMirrorBirthGhost
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
            rightMirrorMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            rightMirrorBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            rightMirrorMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            rightMirrorBumpTo
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
                  rightMirrorNegTurnNext
                    hpsi l.id t
                let b :=
                  rightMirrorBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  rightMirrorMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  rightMirrorBumpTo
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
                rightMirrorNegTurnNext
                  hpsi l.id t
              let b :=
                rightMirrorBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                rightMirrorMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                rightMirrorBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def rightMirrorMoveToken
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
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
            (rightMirrorMkToken
              (offsetPsiCode psi hpsi)
              (rightMirrorBitToFin (!l.id))
              (rightMirrorBitToFin l.id)))
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
            let c :=
              decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                rightMirrorNegTurnNext
                  hpsi l.id t
              let l :=
                sourceSet kind l (some next)
              let r :=
                sourceSet kind r none
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
                    (rightMirrorMkToken
                      nextOffset t.1.2 t.2))
              let r :=
                sourceSet kind r none
              (l, r)
            else
              (l, r)
    match tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c :=
          decodeOffset psi (tokenCode t)
        if hc1 : c = 1 then
          let bit := tokenBitBool t
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          let r :=
            sourceSet kind r
              (some
                (rightMirrorMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2))
          let l :=
            sourceSet kind l none
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
                (rightMirrorMkToken
                  nextOffset t.1.2 t.2))
          let l :=
            sourceSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)

private theorem rightMirrorMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    rightMirrorMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl

/-! ## Positive-move literal data -/

private theorem rightMirrorSubOneValid
    {psi : Nat}
    {c : Int}
    (hc : ValidOffset psi c)
    (h2 : 2 <= c) :
    ValidOffset psi (c - 1) := by
  rcases hc with hn | hp
  · exfalso
    omega
  · right
    omega

private def rightMirrorTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi) : TokenData psi :=
  rightMirrorMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2

private def rightMirrorPositiveNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (h2 :
      2 <= decodeOffset psi (tokenCode t)) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hc : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  rightMirrorMkToken
    (encodeOffset psi (c - 1)
      (rightMirrorSubOneValid hc h2))
    t.1.2 t.2

private theorem rightMirrorShiftRight_add
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (a b : Nat) :
    shiftRight ring (shiftRight ring i a) b =
      shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem rightMirrorShiftRight_afterNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (d : Nat) :
    shiftRight ring (ring.rightNeighbor e) d =
      shiftRight ring e (d + 1) := by
  calc
    shiftRight ring (ring.rightNeighbor e) d =
        shiftRight ring (shiftRight ring e 1) d := by
      rfl
    _ = shiftRight ring e (1 + d) :=
      rightMirrorShiftRight_add ring e 1 d
    _ = shiftRight ring e (d + 1) := by
      rw [Nat.add_comm]

private theorem rightMirrorToNatSubOne
    (c : Int)
    (hc : 2 <= c) :
    (c - 1).toNat + 1 = c.toNat := by
  have hleft :
      (((c - 1).toNat : Nat) : Int) = c - 1 :=
    Int.toNat_of_nonneg (by omega)
  have hright :
      ((c.toNat : Nat) : Int) = c :=
    Int.toNat_of_nonneg (by omega)
  omega

private theorem rightMirrorPositiveTarget
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (h2 :
      2 <= decodeOffset psi (tokenCode t)) :
    tokenTargetSite ring (ring.rightNeighbor e)
        (rightMirrorPositiveNext hpsi t h2) =
      tokenTargetSite ring e t := by
  let c : Int :=
    decodeOffset psi (tokenCode t)
  have hc : 2 <= c := by
    simpa [c] using h2
  have hnew :
      decodeOffset psi
          (tokenCode
            (rightMirrorPositiveNext hpsi t h2)) =
        c - 1 := by
    unfold rightMirrorPositiveNext
    dsimp only
    unfold rightMirrorMkToken
    simp only [tokenCode]
    rw [decode_encode]
    try rfl
  have hold :
      decodeOffset psi (tokenCode t) = c := by
    rfl
  have hpos : 0 < c := by
    omega
  have hposNew : 0 < c - 1 := by
    omega
  unfold tokenTargetSite
  rw [hnew, hold]
  rw [if_pos hposNew, if_pos hpos]
  have hs :=
    rightMirrorShiftRight_afterNeighbor
      ring e (c - 1).toNat
  have hto :=
    rightMirrorToNatSubOne c hc
  rw [hto] at hs
  exact hs

private theorem rightMirrorTurnLiteral
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) = (1 : Int)) :
    Remark2RightLiteralMotionData
      hpsi ring e (ring.rightNeighbor e)
      t (rightMirrorTurnNext hpsi t) := by
  unfold Remark2RightLiteralMotionData
  refine And.intro rfl (And.intro rfl (Or.inr (And.intro hc rfl)))

private theorem rightMirrorPositiveLiteral
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (h2 :
      2 <= decodeOffset psi (tokenCode t)) :
    Remark2RightLiteralMotionData
      hpsi ring e (ring.rightNeighbor e)
      t (rightMirrorPositiveNext hpsi t h2) := by
  unfold Remark2RightLiteralMotionData
  refine And.intro ?_ (And.intro ?_ (Or.inl ?_))
  · rfl
  · rfl
  · refine And.intro h2 (And.intro ?_ ?_)
    · unfold rightMirrorPositiveNext
      dsimp only
      unfold rightMirrorMkToken
      simp only [tokenCode]
      rw [decode_encode]
      have h2' : 2 <= decodeOffset psi t.fst.fst := h2
      omega
    · exact
        rightMirrorPositiveTarget
          hpsi ring e t h2

/-! ## Public residual mirrored through the local ghost function -/

private def RightMirrorSelectedMirrorRow : Prop :=
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
        ((rightMirrorGhostMoveToken
              hpsi kind step e
              l r (some z) gr).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).1 =
              some z.value))
        ((rightMirrorGhostMoveToken
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

private theorem rightMirrorSelectedMirrorRow_defeq :
    Remark2RightSelectedMirrorRowCorrected =
      RightMirrorSelectedMirrorRow := by
  rfl

/-! ## Finite classifier -/

private theorem rightMirrorCore
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoRight :
      forall zr : GhostToken n psi,
        gr = some zr ->
        zr.lmeta.id ≠ z.lmeta.id)
    (hNotBirth :
      z.lmeta.id ≠ .born kind step) :
    forall z' : GhostToken n psi,
      And
        ((rightMirrorGhostMoveToken
              hpsi kind step e
              l r (some z) gr).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).1 =
              some z.value))
        ((rightMirrorGhostMoveToken
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
              z.value z'.value)) := by
  classical

  let noId : Option (GhostToken n psi) -> Prop :=
    fun g =>
      forall u : GhostToken n psi,
        g = some u ->
        u.lmeta.id = z.lmeta.id ->
        False

  have hNoNone : noId none := by
    intro u hu _
    cases hu

  have hShadowNoId :
      forall (q : State psi kappa)
        (g : Option (GhostToken n psi)),
        noId g ->
        noId (rightMirrorLiveShadow kind q g) := by
    intro q g hg u hu hid
    cases g with
    | none =>
        simp [rightMirrorLiveShadow] at hu
    | some g0 =>
        cases ht : tokenAt kind q with
        | none =>
            simp [rightMirrorLiveShadow, ht] at hu
        | some t =>
            by_cases hv :
                g0.value = t ∧
                  rightMirrorLocalValid kind q t
            · have hgu : g0 = u := by
                simpa [rightMirrorLiveShadow, ht, hv]
                  using hu
              subst u
              exact hg g0 rfl hid
            · simp [rightMirrorLiveShadow, ht, hv] at hu

  have hSourceShadow :
      forall u : GhostToken n psi,
        rightMirrorLiveShadow kind l (some z) =
            some u ->
        u = z ∧
          rightMirrorLiveValue kind l =
            some z.value := by
    intro u hu
    cases ht : tokenAt kind l with
    | none =>
        simp [rightMirrorLiveShadow, ht] at hu
    | some t =>
        by_cases hv :
            z.value = t ∧
              rightMirrorLocalValid kind l t
        · have hzu : z = u := by
            simpa [rightMirrorLiveShadow, ht, hv]
              using hu
          have hu0 : u = z := hzu.symm
          subst u
          constructor
          · rfl
          · unfold rightMirrorLiveValue
            simp [ht, hv.1, hv.2]
        · simp [rightMirrorLiveShadow, ht, hv] at hu

  have hBumpNoId :
      forall (q : State psi kappa)
        (v : TokenData psi)
        (g : Option (GhostToken n psi)),
        noId g ->
        noId (rightMirrorBumpTo kind q v g).live := by
    intro q v g hg u hu hid
    cases g with
    | none =>
        simp [rightMirrorBumpTo] at hu
    | some g0 =>
        by_cases hv :
            rightMirrorLocalValid kind q v
        · simp only
            [rightMirrorBumpTo, if_pos hv,
              Option.some.injEq] at hu
          subst u
          have hid0 :
              g0.lmeta.id = z.lmeta.id := by
            exact hid
          exact hg g0 rfl hid0
        · simp [rightMirrorBumpTo, hv] at hu

  have hBumpSome :
      forall (q : State psi kappa)
        (v : TokenData psi)
        (g u : GhostToken n psi),
        (rightMirrorBumpTo kind q v (some g)).live =
            some u ->
        u.value = v ∧
          rightMirrorLocalValid kind q v := by
    intro q v g u hu
    by_cases hv :
        rightMirrorLocalValid kind q v
    · simp only
        [rightMirrorBumpTo, if_pos hv,
          Option.some.injEq] at hu
      subst u
      exact And.intro rfl hv
    · simp [rightMirrorBumpTo, hv] at hu

  have hSetToken :
      forall (q : State psi kappa)
        (v : Option (TokenData psi)),
        tokenAt kind (sourceSet kind q v) = v := by
    intro q v
    rw [rightMirrorSourceSet_eq]
    cases kind <;> rfl

  have hClearToken :
      forall q : State psi kappa,
        tokenAt kind (sourceClear kind q) =
          rightMirrorLiveValue kind q := by
    intro q
    rw [rightMirrorSourceClear_eq]
    unfold rightMirrorClearInvalid rightMirrorLiveValue
    cases ht : tokenAt kind q with
    | none =>
        simp only [ht]
    | some t =>
        by_cases hv :
            rightMirrorLocalValid kind q t
        · simp only [ht, if_pos hv]
        · simp only [ht, if_neg hv]
          unfold rightMirrorSetToken
          cases kind <;> rfl

  have hClearLast :
      forall q : State psi kappa,
        (sourceClear kind q).last = q.last := by
    intro q
    rw [rightMirrorSourceClear_eq]
    unfold rightMirrorClearInvalid
    cases ht : tokenAt kind q with
    | none =>
        simp only [ht]
    | some t =>
        by_cases hv :
            rightMirrorLocalValid kind q t
        · simp only [ht, if_pos hv]
        · simp only [ht, if_neg hv]
          unfold rightMirrorSetToken
          cases kind <;> rfl

  let lv0 := rightMirrorLiveValue kind l
  let rv0 := rightMirrorLiveValue kind r
  let gl0 :=
    rightMirrorLiveShadow kind l (some z)
  let gr0 :=
    rightMirrorLiveShadow kind r gr

  have hNoRight0 : noId gr := by
    intro u hu hid
    exact hNoRight u hu hid

  have hgr0 : noId gr0 := by
    simpa [gr0]
      using hShadowNoId r gr hNoRight0

  by_cases hgate :
      l.last = false ∧ r.last = false

  · let guard :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      rightMirrorBirthGhost
        hpsi kind step e l.id
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

    let finish :
        Option (TokenData psi) ->
          Option (TokenData psi) ->
          Option (GhostToken n psi) ->
          Option (GhostToken n psi) ->
          GhostMoveResult n psi :=
      fun lv rv gl grx =>
        match lv with
        | some t =>
            let c :=
              decodeOffset psi (tokenCode t)
            if h1 : c = 1 then
              let next :=
                rightMirrorMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2
              let b :=
                rightMirrorBumpTo
                  kind r next gl
              ⟨none, b.live, b.done⟩
            else if h2 : 2 <= c then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                rightMirrorMkToken
                  (encodeOffset psi (c - 1) (by
                    rcases hc with hn | hp
                    · exfalso
                      omega
                    · right
                      omega))
                  t.1.2 t.2
              let b :=
                rightMirrorBumpTo
                  kind r next gl
              ⟨none, b.live, b.done⟩
            else
              match rv with
              | none =>
                  ⟨gl, grx, []⟩
              | some tr =>
                  let cr :=
                    decodeOffset psi (tokenCode tr)
                  if hm1 : cr = -1 then
                    let next :=
                      rightMirrorNegTurnNext
                        hpsi l.id tr
                    let b :=
                      rightMirrorBumpTo
                        kind l next grx
                    ⟨b.live, none, b.done⟩
                  else if hm2 : cr <= -2 then
                    have hc : ValidOffset psi cr :=
                      decodeOffset_valid
                        psi (by omega) (tokenCode tr)
                    let next :=
                      rightMirrorMkToken
                        (encodeOffset psi (cr + 1) (by
                          rcases hc with hn | hp
                          · left
                            omega
                          · exfalso
                            omega))
                        tr.1.2 tr.2
                    let b :=
                      rightMirrorBumpTo
                        kind l next grx
                    ⟨b.live, none, b.done⟩
                  else
                    ⟨gl, grx, []⟩
        | none =>
            match rv with
            | none =>
                ⟨gl, grx, []⟩
            | some tr =>
                let cr :=
                  decodeOffset psi (tokenCode tr)
                if hm1 : cr = -1 then
                  let next :=
                    rightMirrorNegTurnNext
                      hpsi l.id tr
                  let b :=
                    rightMirrorBumpTo
                      kind l next grx
                  ⟨b.live, none, b.done⟩
                else if hm2 : cr <= -2 then
                  have hc : ValidOffset psi cr :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    rightMirrorMkToken
                      (encodeOffset psi (cr + 1) (by
                        rcases hc with hn | hp
                        · left
                          omega
                        · exfalso
                          omega))
                      tr.1.2 tr.2
                  let b :=
                    rightMirrorBumpTo
                      kind l next grx
                  ⟨b.live, none, b.done⟩
                else
                  ⟨gl, grx, []⟩

    have hBirthNoId : noId (some birth) := by
      intro u hu hid
      have hbu : birth = u :=
        Option.some.inj hu
      have hu0 : u = birth := hbu.symm
      subst u
      apply hNotBirth
      simpa [birth, rightMirrorBirthGhost]
        using hid.symm

    have hPrefix :
        (lv2 = some z.value ∧
            gl2 = some z ∧
            rv0 = none ∧
            lv0 = some z.value) ∨
          (noId gl2 ∧ noId gr0) := by
      by_cases hg : guard
      · right
        refine And.intro ?_ hgr0
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
            refine And.intro ?_ hgr0
            have hnone : gl2 = none := by
              by_cases hcol : collide
              · simp [gl2, hcol]
              · simp [gl2, hcol, gl1, hg, hgl]
            rw [hnone]
            exact hNoNone
        | some u =>
            have hshadow :
                rightMirrorLiveShadow
                    kind l (some z) =
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
                refine And.intro ?_ (And.intro ?_ (And.intro rfl hlv))
                · simp [lv2, hcol, hlv1]
                · simp [gl2, hcol, gl1, hg, hgl]
            | some tr =>
                right
                refine And.intro ?_ hgr0
                have hcol : collide := by
                  simp [collide, hlv1, hrv]
                have hnone : gl2 = none := by
                  simp [gl2, hcol]
                rw [hnone]
                exact hNoNone

    have hMoveEq :
        rightMirrorGhostMoveToken
            hpsi kind step e
            l r (some z) gr =
          finish lv2 rv0 gl2 gr0 := by
      unfold rightMirrorGhostMoveToken
      simp only [dif_pos hgate]
      rfl

    have hFinishNoId :
        forall (lv rv : Option (TokenData psi))
          (gl grx : Option (GhostToken n psi)),
          noId gl ->
          noId grx ->
          let q := finish lv rv gl grx
          noId q.left ∧ noId q.right := by
      intro lv rv gl grx hgl hgr
      cases lv with
      | none =>
          cases rv with
          | none =>
              exact And.intro hgl hgr
          | some t =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode t) = -1
              · simp only [finish, dif_pos hm1]
                exact
                  And.intro
                    (hBumpNoId l
                      (rightMirrorNegTurnNext
                        hpsi l.id t)
                      grx hgr)
                    hNoNone
              · by_cases hm2 :
                  decodeOffset psi (tokenCode t) <= -2
                · simp only
                    [finish, dif_neg hm1, dif_pos hm2]
                  exact
                    And.intro
                      (hBumpNoId l _ grx hgr)
                      hNoNone
                · simp only
                    [finish, dif_neg hm1, dif_neg hm2]
                  exact And.intro hgl hgr
      | some t =>
          by_cases h1 :
              decodeOffset psi (tokenCode t) = 1
          · simp only [finish, dif_pos h1]
            exact
              And.intro
                hNoNone
                (hBumpNoId r _ gl hgl)
          · by_cases h2 :
              2 <= decodeOffset psi (tokenCode t)
            · simp only
                [finish, dif_neg h1, dif_pos h2]
              exact
                And.intro
                  hNoNone
                  (hBumpNoId r _ gl hgl)
            · cases rv with
              | none =>
                  simp only
                    [finish, dif_neg h1, dif_neg h2]
                  exact And.intro hgl hgr
              | some tr =>
                  by_cases hm1 :
                      decodeOffset psi
                          (tokenCode tr) = -1
                  · simp only
                      [finish, dif_neg h1, dif_neg h2,
                        dif_pos hm1]
                    exact
                      And.intro
                        (hBumpNoId l
                          (rightMirrorNegTurnNext
                            hpsi l.id tr)
                          grx hgr)
                        hNoNone
                  · by_cases hm2 :
                      decodeOffset psi
                          (tokenCode tr) <= -2
                    · simp only
                        [finish, dif_neg h1, dif_neg h2,
                          dif_neg hm1, dif_pos hm2]
                      exact
                        And.intro
                          (hBumpNoId l _ grx hgr)
                          hNoNone
                    · simp only
                        [finish, dif_neg h1, dif_neg h2,
                          dif_neg hm1, dif_neg hm2]
                      exact And.intro hgl hgr

    have hPhysicalTurn :
        lv0 = some z.value ->
        rv0 = none ->
        decodeOffset psi (tokenCode z.value) = 1 ->
        tokenAt kind
            (moveToken hpsi kind l r).2 =
          some (rightMirrorTurnNext hpsi z.value) := by
      intro hlv hrv hc
      have hlv' :
          rightMirrorLiveValue kind l =
            some z.value := by
        simpa [lv0] using hlv
      have hrv' :
          rightMirrorLiveValue kind r = none := by
        simpa [rv0] using hrv
      rw [← rightMirrorMoveToken_eq hpsi kind l r]
      unfold rightMirrorMoveToken
      simp
        [hClearToken, hClearLast, hSetToken,
          hlv', hrv', hgate.1, hgate.2, hc,
          rightMirrorTurnNext]

    have hPhysicalPositive :
        lv0 = some z.value ->
        rv0 = none ->
        forall
          (h1 :
            decodeOffset psi
                (tokenCode z.value) ≠ 1)
          (h2 :
            2 <= decodeOffset psi
              (tokenCode z.value)),
          tokenAt kind
              (moveToken hpsi kind l r).2 =
            some
              (rightMirrorPositiveNext
                hpsi z.value h2) := by
      intro hlv hrv h1 h2
      have hlv' :
          rightMirrorLiveValue kind l =
            some z.value := by
        simpa [lv0] using hlv
      have hrv' :
          rightMirrorLiveValue kind r = none := by
        simpa [rv0] using hrv
      rw [← rightMirrorMoveToken_eq hpsi kind l r]
      unfold rightMirrorMoveToken
      simp
        [hClearToken, hClearLast, hSetToken,
          hlv', hrv', hgate.1, hgate.2,
          h1, h2, rightMirrorPositiveNext,
          rightMirrorSubOneValid]

    have hPhysicalStay :
        lv0 = some z.value ->
        rv0 = none ->
        decodeOffset psi (tokenCode z.value) ≠ 1 ->
        ¬ 2 <= decodeOffset psi (tokenCode z.value) ->
        tokenAt kind
            (moveToken hpsi kind l r).1 =
          some z.value := by
      intro hlv hrv h1 h2
      have hlv' :
          rightMirrorLiveValue kind l =
            some z.value := by
        simpa [lv0] using hlv
      have hrv' :
          rightMirrorLiveValue kind r = none := by
        simpa [rv0] using hrv
      rw [← rightMirrorMoveToken_eq hpsi kind l r]
      unfold rightMirrorMoveToken
      simp
        [hClearToken, hClearLast, hSetToken,
          hlv', hrv', hgate.1, hgate.2,
          h1, h2]

    intro z'
    rcases hPrefix with hsrc | hno

    · rcases hsrc with
        ⟨hlv2, hgl2, hrv, hlv⟩
      constructor

      · intro hout _
        rw [hMoveEq, hlv2, hgl2, hrv] at hout
        by_cases h1 :
            decodeOffset psi
                (tokenCode z.value) = 1
        · simp only [finish, dif_pos h1] at hout
          cases hout
        · by_cases h2 :
            2 <= decodeOffset psi
              (tokenCode z.value)
          · simp only
              [finish, dif_neg h1, dif_pos h2] at hout
            cases hout
          · have hstay :
                (some z : Option (GhostToken n psi)) =
                  some z' := by
              simpa only
                [finish, dif_neg h1, dif_neg h2]
                using hout
            have hz' : z' = z :=
              (Option.some.inj hstay).symm
            subst z'
            exact
              And.intro rfl
                (hPhysicalStay
                  hlv hrv h1 h2)

      · intro hout hid
        rw [hMoveEq, hlv2, hgl2, hrv] at hout
        by_cases h1 :
            decodeOffset psi
                (tokenCode z.value) = 1
        · have hb :
              (rightMirrorBumpTo
                  kind r
                  (rightMirrorTurnNext
                    hpsi z.value)
                  (some z)).live =
                some z' := by
            simpa only
              [finish, dif_pos h1,
                rightMirrorTurnNext]
              using hout
          have hs :=
            hBumpSome
              r
              (rightMirrorTurnNext
                hpsi z.value)
              z z' hb
          have hphys :=
            hPhysicalTurn hlv hrv h1
          refine And.intro ?_ ?_
          · simpa [hs.1] using hphys
          · rw [hs.1]
            exact
              rightMirrorTurnLiteral
                hpsi ring e z.value h1

        · by_cases h2 :
            2 <= decodeOffset psi
              (tokenCode z.value)
          · have hb :
                (rightMirrorBumpTo
                    kind r
                    (rightMirrorPositiveNext
                      hpsi z.value h2)
                    (some z)).live =
                  some z' := by
              simpa
                [finish, h1, h2,
                  rightMirrorPositiveNext,
                  rightMirrorSubOneValid]
                using hout
            have hs :=
              hBumpSome
                r
                (rightMirrorPositiveNext
                  hpsi z.value h2)
                z z' hb
            have hphys :=
              hPhysicalPositive
                hlv hrv h1 h2
            refine And.intro ?_ ?_
            · simpa [hs.1] using hphys
            · rw [hs.1]
              exact
                rightMirrorPositiveLiteral
                  hpsi ring e z.value h2

          · have hgr :
                gr0 = some z' := by
              simpa only
                [finish, dif_neg h1, dif_neg h2]
                using hout
            exact False.elim (hgr0 z' hgr hid)

    · have hf :=
        hFinishNoId
          lv2 rv0 gl2 gr0 hno.1 hno.2
      dsimp only at hf
      constructor
      · intro hout hid
        rw [hMoveEq] at hout
        exact
          False.elim
            (hf.1 z' hout hid)
      · intro hout hid
        rw [hMoveEq] at hout
        exact
          False.elim
            (hf.2 z' hout hid)

  · have hMoveClosed :
        rightMirrorGhostMoveToken
            hpsi kind step e
            l r (some z) gr =
          ⟨gl0, gr0, []⟩ := by
      unfold rightMirrorGhostMoveToken
      simp only [dif_neg hgate]
      rfl

    intro z'
    constructor

    · intro hout _
      rw [hMoveClosed] at hout
      change gl0 = some z' at hout
      have hshadow :
          rightMirrorLiveShadow
              kind l (some z) =
            some z' := by
        simpa [gl0] using hout
      have hs :=
        hSourceShadow z' hshadow
      have hz' : z' = z := hs.1
      subst z'
      have hlv :
          rightMirrorLiveValue kind l =
            some z.value := hs.2
      have hphys :
          tokenAt kind
              (moveToken hpsi kind l r).1 =
            some z.value := by
        rw [← rightMirrorMoveToken_eq hpsi kind l r]
        unfold rightMirrorMoveToken
        simp only [hClearLast, dif_neg hgate]
        exact
          (hClearToken l).trans hlv
      exact And.intro rfl hphys

    · intro hout hid
      rw [hMoveClosed] at hout
      change gr0 = some z' at hout
      exact False.elim (hgr0 z' hout hid)

private theorem rightMirrorSelectedMirrorRow_local :
    RightMirrorSelectedMirrorRow := by
  classical
  unfold RightMirrorSelectedMirrorRow
  intro n psi kappa hpsi ring step e kind l r gr z
  intro hNoRight hNotBirth
  cases kind with
  | black =>
      exact
        rightMirrorCore
          hpsi ring step e TokenKind.black
          l r gr z hNoRight hNotBirth
  | white =>
      exact
        rightMirrorCore
          hpsi ring step e TokenKind.white
          l r gr z hNoRight hNotBirth

theorem remark2RightSelectedMirrorRowCorrected_proved :
    Remark2RightSelectedMirrorRowCorrected := by
  rw [rightMirrorSelectedMirrorRow_defeq]
  exact rightMirrorSelectedMirrorRow_local

/-- The corrected right owner row with its finite mirror premise discharged
(the upstream `remark2RightOwnerRowCorrected_proved` is conditional on it). -/
theorem remark2RightOwnerRowCorrected_closed :
    Remark2RightOwnerRowCorrected :=
  remark2RightOwnerRowCorrected_proved
    remark2RightSelectedMirrorRowCorrected_proved

/-- Remark 2 right selected row, unconditional. -/
theorem remark2RightSelectedRow_closed :
    Remark2RightSelectedRow :=
  remark2RightSelectedRow_proved
    remark2RightSelectedMirrorRowCorrected_proved

end PPL

#print axioms PPL.remark2RightSelectedMirrorRowCorrected_proved
#print axioms PPL.remark2RightOwnerRowCorrected_closed
#print axioms PPL.remark2RightSelectedRow_closed
