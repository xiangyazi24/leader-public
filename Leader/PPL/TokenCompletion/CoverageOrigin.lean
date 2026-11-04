import Leader.PPL.TokenCompletion.CoverageRows


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false




/-! ## Public-name mirror of the selected-colour ghost row -/


private def originBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)




private def originMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)




private def originLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) <= target ∧
        target <= (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 <= target ∧
        target <= (((psi - 1 : Nat)) : Int))




private instance instDecidableOriginLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (originLocalValid kind q t) := by
  unfold originLocalValid
  infer_instance




private def originLiveShadow
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
          if z.value = t ∧
              originLocalValid kind q t then
            some z
          else
            none




private def originLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if originLocalValid kind q t then
        some t
      else
        none




private def originBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      originMkToken
        (offsetPsiCode psi hpsi)
        (originBitToFin (!idBit))
        (originBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }




private def originBumpTo
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
        if originLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩




private def originNegTurnNext {psi : Nat}
    (hpsi : 2 <= psi) (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    originMkToken
      (offsetPsiCode psi hpsi)
      (originBitToFin (!sourceBit))
      (originBitToFin sourceBit)
  else
    originMkToken
      (offsetPsiCode psi hpsi)
      (originBitToFin sourceBit)
      (0 : Fin 2)




private def originFinishMove
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
          originMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          originBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          originMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          originBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                originNegTurnNext hpsi l.id tr
              let b :=
                originBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr <= -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                originMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                originBumpTo kind l next gr0
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
              originNegTurnNext hpsi l.id tr
            let b :=
              originBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr <= -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              originMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b :=
              originBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩


private def originGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := originLiveValue kind l
  let rv0 := originLiveValue kind r
  let gl0 := originLiveShadow kind l gl
  let gr0 := originLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let birthGuard :=
      l.dist.val = tokenD' psi kind ∧ lv0 = none
    let birth :=
      originBirthGhost hpsi kind step site l.id
    let lv1 :=
      if birthGuard then some birth.value else lv0
    let gl1 :=
      if birthGuard then some birth else gl0
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    originFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩




private def originPrelude
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
    else if r1.dist.val = 0 ∨
        r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)




private def originSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := originPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2




private def originSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k




private def originMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    originSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  originGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))




private theorem originGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      originSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (originMovedPair
          hpsi ring step G e kind).left
        (originMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl




/-! ## Finite ghost-branch classification -/


private def originRightMovedShape {psi : Nat}
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  c = 1 - ((psi : Nat) : Int) ∨
    (0 < c ∧ c < ((psi : Nat) : Int))


private def originLeftMovedShape {psi : Nat}
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  c = ((psi : Nat) : Int) ∨
    (1 - ((psi : Nat) : Int) < c ∧ c < 0)


private def originOldSource
    {n psi : Nat}
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi) : Prop :=
  ∃ z0 : GhostToken n psi,
    g = some z0 ∧ z.lmeta.id = z0.lmeta.id


private def originBirthSource
    {n psi kappa : Nat}
    (kind : TokenKind) (step : Nat) (site : Fin n)
    (l : State psi kappa)
    (z : GhostToken n psi) : Prop :=
  l.dist.val = tokenD' psi kind ∧
    z.lmeta.id = .born kind step ∧
      z.lmeta.birthSite = site


private def originLeftSource
    {n psi kappa : Nat}
    (kind : TokenKind) (step : Nat) (site : Fin n)
    (l : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi) : Prop :=
  originBirthSource kind step site l z ∨
    originOldSource gl z


private theorem originLiveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz : originLiveShadow kind q g = some z) :
    originOldSource g z := by
  cases g with
  | none =>
      simp [originLiveShadow] at hz
  | some z0 =>
      refine ⟨z0, rfl, ?_⟩
      cases ht : tokenAt kind q with
      | none =>
          simp [originLiveShadow, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧ originLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [originLiveShadow, ht, hv] using hz
            subst z
            rfl
          · simp [originLiveShadow, ht, hv] at hz


private theorem originBump_live_spec
    {n psi kappa : Nat}
    (kind : TokenKind) (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      (originBumpTo kind qDest newValue g).live =
        some z) :
    originLocalValid kind qDest z.value ∧
      z.value = newValue ∧
        ∃ z0 : GhostToken n psi,
          g = some z0 ∧
            z.lmeta.id = z0.lmeta.id ∧
              z.lmeta.birthSite = z0.lmeta.birthSite := by
  cases g with
  | none =>
      simp [originBumpTo] at hz
  | some z0 =>
      by_cases hv :
          originLocalValid kind qDest newValue
      · simp only
          [originBumpTo, if_pos hv,
            Option.some.injEq] at hz
        subst z
        exact ⟨hv, rfl, z0, rfl, rfl, rfl⟩
      · simp [originBumpTo, hv] at hz


private theorem originOldSource_transfer
    {n psi : Nat}
    {g : Option (GhostToken n psi)}
    {z0 z : GhostToken n psi}
    (hid : z.lmeta.id = z0.lmeta.id)
    (hs : originOldSource g z0) :
    originOldSource g z := by
  rcases hs with ⟨u, hu, hi⟩
  exact ⟨u, hu, hid.trans hi⟩


private theorem originLeftSource_transfer
    {n psi kappa : Nat}
    {kind : TokenKind} {step : Nat} {site : Fin n}
    {l : State psi kappa}
    {gl : Option (GhostToken n psi)}
    {z0 z : GhostToken n psi}
    (hid : z.lmeta.id = z0.lmeta.id)
    (hsite : z.lmeta.birthSite = z0.lmeta.birthSite)
    (hs : originLeftSource kind step site l gl z0) :
    originLeftSource kind step site l gl z := by
  rcases hs with hb | ho
  · left
    exact ⟨hb.1, hid.trans hb.2.1, hsite.trans hb.2.2⟩
  · right
    exact originOldSource_transfer hid ho


private structure OriginPrefix
    (n psi : Nat) where
  lv2 : Option (TokenData psi)
  rv0 : Option (TokenData psi)
  gl2 : Option (GhostToken n psi)
  gr0 : Option (GhostToken n psi)


private def originPrefix
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    OriginPrefix n psi :=
  let lv0 := originLiveValue kind l
  let rv0 := originLiveValue kind r
  let gl0 := originLiveShadow kind l gl
  let gr0 := originLiveShadow kind r gr
  let birthGuard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    originBirthGhost hpsi kind step site l.id
  let lv1 :=
    if birthGuard then some birth.value else lv0
  let gl1 :=
    if birthGuard then some birth else gl0
  let collide :=
    lv1 ≠ none ∧ rv0 ≠ none
  { lv2 := if collide then none else lv1
    rv0 := rv0
    gl2 := if collide then none else gl1
    gr0 := gr0 }


private theorem originGhostMoveToken_eq_finish
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hlast : l.last = false ∧ r.last = false) :
    originGhostMoveToken hpsi kind step site l r gl gr =
      originFinishMove hpsi kind l r
        (originPrefix hpsi kind step site l r gl gr).lv2
        (originPrefix hpsi kind step site l r gl gr).rv0
        (originPrefix hpsi kind step site l r gl gr).gl2
        (originPrefix hpsi kind step site l r gl gr).gr0 := by
  unfold originGhostMoveToken originPrefix
  rw [dif_pos hlast]


private theorem originGhostMoveToken_eq_shadow
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hlast : ¬ (l.last = false ∧ r.last = false)) :
    originGhostMoveToken hpsi kind step site l r gl gr =
      ⟨originLiveShadow kind l gl,
        originLiveShadow kind r gr, []⟩ := by
  unfold originGhostMoveToken
  rw [dif_neg hlast]


private theorem originPrefix_sources
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    (∀ z : GhostToken n psi,
      (originPrefix hpsi kind step site l r gl gr).gr0 =
          some z ->
        originOldSource gr z) ∧
    (∀ z : GhostToken n psi,
      (originPrefix hpsi kind step site l r gl gr).gl2 =
          some z ->
        originLeftSource kind step site l gl z) := by
  constructor
  · intro z hz
    change originLiveShadow kind r gr = some z at hz
    exact originLiveShadow_source kind r gr z hz
  · intro z hz
    let lv0 := originLiveValue kind l
    let rv0 := originLiveValue kind r
    let birthGuard :=
      l.dist.val = tokenD' psi kind ∧ lv0 = none
    let birth :=
      originBirthGhost hpsi kind step site l.id
    let lv1 :=
      if birthGuard then some birth.value else lv0
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    change
      (if collide then none
       else if birthGuard then some birth
       else originLiveShadow kind l gl) = some z at hz
    by_cases hcol : collide
    · rw [if_pos hcol] at hz
      cases hz
    · rw [if_neg hcol] at hz
      by_cases hb : birthGuard
      · rw [if_pos hb] at hz
        have heq : birth = z := Option.some.inj hz
        subst z
        exact Or.inl ⟨hb.1, rfl, rfl⟩
      · rw [if_neg hb] at hz
        exact
          Or.inr
            (originLiveShadow_source
              kind l gl z hz)


private theorem originFinishMove_right_split
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (hleft :
      ∀ z : GhostToken n psi, gl2 = some z ->
        originLeftSource kind step site l gl z)
    (hright :
      ∀ z : GhostToken n psi, gr0 = some z ->
        originOldSource gr z)
    (z : GhostToken n psi)
    (hz :
      (originFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0).right =
          some z) :
    originOldSource gr z ∨
      (originLocalValid kind r z.value ∧
        originRightMovedShape z.value ∧
          originLeftSource kind step site l gl z) := by
  cases lv2 with
  | none =>
      cases rv0 with
      | none =>
          simp only [originFinishMove] at hz
          exact Or.inl (hright z hz)
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [originFinishMove, dif_pos hm1] at hz
            cases hz
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [originFinishMove,
                  dif_neg hm1, dif_pos hm2] at hz
              cases hz
            · simp only
                [originFinishMove,
                  dif_neg hm1, dif_neg hm2] at hz
              exact Or.inl (hright z hz)
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only [originFinishMove, dif_pos h1] at hz
        let next :=
          originMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        obtain ⟨hvalid, hval, z0, hz0, hid, hsite⟩ :=
          originBump_live_spec
            kind r next gl2 z hz
        have hsrc :=
          originLeftSource_transfer
            hid hsite (hleft z0 hz0)
        have hshape : originRightMovedShape next := by
          unfold originRightMovedShape
          dsimp [next, originMkToken, tokenCode]
          left
          exact decodeOffset_negPsiPlusOne psi hpsi
        exact
          Or.inr
            ⟨hvalid,
              by simpa only [hval] using hshape,
              hsrc⟩
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [originFinishMove,
              dif_neg h1, dif_pos h2] at hz
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            originMkToken
              (encodeOffset psi
                (decodeOffset psi (tokenCode t) - 1)
                (by
                  rcases hc with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
              t.1.2 t.2
          obtain ⟨hvalid, hval, z0, hz0, hid, hsite⟩ :=
            originBump_live_spec
              kind r next gl2 z hz
          have hsrc :=
            originLeftSource_transfer
              hid hsite (hleft z0 hz0)
          have hnext :
              decodeOffset psi (tokenCode next) =
                decodeOffset psi (tokenCode t) - 1 := by
            dsimp [next, originMkToken, tokenCode]
            exact decode_encode _ _ _
          have hshape : originRightMovedShape next := by
            unfold originRightMovedShape
            dsimp only
            rw [hnext]
            right
            rcases hc with hn | hp
            · omega
            · omega
          exact
            Or.inr
              ⟨hvalid,
                by simpa only [hval] using hshape,
                hsrc⟩
        · cases rv0 with
          | none =>
              simp only
                [originFinishMove,
                  dif_neg h1, dif_neg h2] at hz
              exact Or.inl (hright z hz)
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [originFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1] at hz
                cases hz
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) <= -2
                · simp only
                    [originFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2] at hz
                  cases hz
                · simp only
                    [originFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2] at hz
                  exact Or.inl (hright z hz)


private theorem originFinishMove_left_split
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (hleft :
      ∀ z : GhostToken n psi, gl2 = some z ->
        originLeftSource kind step site l gl z)
    (hright :
      ∀ z : GhostToken n psi, gr0 = some z ->
        originOldSource gr z)
    (z : GhostToken n psi)
    (hz :
      (originFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0).left =
          some z) :
    originLeftSource kind step site l gl z ∨
      (originLocalValid kind l z.value ∧
        originLeftMovedShape z.value ∧
          originOldSource gr z) := by
  cases lv2 with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only [originFinishMove, dif_pos h1] at hz
        cases hz
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [originFinishMove,
              dif_neg h1, dif_pos h2] at hz
          cases hz
        · cases rv0 with
          | none =>
              simp only
                [originFinishMove,
                  dif_neg h1, dif_neg h2] at hz
              exact Or.inl (hleft z hz)
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [originFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1] at hz
                let next :=
                  originNegTurnNext hpsi l.id tr
                obtain ⟨hvalid, hval, z0, hz0, hid, _hsite⟩ :=
                  originBump_live_spec
                    kind l next gr0 z hz
                have hsrc :=
                  originOldSource_transfer
                    hid (hright z0 hz0)
                have hshape : originLeftMovedShape next := by
                  unfold originLeftMovedShape
                  unfold next originNegTurnNext
                  by_cases hcarry : tr.2 = (1 : Fin 2)
                  · rw [if_pos hcarry]
                    dsimp [originMkToken, tokenCode]
                    left
                    exact decodeOffset_psi psi hpsi
                  · rw [if_neg hcarry]
                    dsimp [originMkToken, tokenCode]
                    left
                    exact decodeOffset_psi psi hpsi
                exact
                  Or.inr
                    ⟨hvalid,
                      by simpa only [hval] using hshape,
                      hsrc⟩
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) <= -2
                · simp only
                    [originFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2] at hz
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    originMkToken
                      (encodeOffset psi
                        (decodeOffset psi (tokenCode tr) + 1)
                        (by
                          rcases hc with hn | hp
                          · left
                            omega
                          · exfalso
                            omega))
                      tr.1.2 tr.2
                  obtain ⟨hvalid, hval, z0, hz0, hid, _hsite⟩ :=
                    originBump_live_spec
                      kind l next gr0 z hz
                  have hsrc :=
                    originOldSource_transfer
                      hid (hright z0 hz0)
                  have hnext :
                      decodeOffset psi (tokenCode next) =
                        decodeOffset psi (tokenCode tr) + 1 := by
                    dsimp [next, originMkToken, tokenCode]
                    exact decode_encode _ _ _
                  have hshape : originLeftMovedShape next := by
                    unfold originLeftMovedShape
                    dsimp only
                    rw [hnext]
                    right
                    rcases hc with hn | hp
                    · omega
                    · omega
                  exact
                    Or.inr
                      ⟨hvalid,
                        by simpa only [hval] using hshape,
                        hsrc⟩
                · simp only
                    [originFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2] at hz
                  exact Or.inl (hleft z hz)
  | none =>
      cases rv0 with
      | none =>
          simp only [originFinishMove] at hz
          exact Or.inl (hleft z hz)
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [originFinishMove, dif_pos hm1] at hz
            let next :=
              originNegTurnNext hpsi l.id tr
            obtain ⟨hvalid, hval, z0, hz0, hid, _hsite⟩ :=
              originBump_live_spec
                kind l next gr0 z hz
            have hsrc :=
              originOldSource_transfer
                hid (hright z0 hz0)
            have hshape : originLeftMovedShape next := by
              unfold originLeftMovedShape
              unfold next originNegTurnNext
              by_cases hcarry : tr.2 = (1 : Fin 2)
              · rw [if_pos hcarry]
                dsimp [originMkToken, tokenCode]
                left
                exact decodeOffset_psi psi hpsi
              · rw [if_neg hcarry]
                dsimp [originMkToken, tokenCode]
                left
                exact decodeOffset_psi psi hpsi
            exact
              Or.inr
                ⟨hvalid,
                  by simpa only [hval] using hshape,
                  hsrc⟩
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [originFinishMove,
                  dif_neg hm1, dif_pos hm2] at hz
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                originMkToken
                  (encodeOffset psi
                    (decodeOffset psi (tokenCode tr) + 1)
                    (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                  tr.1.2 tr.2
              obtain ⟨hvalid, hval, z0, hz0, hid, _hsite⟩ :=
                originBump_live_spec
                  kind l next gr0 z hz
              have hsrc :=
                originOldSource_transfer
                  hid (hright z0 hz0)
              have hnext :
                  decodeOffset psi (tokenCode next) =
                    decodeOffset psi (tokenCode tr) + 1 := by
                dsimp [next, originMkToken, tokenCode]
                exact decode_encode _ _ _
              have hshape : originLeftMovedShape next := by
                unfold originLeftMovedShape
                dsimp only
                rw [hnext]
                right
                rcases hc with hn | hp
                · omega
                · omega
              exact
                Or.inr
                  ⟨hvalid,
                    by simpa only [hval] using hshape,
                    hsrc⟩
            · simp only
                [originFinishMove,
                  dif_neg hm1, dif_neg hm2] at hz
              exact Or.inl (hleft z hz)


private theorem originResponderGhostBranchSplit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      (originGhostMoveToken
        hpsi kind step site l r gl gr).right =
        some z) :
    (∃ z0 : GhostToken n psi,
      gr = some z0 ∧ z.lmeta.id = z0.lmeta.id) ∨
      (originLocalValid kind r z.value ∧
        originRightMovedShape z.value ∧
          ((l.dist.val = tokenD' psi kind ∧
              z.lmeta.id = .born kind step ∧
                z.lmeta.birthSite = site) ∨
            ∃ z0 : GhostToken n psi,
              gl = some z0 ∧
                z.lmeta.id = z0.lmeta.id)) := by
  have hres :
      originOldSource gr z ∨
        (originLocalValid kind r z.value ∧
          originRightMovedShape z.value ∧
            originLeftSource kind step site l gl z) := by
    by_cases hlast : l.last = false ∧ r.last = false
    · rw [originGhostMoveToken_eq_finish
        hpsi kind step site l r gl gr hlast] at hz
      have hs :=
        originPrefix_sources
          hpsi kind step site l r gl gr
      exact
        originFinishMove_right_split
          hpsi kind step site l r gl gr
          (originPrefix hpsi kind step site l r gl gr).lv2
          (originPrefix hpsi kind step site l r gl gr).rv0
          (originPrefix hpsi kind step site l r gl gr).gl2
          (originPrefix hpsi kind step site l r gl gr).gr0
          hs.2 hs.1 z hz
    · rw [originGhostMoveToken_eq_shadow
        hpsi kind step site l r gl gr hlast] at hz
      exact
        Or.inl
          (originLiveShadow_source kind r gr z hz)
  simpa only
    [originOldSource, originLeftSource,
      originBirthSource] using hres


private theorem originInitiatorGhostBranchSplit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      (originGhostMoveToken
        hpsi kind step site l r gl gr).left =
        some z) :
    (l.dist.val = tokenD' psi kind ∧
      z.lmeta.id = .born kind step ∧
        z.lmeta.birthSite = site) ∨
      (∃ z0 : GhostToken n psi,
        gl = some z0 ∧
          z.lmeta.id = z0.lmeta.id) ∨
        (originLocalValid kind l z.value ∧
          originLeftMovedShape z.value ∧
            ∃ z0 : GhostToken n psi,
              gr = some z0 ∧
                z.lmeta.id = z0.lmeta.id) := by
  have hres :
      originLeftSource kind step site l gl z ∨
        (originLocalValid kind l z.value ∧
          originLeftMovedShape z.value ∧
            originOldSource gr z) := by
    by_cases hlast : l.last = false ∧ r.last = false
    · rw [originGhostMoveToken_eq_finish
        hpsi kind step site l r gl gr hlast] at hz
      have hs :=
        originPrefix_sources
          hpsi kind step site l r gl gr
      exact
        originFinishMove_left_split
          hpsi kind step site l r gl gr
          (originPrefix hpsi kind step site l r gl gr).lv2
          (originPrefix hpsi kind step site l r gl gr).rv0
          (originPrefix hpsi kind step site l r gl gr).gl2
          (originPrefix hpsi kind step site l r gl gr).gr0
          hs.2 hs.1 z hz
    · rw [originGhostMoveToken_eq_shadow
        hpsi kind step site l r gl gr hlast] at hz
      exact
        Or.inl
          (Or.inr
            (originLiveShadow_source kind l gl z hz))
  unfold originLeftSource originBirthSource originOldSource at hres
  rcases hres with hsource | hmoved
  · rcases hsource with hbirth | hold
    · exact Or.inl hbirth
    · exact Or.inr (Or.inl hold)
  · exact Or.inr (Or.inr hmoved)




/-! ## Physical selected-input distance frame -/


private theorem originMoveTokenDist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := moveToken hpsi kind l r
    q.1.dist = l.dist ∧ q.2.dist = r.dist := by
  dsimp only
  have hi :=
    moveToken_initiator_fields
      hpsi kind l r
  rcases
      moveToken_responder_fields
        hpsi kind l r with hr | hr
  · cases kind <;>
      simp_all
        [eraseKindToken,
          eraseKindTokenId]
  · cases kind <;>
      simp_all
        [eraseKindToken,
          eraseKindTokenId,
          birthFields]




private theorem originElimDist
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let q := eliminateLeaders l r
    q.1.dist = l.dist ∧ q.2.dist = r.dist := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    And.intro
      (congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hl)
      (congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hr)




private theorem originPplSelectedDist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := originSelectedInput hpsi kind l r
    (ppl hpsi l r).1.dist = p.1.dist ∧
      (ppl hpsi l r).2.dist = p.2.dist := by
  cases kind with
  | black =>
      let p := originPrelude hpsi l r
      let b :=
        moveToken hpsi TokenKind.black
          p.1 p.2
      let w :=
        moveToken hpsi TokenKind.white
          b.1 b.2
      have hb :=
        originMoveTokenDist
          hpsi TokenKind.black p.1 p.2
      have hw :=
        originMoveTokenDist
          hpsi TokenKind.white b.1 b.2
      have he :=
        originElimDist w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          originSelectedInput
              hpsi TokenKind.black l r =
            p := by
        rfl
      dsimp only at hb hw he
      rw [hfull, hselected]
      exact
        And.intro
          (he.1.trans (hw.1.trans hb.1))
          (he.2.trans (hw.2.trans hb.2))
  | white =>
      let p := originPrelude hpsi l r
      let b :=
        moveToken hpsi TokenKind.black
          p.1 p.2
      let w :=
        moveToken hpsi TokenKind.white
          b.1 b.2
      have hw :=
        originMoveTokenDist
          hpsi TokenKind.white b.1 b.2
      have he :=
        originElimDist w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          originSelectedInput
              hpsi TokenKind.white l r =
            b := by
        rfl
      dsimp only at hw he
      rw [hfull, hselected]
      exact
        And.intro
          (he.1.trans hw.1)
          (he.2.trans hw.2)




private theorem originStepSelectedDist
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      originSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    ((ghostStep hpsi ring step G e).phys e).dist =
        p.1.dist ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        p.2.dist := by
  dsimp only
  have hp :=
    originPplSelectedDist
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  dsimp only at hp
  have hl :
      (ghostStep hpsi ring step G e).phys e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1
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
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    And.intro
      ((congrArg
        (fun q : State psi kappa => q.dist) hl).trans hp.1)
      ((congrArg
        (fun q : State psi kappa => q.dist) hr).trans hp.2)




/-! ## Window geometry -/


private theorem originCdTwoLe
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 <= n := by
  by_cases hn2 : 2 <= n
  · exact hn2
  · have hn1 : n = 1 := by
      have hn := ring.hn
      omega
    subst n
    let x0 : Fin (2 * psi) :=
      ⟨0, by omega⟩
    let x1 : Fin (2 * psi) :=
      ⟨1, by omega⟩
    have h0 := hCd x0
    have h1 := hCd x1
    dsimp only at h0 h1
    have hs :
        shiftRight ring k x0.val =
          shiftRight ring k x1.val := by
      exact Subsingleton.elim _ _
    have hd :=
      congrArg
        (fun i : Fin 1 => (C i).dist.val) hs
    rw [h0.1, h1.1] at hd
    dsimp [x0, x1] at hd
    cases kind with
    | black =>
        simp only [tokenD', Nat.add_zero,
          Nat.zero_mod] at hd
        rw [Nat.mod_eq_of_lt
          (by omega : 1 < 2 * psi)] at hd
        omega
    | white =>
        simp only [tokenD', Nat.zero_add] at hd
        rw [Nat.mod_eq_of_lt
          (by omega : psi < 2 * psi)] at hd
        rw [Nat.mod_eq_of_lt
          (by omega : 1 + psi < 2 * psi)] at hd
        omega




private theorem originRightNeighborNe
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 <= n)
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




private theorem originLeftNeighborRightNeighbor
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




private theorem originRightNeighborShiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) (d : Nat) :
    ring.rightNeighbor (shiftRight ring k d) =
      shiftRight ring k (d + 1) := by
  apply Fin.ext
  simp only
    [DirectedRing.rightNeighbor, shiftRight]
  rw [Nat.mod_add_mod, Nat.add_assoc]




private theorem originShiftRightZero
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) :
    shiftRight ring k 0 = k := by
  apply Fin.ext
  simp only [shiftRight]
  rw [Nat.add_zero, Nat.mod_eq_of_lt k.isLt]




private theorem originTokenDLt
    {psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind) :
    tokenD' psi kind < 2 * psi := by
  cases kind <;>
    simp only [tokenD'] <;>
    omega




private theorem originCanonicalBase
    {psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (x : Fin (2 * psi))
    (hcanon :
      (x.val + tokenD' psi kind) %
          (2 * psi) =
        tokenD' psi kind) :
    x.val = 0 := by
  cases kind with
  | black =>
      simp only [tokenD'] at hcanon
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt x.isLt] at hcanon
      exact hcanon
  | white =>
      simp only [tokenD'] at hcanon
      by_cases hlt :
          x.val + psi < 2 * psi
      · rw [Nat.mod_eq_of_lt hlt] at hcanon
        omega
      · have hge :
          2 * psi <= x.val + psi := by
          omega
        have hsub :
            x.val + psi - 2 * psi <
              2 * psi := by
          omega
        rw [Nat.mod_eq_sub_mod hge,
          Nat.mod_eq_of_lt hsub] at hcanon
        omega




/-! ## Boundary validity calculations -/


private theorem originNegTurnMod
    (psi : Nat) (hpsi : 2 <= psi) :
    (1 - ((psi : Nat) : Int)) %
        (((2 * psi : Nat)) : Int) =
      (((psi + 1 : Nat)) : Int) := by
  cases psi with
  | zero =>
      omega
  | succ p =>
      cases p with
      | zero =>
          omega
      | succ a =>
          have hneg :
              1 -
                  (((Nat.succ
                    (Nat.succ a) : Nat)) : Int) =
                Int.negSucc a := by
            omega
          rw [hneg]
          change
            Int.subNatNat
                (2 * Nat.succ (Nat.succ a))
                ((a %
                  (2 * Nat.succ
                    (Nat.succ a))).succ) =
              (((Nat.succ (Nat.succ a) + 1 :
                Nat)) : Int)
          rw [Nat.mod_eq_of_lt
            (by omega :
              a <
                2 * Nat.succ (Nat.succ a))]
          rw [Int.subNatNat_of_sub_eq_zero
            (by omega)]
          omega




private theorem originFirstRightTargetTurn
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hc :
      decodeOffset psi (tokenCode t) =
        1 - ((psi : Nat) : Int)) :
    tokenTargetCoordinate kind q t =
      (((psi + 1 : Nat)) : Int) := by
  cases kind with
  | black =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist, hc]
      simpa using originNegTurnMod psi hpsi
  | white =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist, hc]
      have hsum :
          ((psi : Nat) : Int) +
                (1 - ((psi : Nat) : Int)) +
                ((psi : Nat) : Int) =
            (((psi + 1 : Nat)) : Int) := by
        omega
      rw [hsum]
      change
        (((psi + 1) % (2 * psi) : Nat) : Int) =
          (((psi + 1 : Nat)) : Int)
      rw [Nat.mod_eq_of_lt (by omega)]




private theorem originFirstRightTargetPositive
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hpos :
      0 < decodeOffset psi (tokenCode t))
    (hlt :
      decodeOffset psi (tokenCode t) <
        ((psi : Nat) : Int)) :
    tokenTargetCoordinate kind q t =
      decodeOffset psi (tokenCode t) := by
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hpos hlt
      cases kind with
      | black =>
          simp only [tokenD'] at hdist
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hdist, hc]
          simp only [Int.ofNat_eq_coe] at *
          rw [Int.natCast_zero, Int.zero_add, Int.add_zero,
            Int.emod_eq_of_lt (by omega) (by omega)]
      | white =>
          simp only [tokenD'] at hdist
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hdist, hc]
          simp only [Int.ofNat_eq_coe] at *
          have hsum :
              ((psi : Nat) : Int) + ((m : Nat) : Int) +
                    ((psi : Nat) : Int) =
                ((m : Nat) : Int) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right,
            Int.emod_eq_of_lt (by omega) (by omega)]
  | negSucc m =>
      rw [hc] at hpos
      omega




private theorem originRightMovedNotFirst
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hlocal : originLocalValid kind q t)
    (hshape : originRightMovedShape t) :
    False := by
  unfold originRightMovedShape at hshape
  dsimp only at hshape
  unfold originLocalValid at hlocal
  dsimp only at hlocal
  rcases hshape with hturn | hpos
  · have ht :=
      originFirstRightTargetTurn
        hpsi kind q t hdist hturn
    rw [hturn, ht] at hlocal
    rcases hlocal with hp | hn <;>
      omega
  · have ht :=
      originFirstRightTargetPositive
        hpsi kind q t hdist
        hpos.1 hpos.2
    rw [ht] at hlocal
    rcases hlocal with hp | hn <;>
      omega




private theorem originThreePsiMinusOneMod
    {psi : Nat}
    (hpsi : 2 <= psi) :
    (3 * psi - 1) % (2 * psi) =
      psi - 1 := by
  have hge :
      2 * psi <= 3 * psi - 1 := by
    omega
  rw [Nat.mod_eq_sub_mod hge]
  have heq :
      3 * psi - 1 - 2 * psi =
        psi - 1 := by
    omega
  rw [heq]
  rw [Nat.mod_eq_of_lt (by omega)]




private theorem originLastDistPlusD
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
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
          2 * psi <= 2 * psi - 1 + psi := by
        omega
      have hlt :
          2 * psi - 1 + psi - 2 * psi <
            2 * psi := by
        omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt hlt] at hdist
      omega




private theorem originLastLeftTargetTurn
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hc :
      decodeOffset psi (tokenCode t) =
        ((psi : Nat) : Int)) :
    tokenTargetCoordinate kind q t =
      (((psi - 1 : Nat)) : Int) := by
  have hsum :=
    originLastDistPlusD
      hpsi kind q hdist
  have hsumInt :
      (((q.dist.val + tokenD' psi kind :
        Nat)) : Int) =
        (((2 * psi - 1 : Nat)) : Int) :=
    congrArg (fun a : Nat => (a : Int)) hsum
  have hnum :
      ((q.dist.val : Nat) : Int) +
            ((psi : Nat) : Int) +
            ((tokenD' psi kind : Nat) : Int) =
        (((3 * psi - 1 : Nat)) : Int) := by
    simp only [Int.natCast_add] at hsumInt
    omega
  unfold tokenTargetCoordinate
  rw [hc, hnum]
  change
    ((((3 * psi - 1) % (2 * psi) :
      Nat)) : Int) =
      (((psi - 1 : Nat)) : Int)
  rw [originThreePsiMinusOneMod hpsi]




private theorem originLastLeftTargetNegative
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hlow :
      1 - ((psi : Nat) : Int) <
        decodeOffset psi (tokenCode t))
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) <
      tokenTargetCoordinate kind q t := by
  have hsum :=
    originLastDistPlusD
      hpsi kind q hdist
  have hsumInt :
      (((q.dist.val + tokenD' psi kind :
        Nat)) : Int) =
        (((2 * psi - 1 : Nat)) : Int) :=
    congrArg (fun a : Nat => (a : Int)) hsum
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hneg
      simp only [Int.ofNat_eq_coe] at *
      omega
  | negSucc m =>
      rw [hc] at hlow hneg
      have hm : m + 2 < psi := by
        omega
      let s : Nat := 2 * psi - m - 2
      have hspsi : psi < s := by
        dsimp [s]
        omega
      have hslt : s < 2 * psi := by
        dsimp [s]
        omega
      have hcInt :
          Int.negSucc m =
            -(((m + 1 : Nat)) : Int) := by
        omega
      have hnum :
          ((q.dist.val : Nat) : Int) +
                decodeOffset psi (tokenCode t) +
                ((tokenD' psi kind : Nat) : Int) =
            ((s : Nat) : Int) := by
        rw [hc, hcInt]
        simp only [Int.natCast_add] at hsumInt
        dsimp [s]
        omega
      unfold tokenTargetCoordinate
      rw [hnum]
      change
        (((s % (2 * psi) : Nat)) : Int) >
          ((psi : Nat) : Int)
      rw [Nat.mod_eq_of_lt hslt]
      exact_mod_cast hspsi




private theorem originLeftMovedNotLast
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hlocal : originLocalValid kind q t)
    (hshape : originLeftMovedShape t) :
    False := by
  unfold originLeftMovedShape at hshape
  dsimp only at hshape
  unfold originLocalValid at hlocal
  dsimp only at hlocal
  rcases hshape with hturn | hneg
  · have ht :=
      originLastLeftTargetTurn
        hpsi kind q t hdist hturn
    rw [hturn, ht] at hlocal
    rcases hlocal with hp | hn <;>
      omega
  · have ht :=
      originLastLeftTargetNegative
        hpsi kind q t hdist
        hneg.1 hneg.2
    rcases hlocal with hp | hn <;>
      omega




/-! ## Conclusion and branch lemmas -/


private def originConclusion
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (z : GhostToken n psi) : Prop :=
  FreshAt kind k z.lmeta ∨
    ∃ j z0,
      Lemma4InWindow ring k psi j ∧
        ghostTokenAt kind G j = some z0 ∧
          z.lmeta.id = z0.lmeta.id




private theorem originFreshAtFromGuard
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (i : Fin n)
    (q : State psi kappa)
    (z : GhostToken n psi)
    (step : Nat)
    (hCd : Cd ring k kind C)
    (hwin : Lemma4InWindow ring k psi i)
    (hdist : (C i).dist = q.dist)
    (hguard :
      q.dist.val = tokenD' psi kind)
    (hid :
      z.lmeta.id = .born kind step)
    (hsite :
      z.lmeta.birthSite = i) :
    FreshAt kind k z.lmeta := by
  rcases hwin with ⟨x, hx⟩
  have hrow := hCd x
  dsimp only at hrow
  have hcanon :
      (x.val + tokenD' psi kind) %
          (2 * psi) =
        tokenD' psi kind := by
    calc
      (x.val + tokenD' psi kind) %
            (2 * psi) =
          (C i).dist.val := by
            rw [hx]
            exact hrow.1.symm
      _ = q.dist.val :=
        congrArg Fin.val hdist
      _ = tokenD' psi kind := hguard
  have hx0 :=
    originCanonicalBase hpsi kind x hcanon
  have hik : i = k := by
    calc
      i = shiftRight ring k x.val := hx
      _ = shiftRight ring k 0 := by rw [hx0]
      _ = k := originShiftRightZero ring k
  exact
    ⟨step, hid, hsite.trans hik⟩




/-- Responder branch 1: a live-shadow stay. -/
private theorem originResponderStayBranch
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (hsource :
      ∃ z0,
        ghostTokenAt kind G
            (ring.rightNeighbor e) = some z0 ∧
          z.lmeta.id = z0.lmeta.id) :
    originConclusion ring k kind G z := by
  rcases hsource with ⟨z0, hz0, hid⟩
  exact
    Or.inr
      ⟨ring.rightNeighbor e, z0,
        hwin, hz0, hid⟩




/-- Responder branch 2: a positive-direction bump from the initiator. -/
private theorem originResponderBumpBranch
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (Cpost : Config n psi kappa)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (p : State psi kappa × State psi kappa)
    (z : GhostToken n psi)
    (step : Nat)
    (hCdPost : Cd ring k kind Cpost)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (hdist :
      (Cpost e).dist = p.1.dist ∧
        (Cpost (ring.rightNeighbor e)).dist =
          p.2.dist)
    (hlocal :
      originLocalValid kind p.2 z.value)
    (hshape :
      originRightMovedShape z.value)
    (hsource :
      (p.1.dist.val = tokenD' psi kind ∧
        z.lmeta.id = .born kind step ∧
          z.lmeta.birthSite = e) ∨
        ∃ z0,
          ghostTokenAt kind G e = some z0 ∧
            z.lmeta.id = z0.lmeta.id) :
    originConclusion ring k kind G z := by
  rcases hwin with ⟨x, hx⟩
  have hwinE :
      Lemma4InWindow ring k psi e := by
    by_cases hx0 : x.val = 0
    · have hrow := hCdPost x
      dsimp only at hrow
      have hpost :
          (Cpost (ring.rightNeighbor e)).dist.val =
            tokenD' psi kind := by
        calc
          (Cpost (ring.rightNeighbor e)).dist.val =
              (x.val + tokenD' psi kind) %
                (2 * psi) := by
            rw [hx]
            exact hrow.1
          _ = tokenD' psi kind := by
            rw [hx0, Nat.zero_add,
              Nat.mod_eq_of_lt
                (originTokenDLt hpsi kind)]
      have hpdist :
          p.2.dist.val = tokenD' psi kind := by
        exact
          (congrArg Fin.val hdist.2).symm.trans
            hpost
      exact
        False.elim
          (originRightMovedNotFirst
            hpsi kind p.2 z.value
            hpdist hlocal hshape)
    · let y : Fin (2 * psi) :=
        ⟨x.val - 1, by omega⟩
      have hstep :
          ring.rightNeighbor
              (shiftRight ring k y.val) =
            shiftRight ring k x.val := by
        calc
          ring.rightNeighbor
                (shiftRight ring k y.val) =
              shiftRight ring k (y.val + 1) :=
            originRightNeighborShiftRight
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
      rw [originLeftNeighborRightNeighbor,
        originLeftNeighborRightNeighbor] at he
      exact ⟨y, he⟩
  rcases hsource with hfresh | hold
  · exact
      Or.inl
        (originFreshAtFromGuard
          hpsi ring k kind Cpost
          e p.1 z step
          hCdPost hwinE hdist.1
          hfresh.1 hfresh.2.1 hfresh.2.2)
  · rcases hold with ⟨z0, hz0, hid⟩
    exact
      Or.inr
        ⟨e, z0, hwinE, hz0, hid⟩




/-- Initiator branch 1: a same-step birth at the selected source. -/
private theorem originInitiatorBirthBranch
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (Cpost : Config n psi kappa)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (p : State psi kappa × State psi kappa)
    (z : GhostToken n psi)
    (step : Nat)
    (hCdPost : Cd ring k kind Cpost)
    (hwin : Lemma4InWindow ring k psi e)
    (hdist :
      (Cpost e).dist = p.1.dist)
    (hfresh :
      p.1.dist.val = tokenD' psi kind ∧
        z.lmeta.id = .born kind step ∧
          z.lmeta.birthSite = e) :
    originConclusion ring k kind G z := by
  exact
    Or.inl
      (originFreshAtFromGuard
        hpsi ring k kind Cpost
        e p.1 z step
        hCdPost hwin hdist
        hfresh.1 hfresh.2.1 hfresh.2.2)




/-- Initiator branch 2: a live-shadow stay. -/
private theorem originInitiatorStayBranch
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hwin : Lemma4InWindow ring k psi e)
    (hsource :
      ∃ z0,
        ghostTokenAt kind G e = some z0 ∧
          z.lmeta.id = z0.lmeta.id) :
    originConclusion ring k kind G z := by
  rcases hsource with ⟨z0, hz0, hid⟩
  exact
    Or.inr
      ⟨e, z0, hwin, hz0, hid⟩




/-- Initiator branch 3: a negative-direction bump from the responder. -/
private theorem originInitiatorBumpBranch
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (Cpost : Config n psi kappa)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (p : State psi kappa × State psi kappa)
    (z : GhostToken n psi)
    (hCdPost : Cd ring k kind Cpost)
    (hwin : Lemma4InWindow ring k psi e)
    (hdist :
      (Cpost e).dist = p.1.dist ∧
        (Cpost (ring.rightNeighbor e)).dist =
          p.2.dist)
    (hlocal :
      originLocalValid kind p.1 z.value)
    (hshape :
      originLeftMovedShape z.value)
    (hsource :
      ∃ z0,
        ghostTokenAt kind G
            (ring.rightNeighbor e) = some z0 ∧
          z.lmeta.id = z0.lmeta.id) :
    originConclusion ring k kind G z := by
  rcases hwin with ⟨x, hx⟩
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) := by
    by_cases hnext :
        x.val + 1 < 2 * psi
    · let y : Fin (2 * psi) :=
        ⟨x.val + 1, hnext⟩
      refine ⟨y, ?_⟩
      calc
        ring.rightNeighbor e =
            ring.rightNeighbor
              (shiftRight ring k x.val) :=
          congrArg ring.rightNeighbor hx
        _ = shiftRight ring k (x.val + 1) :=
          originRightNeighborShiftRight
            ring k x.val
        _ = shiftRight ring k y.val := by
          rfl
    · have hxlast :
          x.val = 2 * psi - 1 := by
        have hxlt := x.isLt
        omega
      have hrow := hCdPost x
      dsimp only at hrow
      have hpost :
          (Cpost e).dist.val =
            (x.val + tokenD' psi kind) %
              (2 * psi) := by
        rw [hx]
        exact hrow.1
      have hpdist :
          p.1.dist.val =
            (2 * psi - 1 +
                tokenD' psi kind) %
              (2 * psi) := by
        calc
          p.1.dist.val =
              (Cpost e).dist.val :=
            (congrArg Fin.val hdist.1).symm
          _ =
              (x.val + tokenD' psi kind) %
                (2 * psi) := hpost
          _ =
              (2 * psi - 1 +
                  tokenD' psi kind) %
                (2 * psi) := by
            rw [hxlast]
      exact
        False.elim
          (originLeftMovedNotLast
            hpsi kind p.1 z.value
            hpdist hlocal hshape)
  rcases hsource with ⟨z0, hz0, hid⟩
  exact
    Or.inr
      ⟨ring.rightNeighbor e, z0,
        hwinR, hz0, hid⟩




/-! ## Public provenance leaves -/


theorem lemma4CoverageOriginResponderRow_proved :
    Lemma4CoverageOriginResponderRow := by
  unfold Lemma4CoverageOriginResponderRow
  intro n psi kappa hpsi ring k kind step G e z
  intro hCd hCdPost hwin hpost
  have hn2 :=
    originCdTwoLe
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    originRightNeighborNe ring hn2 e
  let p :=
    originSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hdist :
      ((ghostStep hpsi ring step G e).phys e).dist =
          p.1.dist ∧
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          p.2.dist := by
    simpa [p] using
      (originStepSelectedDist
        hpsi ring step G e kind hne)
  rw [originGhostTokenAtStep
    hpsi ring step G e kind
      (ring.rightNeighbor e)] at hpost
  simp only
    [originSetTwo, if_neg hne, if_pos rfl]
    at hpost
  unfold originMovedPair at hpost
  dsimp only at hpost
  change
    (originGhostMoveToken
      hpsi kind step e
      p.1 p.2
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G
        (ring.rightNeighbor e))).right =
      some z at hpost
  have hsplit :=
    originResponderGhostBranchSplit
      hpsi kind step e
      p.1 p.2
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z hpost
  change originConclusion ring k kind G z
  rcases hsplit with hstay | hbump
  · exact
      originResponderStayBranch
        ring k kind G e z
        hwin hstay
  · exact
      originResponderBumpBranch
        hpsi ring k kind
        (ghostStep hpsi ring step G e).phys
        G e p z step
        hCdPost hwin hdist
        hbump.1 hbump.2.1 hbump.2.2




theorem lemma4CoverageOriginInitiatorRow_proved :
    Lemma4CoverageOriginInitiatorRow := by
  unfold Lemma4CoverageOriginInitiatorRow
  intro n psi kappa hpsi ring k kind step G e z
  intro hCd hCdPost hwin hpost
  have hn2 :=
    originCdTwoLe
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    originRightNeighborNe ring hn2 e
  let p :=
    originSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hdist :
      ((ghostStep hpsi ring step G e).phys e).dist =
          p.1.dist ∧
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          p.2.dist := by
    simpa [p] using
      (originStepSelectedDist
        hpsi ring step G e kind hne)
  rw [originGhostTokenAtStep
    hpsi ring step G e kind e] at hpost
  simp only
    [originSetTwo, if_pos rfl] at hpost
  unfold originMovedPair at hpost
  dsimp only at hpost
  change
    (originGhostMoveToken
      hpsi kind step e
      p.1 p.2
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G
        (ring.rightNeighbor e))).left =
      some z at hpost
  have hsplit :=
    originInitiatorGhostBranchSplit
      hpsi kind step e
      p.1 p.2
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z hpost
  change originConclusion ring k kind G z
  rcases hsplit with hbirth | hrest
  · exact
      originInitiatorBirthBranch
        hpsi ring k kind
        (ghostStep hpsi ring step G e).phys
        G e p z step
        hCdPost hwin hdist.1 hbirth
  · rcases hrest with hstay | hbump
    · exact
        originInitiatorStayBranch
          ring k kind G e z
          hwin hstay
    · exact
        originInitiatorBumpBranch
          hpsi ring k kind
          (ghostStep hpsi ring step G e).phys
          G e p z
          hCdPost hwin hdist
          hbump.1 hbump.2.1 hbump.2.2




end PPL




#print axioms PPL.lemma4CoverageOriginResponderRow_proved
#print axioms PPL.lemma4CoverageOriginInitiatorRow_proved


