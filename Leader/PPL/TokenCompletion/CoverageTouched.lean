import Leader.PPL.TokenCompletion.CoverageRows








namespace PPL








set_option autoImplicit false
set_option Elab.async false








private def coverageTouchedBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)
















private def coverageTouchedMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)
















private def coverageTouchedLocalValid {psi kappa : Nat}
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
















private instance instDecidableCoverageTouchedLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (coverageTouchedLocalValid kind q t) := by
  unfold coverageTouchedLocalValid
  infer_instance
















private def coverageTouchedSetToken {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }
















private def coverageTouchedClearInvalid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if coverageTouchedLocalValid kind q t then
        q
      else
        coverageTouchedSetToken kind q none
















private def coverageTouchedLeaderBirth {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }
















private theorem coverageTouchedSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      coverageTouchedSetToken kind q t := by
  cases kind <;> rfl
















private theorem coverageTouchedSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    sourceClear kind q =
      coverageTouchedClearInvalid kind q := by
  cases kind <;> rfl
















private theorem coverageTouchedSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = coverageTouchedLeaderBirth q := by
  rfl
















private def coverageTouchedNegTurnNext {psi : Nat}
    (hpsi : 2 <= psi) (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    coverageTouchedMkToken
      (offsetPsiCode psi hpsi)
      (coverageTouchedBitToFin (!sourceBit))
      (coverageTouchedBitToFin sourceBit)
  else
    coverageTouchedMkToken
      (offsetPsiCode psi hpsi)
      (coverageTouchedBitToFin sourceBit)
      (0 : Fin 2)
















private def coverageTouchedMoveToken
    {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
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
            (coverageTouchedMkToken
              (offsetPsiCode psi hpsi)
              (coverageTouchedBitToFin (!l.id))
              (coverageTouchedBitToFin l.id)))
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
            if hm1 : c = -1 then
              let next :=
                coverageTouchedNegTurnNext
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
                    (coverageTouchedMkToken
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
                (coverageTouchedMkToken
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
                (coverageTouchedMkToken
                  nextOffset t.1.2 t.2))
          let l := sourceSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)
















private theorem coverageTouchedMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa) :
    coverageTouchedMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl
















private def coverageTouchedLiveShadow
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
              (coverageTouchedLocalValid kind q t) then
            some z
          else
            none
















private def coverageTouchedLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if coverageTouchedLocalValid kind q t then
        some t
      else
        none
















private def coverageTouchedBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      coverageTouchedMkToken
        (offsetPsiCode psi hpsi)
        (coverageTouchedBitToFin (!idBit))
        (coverageTouchedBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }
















private def coverageTouchedBumpTo
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
        if coverageTouchedLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩
















private def coverageTouchedGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := coverageTouchedLiveValue kind l
  let rv0 := coverageTouchedLiveValue kind r
  let gl0 := coverageTouchedLiveShadow kind l gl
  let gr0 := coverageTouchedLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (coverageTouchedBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (coverageTouchedBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := And (lv1 ≠ none) (rv0 ≠ none)
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if h1 : c = 1 then
          let next :=
            coverageTouchedMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            coverageTouchedBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            coverageTouchedMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            coverageTouchedBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some t =>
              let c := decodeOffset psi (tokenCode t)
              if hm1 : c = -1 then
                let next :=
                  coverageTouchedNegTurnNext hpsi l.id t
                let b :=
                  coverageTouchedBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  coverageTouchedMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  coverageTouchedBumpTo kind l next gr0
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
                coverageTouchedNegTurnNext hpsi l.id t
              let b :=
                coverageTouchedBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                coverageTouchedMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                coverageTouchedBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩
















private def coverageTouchedPrelude
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
















private def coverageTouchedSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := coverageTouchedPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2
















private def coverageTouchedSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := coverageTouchedSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2
















private def coverageTouchedSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k
















private def coverageTouchedMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    coverageTouchedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  coverageTouchedGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))
















private theorem coverageTouchedGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      coverageTouchedSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (coverageTouchedMovedPair
          hpsi ring step G e kind).left
        (coverageTouchedMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl
























/-! ## Public physical suffix frame -/
















private theorem coverageTouchedMoveToken_dist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := moveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only
  have hi :=
    moveToken_initiator_fields
      hpsi kind l r
  have hil :
      (moveToken hpsi kind l r).1.dist =
        l.dist := by
    have h :=
      congrArg
        (fun q : State psi kappa => q.dist) hi
    cases kind <;>
      simpa [eraseKindToken] using h
  rcases
      moveToken_responder_fields
        hpsi kind l r with hr | hr
  · have hrr :
        (moveToken hpsi kind l r).2.dist =
          r.dist := by
      have h :=
        congrArg
          (fun q : State psi kappa => q.dist) hr
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken]
          using h
    exact ⟨hil, hrr⟩
  · have hrr :
        (moveToken hpsi kind l r).2.dist =
          r.dist := by
      have h :=
        congrArg
          (fun q : State psi kappa => q.dist) hr
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken,
            birthFields] using h
    exact ⟨hil, hrr⟩
















private theorem coverageTouchedElimFrame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := eliminateLeaders l r
    And
      (tokenAt kind q.1 = tokenAt kind l)
      (And
        (q.1.dist = l.dist)
        (And
          (tokenAt kind q.2 = tokenAt kind r)
          (q.2.dist = r.dist))) := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  cases kind with
  | black =>
      exact
        And.intro
          (by
            have h :=
              congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.tokenB) hl
            simpa [PPL.Elim.otherView, tokenAt]
              using h)
          (And.intro
            (congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.dist) hl)
            (And.intro
              (by
                have h :=
                  congrArg
                    (fun q : PPL.Elim.OtherFields
                      psi kappa => q.tokenB) hr
                simpa [PPL.Elim.otherView, tokenAt]
                  using h)
              (congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.dist) hr)))
  | white =>
      exact
        And.intro
          (by
            have h :=
              congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.tokenW) hl
            simpa [PPL.Elim.otherView, tokenAt]
              using h)
          (And.intro
            (congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.dist) hl)
            (And.intro
              (by
                have h :=
                  congrArg
                    (fun q : PPL.Elim.OtherFields
                      psi kappa => q.tokenW) hr
                simpa [PPL.Elim.otherView, tokenAt]
                  using h)
              (congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.dist) hr)))
















private theorem coverageTouchedWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    And
      (tokenAt .black
          (moveToken hpsi .white l r).1 =
        tokenAt .black l)
      (tokenAt .black
          (moveToken hpsi .white l r).2 =
        tokenAt .black r) := by
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
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          tokenAt]
        using h
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          birthFields, tokenAt]
        using h
















private theorem coverageTouchedPplSelectedFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let s :=
      coverageTouchedSelectedOutput hpsi kind l r
    let q := ppl hpsi l r
    And
      (tokenAt kind q.1 = tokenAt kind s.1)
      (And
        (q.1.dist = s.1.dist)
        (And
          (tokenAt kind q.2 = tokenAt kind s.2)
          (q.2.dist = s.2.dist))) := by
  cases kind with
  | black =>
      let p := coverageTouchedPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hwTok :=
        coverageTouchedWhitePreservesBlack
          hpsi b.1 b.2
      have hwDist :=
        coverageTouchedMoveToken_dist
          hpsi .white b.1 b.2
      have he :=
        coverageTouchedElimFrame
          TokenKind.black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          coverageTouchedSelectedOutput
              hpsi TokenKind.black l r =
            b := by
        rfl
      dsimp only at hwDist he
      rw [hfull, hselected]
      exact
        And.intro
          (he.1.trans hwTok.1)
          (And.intro
            (he.2.1.trans hwDist.1)
            (And.intro
              (he.2.2.1.trans hwTok.2)
              (he.2.2.2.trans hwDist.2)))
  | white =>
      let p := coverageTouchedPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        coverageTouchedElimFrame
          TokenKind.white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          coverageTouchedSelectedOutput
              hpsi TokenKind.white l r =
            w := by
        rfl
      dsimp only at he
      rw [hfull, hselected]
      exact he
































/-! ## Lightweight coverage relations -/








private def CoverageTouchedValidAt
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : Prop :=
  exists t : TokenData psi,
    And
      (tokenAt kind q = some t)
      (coverageTouchedLocalValid kind q t)








private def CoverageTouchedShadowReady
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) : Prop :=
  forall t : TokenData psi,
    coverageTouchedLiveValue kind q = some t ->
      exists z : GhostToken n psi,
        coverageTouchedLiveShadow kind q g = some z








private theorem coverageTouched_validAt_of_validToken
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (i : Fin n)
    (hvalid : ValidToken kind C i) :
    CoverageTouchedValidAt kind (C i) := by
  unfold ValidToken at hvalid
  cases ht : tokenAt kind (C i) with
  | none =>
      rw [ht] at hvalid
      exact False.elim hvalid
  | some t =>
      rw [ht] at hvalid
      exact ⟨t, ht, hvalid⟩








private theorem coverageTouched_validAt_transport
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (htok : tokenAt kind q = tokenAt kind q')
    (hdist : q.dist = q'.dist) :
    CoverageTouchedValidAt kind q <->
      CoverageTouchedValidAt kind q' := by
  constructor
  · rintro ⟨t, ht, hv⟩
    refine ⟨t, htok.symm.trans ht, ?_⟩
    unfold coverageTouchedLocalValid at hv ⊢
    unfold tokenTargetCoordinate at hv ⊢
    rw [← hdist]
    exact hv
  · rintro ⟨t, ht, hv⟩
    refine ⟨t, htok.trans ht, ?_⟩
    unfold coverageTouchedLocalValid at hv ⊢
    unfold tokenTargetCoordinate at hv ⊢
    rw [hdist]
    exact hv








/-! ## One private lemma for each literal owner carrier -/








/--
The liveShadow stay branch.  This is the one branch that needs GhostSound:
the old unsound counterexample supplied an owner whose value disagreed with
the physical token, so liveShadow deleted it.
-/
private theorem coverageTouched_liveShadow_stay
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (t : TokenData psi)
    (howner :
      exists z : GhostToken n psi,
        g = some z ∧ z.value = t)
    (htok : tokenAt kind q = some t)
    (hvalid : coverageTouchedLocalValid kind q t) :
    exists z : GhostToken n psi,
      coverageTouchedLiveShadow kind q g = some z := by
  rcases howner with ⟨z, hg, hz⟩
  subst g
  subst t
  refine ⟨z, ?_⟩
  simp [coverageTouchedLiveShadow, htok, hvalid]








/-- The birthGhost branch always carries a fresh owner. -/
private theorem coverageTouched_birthGhost_owner
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    exists z : GhostToken n psi,
      some
        (coverageTouchedBirthGhost
          hpsi kind step site idBit) = some z := by
  exact
    ⟨coverageTouchedBirthGhost
      hpsi kind step site idBit, rfl⟩








/-- The bumpTo move branch keeps the moving owner exactly when its new value is valid. -/
private theorem coverageTouched_bumpTo_owner
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (next : TokenData psi)
    (g : Option (GhostToken n psi))
    (hg : g ≠ none)
    (hv : coverageTouchedLocalValid kind q next) :
    exists z : GhostToken n psi,
      (coverageTouchedBumpTo kind q next g).live = some z := by
  cases hg0 : g with
  | none =>
      exact False.elim (hg hg0)
  | some z =>
      let z' : GhostToken n psi :=
        { value := next
          lmeta :=
            { z.lmeta with moves := z.lmeta.moves + 1 } }
      refine ⟨z', ?_⟩
      simp [coverageTouchedBumpTo, hg0, hv, z']








/-! ## C_d geometry and selected-input alignment -/








private theorem coverageTouchedCdGeometryEq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (hC : Cd ring k kind C)
    (hC' : Cd ring k kind C')
    (i : Fin n)
    (hi : Lemma4InWindow ring k psi i) :
    And
      ((C i).dist = (C' i).dist)
      ((C i).last = (C' i).last) := by
  rcases hi with ⟨x, rfl⟩
  have h0 := hC x
  have h1 := hC' x
  dsimp only at h0 h1
  constructor
  · apply Fin.ext
    exact h0.1.trans h1.1.symm
  · exact h0.2.trans h1.2.symm








private structure CoverageTouchedTokenFields (psi : Nat) where
  tokenB : Option (TokenData psi)
  tokenW : Option (TokenData psi)








private def coverageTouchedTokenFields
    {psi kappa : Nat}
    (q : State psi kappa) :
    CoverageTouchedTokenFields psi where
  tokenB := q.tokenB
  tokenW := q.tokenW








private theorem coverageTouchedDetermineModeTokenFields
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let d := determineMode l r
    coverageTouchedTokenFields d.1 =
        coverageTouchedTokenFields l ∧
      coverageTouchedTokenFields d.2 =
        coverageTouchedTokenFields r := by
  simp only [determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl⟩








private theorem coverageTouchedDetermineModeTokenFrame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (determineMode l r).1 =
        tokenAt kind l ∧
      tokenAt kind (determineMode l r).2 =
        tokenAt kind r := by
  have hd :=
    coverageTouchedDetermineModeTokenFields l r
  dsimp only at hd
  cases kind with
  | black =>
      have hl :=
        congrArg
          (fun z : CoverageTouchedTokenFields psi =>
            z.tokenB) hd.1
      have hr :=
        congrArg
          (fun z : CoverageTouchedTokenFields psi =>
            z.tokenB) hd.2
      exact
        ⟨by
            simpa [coverageTouchedTokenFields, tokenAt]
              using hl,
          by
            simpa [coverageTouchedTokenFields, tokenAt]
              using hr⟩
  | white =>
      have hl :=
        congrArg
          (fun z : CoverageTouchedTokenFields psi =>
            z.tokenW) hd.1
      have hr :=
        congrArg
          (fun z : CoverageTouchedTokenFields psi =>
            z.tokenW) hd.2
      exact
        ⟨by
            simpa [coverageTouchedTokenFields, tokenAt]
              using hl,
          by
            simpa [coverageTouchedTokenFields, tokenAt]
              using hr⟩








private theorem coverageTouchedCreateLeaderTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := createLeaderThroughLine6 hpsi l r
    And
      (tokenAt kind q.left = tokenAt kind l)
      (tokenAt kind q.right = tokenAt kind r) := by
  have hd :=
    coverageTouchedDetermineModeTokenFrame
      kind l r
  dsimp only
  constructor
  · exact hd.1
  · by_cases hguard :
        createLeaderLine6Guard hpsi l r
    · simp only
        [createLeaderThroughLine6, if_pos hguard]
      change
        tokenAt kind
            (sourceBirth (determineMode l r).2) =
          tokenAt kind r
      rw [coverageTouchedSourceBirth_eq]
      cases kind <;>
        simpa
          [coverageTouchedLeaderBirth, tokenAt]
          using hd.2
    · simp only
        [createLeaderThroughLine6, if_neg hguard]
      exact hd.2








private theorem coverageTouchedPreludeTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := coverageTouchedPrelude hpsi l r
    tokenAt kind p.1 = tokenAt kind l ∧
      tokenAt kind p.2 = tokenAt kind r := by
  have hs :=
    coverageTouchedCreateLeaderTokenFrame
      hpsi kind l r
  dsimp only at hs
  constructor
  · calc
      tokenAt kind
            (coverageTouchedPrelude hpsi l r).1 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).left := by
        unfold coverageTouchedPrelude
        cases kind <;> (try simp only [tokenAt]) <;>
          (repeat' split) <;> (try rfl)
      _ = tokenAt kind l := hs.1
  · calc
      tokenAt kind
            (coverageTouchedPrelude hpsi l r).2 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).right := by
        unfold coverageTouchedPrelude
        cases kind <;> (try simp only [tokenAt]) <;>
          (repeat' split) <;> (try rfl)
      _ = tokenAt kind r := hs.2








private theorem coverageTouchedBlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    And
      (tokenAt .white
          (moveToken hpsi .black l r).1 =
        tokenAt .white l)
      (tokenAt .white
          (moveToken hpsi .black l r).2 =
        tokenAt .white r) := by
  have hi :=
    moveToken_initiator_fields
      hpsi TokenKind.black l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenW) hi
  constructor
  · simpa [eraseKindToken, tokenAt] using hil
  · rcases
      moveToken_responder_fields
        hpsi TokenKind.black l r with hr | hr
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenW) hr
      simpa
        [eraseKindTokenId, eraseKindToken, tokenAt]
        using h
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenW) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          birthFields, tokenAt]
        using h








private theorem coverageTouchedSelectedInputTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := coverageTouchedSelectedInput hpsi kind l r
    And
      (tokenAt kind p.1 = tokenAt kind l)
      (tokenAt kind p.2 = tokenAt kind r) := by
  cases kind with
  | black =>
      exact
        coverageTouchedPreludeTokenFrame
          hpsi .black l r
  | white =>
      let p := coverageTouchedPrelude hpsi l r
      have hp :=
        coverageTouchedPreludeTokenFrame
          hpsi .white l r
      have hb :=
        coverageTouchedBlackPreservesWhite
          hpsi p.1 p.2
      dsimp only [coverageTouchedSelectedInput]
      exact
        And.intro
          (hb.1.trans hp.1)
          (hb.2.trans hp.2)








private theorem coverageTouchedStepLeftState
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
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








private theorem coverageTouchedStepRightState
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
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








private theorem coverageTouchedSelectedInputDistLeft
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hwin : Lemma4InWindow ring k psi e) :
    (coverageTouchedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).1.dist =
      (G.phys e).dist := by
  let p :=
    coverageTouchedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hm :=
    coverageTouchedMoveToken_dist
      hpsi kind p.1 p.2
  have hf :=
    coverageTouchedPplSelectedFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hs :=
    coverageTouchedStepLeftState
      hpsi ring step G e
  have hg :=
    coverageTouchedCdGeometryEq
      ring k kind G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' e hwin
  dsimp only at hm hf
  calc
    p.1.dist =
        (coverageTouchedSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.dist :=
      hm.1.symm
    _ =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.dist :=
      hf.2.1.symm
    _ =
        ((ghostStep hpsi ring step G e).phys e).dist := by
      rw [hs]
    _ = (G.phys e).dist := hg.1.symm








private theorem coverageTouchedSelectedInputDistRight
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e)) :
    (coverageTouchedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).2.dist =
      (G.phys (ring.rightNeighbor e)).dist := by
  let p :=
    coverageTouchedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hm :=
    coverageTouchedMoveToken_dist
      hpsi kind p.1 p.2
  have hf :=
    coverageTouchedPplSelectedFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hs :=
    coverageTouchedStepRightState
      hpsi ring step G e hne
  have hg :=
    coverageTouchedCdGeometryEq
      ring k kind G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd'
      (ring.rightNeighbor e) hwin
  dsimp only at hm hf
  calc
    p.2.dist =
        (coverageTouchedSelectedOutput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.dist :=
      hm.2.symm
    _ =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2.dist :=
      hf.2.2.2.symm
    _ =
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist := by
      rw [hs]
    _ = (G.phys (ring.rightNeighbor e)).dist :=
      hg.1.symm








private theorem coverageTouchedGhostSoundAt
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa)
    (hsound : GhostSound G)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hz : ghostTokenAt kind G i = some z) :
    And
      (tokenAt kind (G.phys i) = some z.value)
      (coverageTouchedLocalValid
        kind (G.phys i) z.value) := by
  cases kind with
  | black =>
      exact hsound.1 i z hz
  | white =>
      exact hsound.2 i z hz








private theorem coverageTouchedShadowReadyLeft
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (hwin : Lemma4InWindow ring k psi e) :
    CoverageTouchedShadowReady kind
      (coverageTouchedSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1
      (ghostTokenAt kind G e) := by
  intro t ht
  have htok :=
    (coverageTouchedSelectedInputTokenFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).1
  have hdist :=
    coverageTouchedSelectedInputDistLeft
      hpsi ring k kind step G e
      hCd hCd' hwin
  have hlocal :
      coverageTouchedLocalValid kind (G.phys e) t := by
    unfold coverageTouchedLiveValue at ht
    cases hs :
        tokenAt kind
          (coverageTouchedSelectedInput hpsi kind
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).1 with
    | none =>
        simp [hs] at ht
    | some u =>
        by_cases hv :
            coverageTouchedLocalValid kind
              (coverageTouchedSelectedInput hpsi kind
                (G.phys e)
                (G.phys (ring.rightNeighbor e))).1 u
        · simp [hs, hv] at ht
          subst u
          unfold coverageTouchedLocalValid at hv ⊢
          unfold tokenTargetCoordinate at hv ⊢
          rw [hdist] at hv
          exact hv
        · simp [hs, hv] at ht
  have htok0 :
      tokenAt kind (G.phys e) = some t := by
    rw [← htok]
    unfold coverageTouchedLiveValue at ht
    cases hs :
        tokenAt kind
          (coverageTouchedSelectedInput hpsi kind
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).1 with
    | none =>
        simp [hs] at ht
    | some u =>
        by_cases hv :
            coverageTouchedLocalValid kind
              (coverageTouchedSelectedInput hpsi kind
                (G.phys e)
                (G.phys (ring.rightNeighbor e))).1 u
        · simp [hs, hv] at ht
          simpa [ht] using hs
        · simp [hs, hv] at ht
  have hvalid0 : ValidToken kind G.phys e := by
    unfold ValidToken
    rw [htok0]
    exact hlocal
  obtain ⟨z, hz⟩ :=
    hcovered e hwin hvalid0
  have hs :=
    coverageTouchedGhostSoundAt
      G hsound kind e z hz
  have hzval : z.value = t := by
    exact Option.some.inj (hs.1.symm.trans htok0)
  apply
    coverageTouched_liveShadow_stay
      kind
      (coverageTouchedSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1
      (ghostTokenAt kind G e) t
  · exact ⟨z, hz, hzval⟩
  · rw [htok]
    exact htok0
  · unfold coverageTouchedLocalValid at hlocal ⊢
    unfold tokenTargetCoordinate at hlocal ⊢
    rw [hdist]
    exact hlocal








private theorem coverageTouchedShadowReadyRight
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e)) :
    CoverageTouchedShadowReady kind
      (coverageTouchedSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2
      (ghostTokenAt kind G
        (ring.rightNeighbor e)) := by
  intro t ht
  have htok :=
    (coverageTouchedSelectedInputTokenFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).2
  have hdist :=
    coverageTouchedSelectedInputDistRight
      hpsi ring k kind step G e hne
      hCd hCd' hwin
  have hlocal :
      coverageTouchedLocalValid kind
        (G.phys (ring.rightNeighbor e)) t := by
    unfold coverageTouchedLiveValue at ht
    cases hs :
        tokenAt kind
          (coverageTouchedSelectedInput hpsi kind
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).2 with
    | none =>
        simp [hs] at ht
    | some u =>
        by_cases hv :
            coverageTouchedLocalValid kind
              (coverageTouchedSelectedInput hpsi kind
                (G.phys e)
                (G.phys (ring.rightNeighbor e))).2 u
        · simp [hs, hv] at ht
          subst u
          unfold coverageTouchedLocalValid at hv ⊢
          unfold tokenTargetCoordinate at hv ⊢
          rw [hdist] at hv
          exact hv
        · simp [hs, hv] at ht
  have htok0 :
      tokenAt kind
        (G.phys (ring.rightNeighbor e)) = some t := by
    rw [← htok]
    unfold coverageTouchedLiveValue at ht
    cases hs :
        tokenAt kind
          (coverageTouchedSelectedInput hpsi kind
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).2 with
    | none =>
        simp [hs] at ht
    | some u =>
        by_cases hv :
            coverageTouchedLocalValid kind
              (coverageTouchedSelectedInput hpsi kind
                (G.phys e)
                (G.phys (ring.rightNeighbor e))).2 u
        · simp [hs, hv] at ht
          simpa [ht] using hs
        · simp [hs, hv] at ht
  have hvalid0 :
      ValidToken kind G.phys
        (ring.rightNeighbor e) := by
    unfold ValidToken
    rw [htok0]
    exact hlocal
  obtain ⟨z, hz⟩ :=
    hcovered (ring.rightNeighbor e) hwin hvalid0
  have hs :=
    coverageTouchedGhostSoundAt
      G hsound kind (ring.rightNeighbor e) z hz
  have hzval : z.value = t := by
    exact Option.some.inj (hs.1.symm.trans htok0)
  apply
    coverageTouched_liveShadow_stay
      kind
      (coverageTouchedSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2
      (ghostTokenAt kind G
        (ring.rightNeighbor e)) t
  · exact ⟨z, hz, hzval⟩
  · rw [htok]
    exact htok0
  · unfold coverageTouchedLocalValid at hlocal ⊢
    unfold tokenTargetCoordinate at hlocal ⊢
    rw [hdist]
    exact hlocal








/-! ## Finite branch rows -/








/-
Insert these declarations immediately before
coverageTouchedInitiatorBranches, replacing the two old branch helpers below.

They use only definitions already present earlier in L4Touched-R9.lean.
-/

/-! -------------------------------------------------------------------------
    Small named field projections
------------------------------------------------------------------------- -/

private theorem coverageTouchedTokenAt_setToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    tokenAt kind
        (coverageTouchedSetToken kind q x) =
      x := by
  cases kind <;> rfl


private theorem coverageTouchedTokenAt_sourceSet
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q x) = x := by
  rw [coverageTouchedSourceSet_eq]
  exact coverageTouchedTokenAt_setToken kind q x


private theorem coverageTouchedTokenAt_sourceBirth
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceBirth q) =
      tokenAt kind q := by
  rw [coverageTouchedSourceBirth_eq]
  cases kind <;>
    rfl


private theorem coverageTouchedTokenAt_clearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind
        (coverageTouchedClearInvalid kind q) =
      coverageTouchedLiveValue kind q := by
  unfold coverageTouchedClearInvalid
  unfold coverageTouchedLiveValue
  cases htok : tokenAt kind q with
  | none =>
      exact htok
  | some t =>
      show tokenAt kind
          (if coverageTouchedLocalValid kind q t then q
            else coverageTouchedSetToken kind q none) =
        (if coverageTouchedLocalValid kind q t then some t else none)
      by_cases hv :
          coverageTouchedLocalValid kind q t
      · rw [if_pos hv, if_pos hv]
        exact htok
      · rw [if_neg hv, if_neg hv]
        exact coverageTouchedTokenAt_setToken kind q none


private theorem coverageTouchedTokenAt_sourceClear
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      coverageTouchedLiveValue kind q := by
  rw [coverageTouchedSourceClear_eq]
  exact coverageTouchedTokenAt_clearInvalid kind q


private theorem coverageTouchedShadow_of_liveValue
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hready : CoverageTouchedShadowReady kind q g)
    (t : TokenData psi)
    (ht :
      coverageTouchedLiveValue kind q = some t) :
    ∃ z : GhostToken n psi,
      coverageTouchedLiveShadow kind q g =
        some z := by
  exact hready t ht


private theorem coverageTouchedBump_owner_of_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (next : TokenData psi)
    (g : Option (GhostToken n psi))
    (hg : g ≠ none)
    (hv :
      coverageTouchedLocalValid kind q next) :
    (coverageTouchedBumpTo
        kind q next g).live ≠ none := by
  obtain ⟨z, hz⟩ :=
    coverageTouched_bumpTo_owner
      kind q next g hg hv
  rw [hz]
  simp


/-! -------------------------------------------------------------------------
    Seven explicit selected-move carrier cases
------------------------------------------------------------------------- -/

/--
Collision: the selected left contender is deleted.  Therefore no valid
initiator output can be justified by the collided left value.  Any surviving
responder value is still the responder live value, hence its sound shadow
supplies the ghost owner.
-/
private theorem coverageTouched_collision_case
    {n psi kappa : Nat}
    (kind : TokenKind)
    (r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (hR : CoverageTouchedShadowReady kind r gr)
    (t : TokenData psi)
    (hrt :
      coverageTouchedLiveValue kind r = some t) :
    coverageTouchedLiveShadow kind r gr ≠ none := by
  obtain ⟨z, hz⟩ :=
    coverageTouchedShadow_of_liveValue
      kind r gr hR t hrt
  rw [hz]
  simp


/-- c = 1: a sound left owner is bumped to the responder. -/
private theorem coverageTouched_c1_turn_case
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (r : State psi kappa)
    (t : TokenData psi)
    (g : Option (GhostToken n psi))
    (hg : g ≠ none)
    (hvalid :
      coverageTouchedLocalValid kind r
        (coverageTouchedMkToken
          (offsetNegPsiPlusOneCode psi hpsi)
          t.1.2 t.2)) :
    (coverageTouchedBumpTo
        kind r
        (coverageTouchedMkToken
          (offsetNegPsiPlusOneCode psi hpsi)
          t.1.2 t.2)
        g).live ≠ none := by
  exact
    coverageTouchedBump_owner_of_valid
      kind r
      (coverageTouchedMkToken
        (offsetNegPsiPlusOneCode psi hpsi)
        t.1.2 t.2)
      g hg hvalid


/-- c >= 2: ordinary positive motion bumps the sound left owner right. -/
private theorem coverageTouched_pos_move_case
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (r : State psi kappa)
    (t : TokenData psi)
    (c : Int)
    (hc : ValidOffset psi c)
    (hc2 : 2 <= c)
    (g : Option (GhostToken n psi))
    (hg : g ≠ none)
    (hvalid :
      coverageTouchedLocalValid kind r
        (coverageTouchedMkToken
          (encodeOffset psi (c - 1) (by
            rcases hc with hn | hp
            · exfalso
              omega
            · right
              omega))
          t.1.2 t.2)) :
    (coverageTouchedBumpTo
        kind r
        (coverageTouchedMkToken
          (encodeOffset psi (c - 1) (by
            rcases hc with hn | hp
            · exfalso
              omega
            · right
              omega))
          t.1.2 t.2)
        g).live ≠ none := by
  exact
    coverageTouchedBump_owner_of_valid
      kind r
      (coverageTouchedMkToken
        (encodeOffset psi (c - 1) (by
          rcases hc with hn | hp
          · exfalso
            omega
          · right
            omega))
        t.1.2 t.2)
      g hg hvalid


/-- c <= -2: ordinary negative motion bumps the sound responder owner left. -/
private theorem coverageTouched_neg_move_case
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l : State psi kappa)
    (t : TokenData psi)
    (c : Int)
    (hc : ValidOffset psi c)
    (hc2 : c <= -2)
    (g : Option (GhostToken n psi))
    (hg : g ≠ none)
    (hvalid :
      coverageTouchedLocalValid kind l
        (coverageTouchedMkToken
          (encodeOffset psi (c + 1) (by
            rcases hc with hn | hp
            · left
              omega
            · exfalso
              omega))
          t.1.2 t.2)) :
    (coverageTouchedBumpTo
        kind l
        (coverageTouchedMkToken
          (encodeOffset psi (c + 1) (by
            rcases hc with hn | hp
            · left
              omega
            · exfalso
              omega))
          t.1.2 t.2)
        g).live ≠ none := by
  exact
    coverageTouchedBump_owner_of_valid
      kind l
      (coverageTouchedMkToken
        (encodeOffset psi (c + 1) (by
          rcases hc with hn | hp
          · left
            omega
          · exfalso
            omega))
        t.1.2 t.2)
      g hg hvalid


/-- c = -1: the responder turns and is bumped to the initiator. -/
private theorem coverageTouched_neg_turn_case
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l : State psi kappa)
    (t : TokenData psi)
    (g : Option (GhostToken n psi))
    (hg : g ≠ none)
    (hvalid :
      coverageTouchedLocalValid kind l
        (coverageTouchedNegTurnNext
          hpsi l.id t)) :
    (coverageTouchedBumpTo
        kind l
        (coverageTouchedNegTurnNext
          hpsi l.id t)
        g).live ≠ none := by
  exact
    coverageTouchedBump_owner_of_valid
      kind l
      (coverageTouchedNegTurnNext
        hpsi l.id t)
      g hg hvalid


/--
Stay: a physical live value at an endpoint has a live shadow by
CoverageTouchedShadowReady.
-/
private theorem coverageTouched_stay_case
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hready : CoverageTouchedShadowReady kind q g)
    (t : TokenData psi)
    (ht :
      coverageTouchedLiveValue kind q = some t) :
    coverageTouchedLiveShadow kind q g ≠ none := by
  obtain ⟨z, hz⟩ :=
    coverageTouchedShadow_of_liveValue
      kind q g hready t ht
  rw [hz]
  simp


/--
Birth: the physical and ghost birth guards are identical.  The born offset is
+psi, so psi >= 2 rules out c=1 and sends the born owner through the ordinary
positive-move carrier.  Thus, whenever that physical right output is locally
valid, the ghost right output is live.
-/
private theorem coverageTouched_birth_case
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (hvalid :
      coverageTouchedLocalValid kind r
        (coverageTouchedMkToken
          (encodeOffset psi
            (((psi : Nat) : Int) - 1)
            (by
              right
              omega))
          (coverageTouchedBitToFin (!l.id))
          (coverageTouchedBitToFin l.id))) :
    let born :=
      coverageTouchedBirthGhost
        hpsi kind step site l.id
    let next :=
      coverageTouchedMkToken
        (encodeOffset psi
          (((psi : Nat) : Int) - 1)
          (by
            right
            omega))
        (coverageTouchedBitToFin (!l.id))
        (coverageTouchedBitToFin l.id)
    (coverageTouchedBumpTo
        kind r next (some born)).live ≠ none := by
  dsimp only
  exact
    coverageTouchedBump_owner_of_valid
      kind r
      (coverageTouchedMkToken
        (encodeOffset psi
          (((psi : Nat) : Int) - 1)
          (by
            right
            omega))
        (coverageTouchedBitToFin (!l.id))
        (coverageTouchedBitToFin l.id))
      (some
        (coverageTouchedBirthGhost
          hpsi kind step site l.id))
      (by simp)
      hvalid


/-! -------------------------------------------------------------------------
    Two branch classifiers
------------------------------------------------------------------------- -/

/--
A cleared physical selected token and its ghost shadow have the same
availability: whenever the physical live value is present, ShadowReady gives
a nonempty ghost shadow.
-/
private theorem coverageTouchedCleared_owner
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hready : CoverageTouchedShadowReady kind q g)
    (t : TokenData psi)
    (ht :
      tokenAt kind (sourceClear kind q) =
        some t) :
    coverageTouchedLiveShadow kind q g ≠ none := by
  have hlive :
      coverageTouchedLiveValue kind q =
        some t := by
    rw [← coverageTouchedTokenAt_sourceClear]
    exact ht
  exact
    coverageTouched_stay_case
      kind q g hready t hlive


/--
The only use of local validity below is to turn the post physical
CoverageTouchedValidAt witness into the exact bumpTo validity premise.
-/
private theorem coverageTouchedValidAt_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hvalid : CoverageTouchedValidAt kind q)
    (htok : tokenAt kind q = some t) :
    coverageTouchedLocalValid kind q t := by
  rcases hvalid with ⟨u, hu, hv⟩
  rw [htok] at hu
  cases hu
  exact hv



/-! -------------------------------------------------------------------------
    Field projections used by the branch classifiers
------------------------------------------------------------------------- -/

/-- Clearing an invalid selected token changes only that token field; in
particular `last`, `id`, and `dist` are unchanged. -/
private theorem coverageTouchedSourceClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    And ((sourceClear kind q).last = q.last)
      (And ((sourceClear kind q).id = q.id)
        ((sourceClear kind q).dist = q.dist)) := by
  have key :
      Or (coverageTouchedClearInvalid kind q = q)
        (coverageTouchedClearInvalid kind q =
          coverageTouchedSetToken kind q none) := by
    unfold coverageTouchedClearInvalid
    cases tokenAt kind q with
    | none => exact Or.inl rfl
    | some t =>
        by_cases hv : coverageTouchedLocalValid kind q t
        · exact Or.inl (if_pos hv)
        · exact Or.inr (if_neg hv)
  rw [coverageTouchedSourceClear_eq]
  rcases key with h | h <;> rw [h]
  · exact ⟨rfl, rfl, rfl⟩
  · cases kind <;> exact ⟨rfl, rfl, rfl⟩

private theorem coverageTouchedSourceClear_last
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).last = q.last :=
  (coverageTouchedSourceClear_fields kind q).1

private theorem coverageTouchedSourceClear_id
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).id = q.id :=
  (coverageTouchedSourceClear_fields kind q).2.1

private theorem coverageTouchedSourceClear_dist
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (sourceClear kind q).dist = q.dist :=
  (coverageTouchedSourceClear_fields kind q).2.2

private theorem coverageTouchedSourceSet_id
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (x : Option (TokenData psi)) :
    (sourceSet kind q x).id = q.id := by
  rw [coverageTouchedSourceSet_eq]
  cases kind <;> rfl

private theorem coverageTouchedTokenCode_mk
    {psi : Nat} (o : Fin (2 * psi - 1)) (b c : Fin 2) :
    tokenCode (coverageTouchedMkToken o b c) = o := rfl

private theorem coverageTouchedBirthGhost_value
    {n psi : Nat} (hpsi : 2 <= psi) (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    (coverageTouchedBirthGhost hpsi kind step site idBit :
        GhostToken n psi).value =
      coverageTouchedMkToken
        (offsetPsiCode psi hpsi)
        (coverageTouchedBitToFin (!idBit))
        (coverageTouchedBitToFin idBit) := rfl

/-- Local validity reads the state only through `dist`. -/
private theorem coverageTouchedLocalValid_of_dist
    {psi kappa : Nat} (kind : TokenKind) (q q' : State psi kappa)
    (t : TokenData psi) (hdist : q.dist = q'.dist)
    (hv : coverageTouchedLocalValid kind q t) :
    coverageTouchedLocalValid kind q' t := by
  unfold coverageTouchedLocalValid at hv ⊢
  unfold tokenTargetCoordinate at hv ⊢
  rw [← hdist]
  exact hv

/-- The physical token move preserves both endpoint distances. -/
private theorem coverageTouchedMoveToken_dist_pair
    {psi kappa : Nat} (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa) :
    And ((coverageTouchedMoveToken hpsi kind l r).1.dist = l.dist)
      ((coverageTouchedMoveToken hpsi kind l r).2.dist = r.dist) := by
  rw [coverageTouchedMoveToken_eq]
  obtain ⟨h1, h2⟩ := coverageTouchedMoveToken_dist hpsi kind l r
  exact ⟨h1, h2⟩


-- replaces coverageTouchedInitiatorBranches
/--
Initiator branch classifier.  If the physical initiator output of the selected
token move carries a locally valid token, then the ghost initiator output is
live.  Proof: split on the two `last` flags, the two live values, the birth
guard, and the decoded offset signs; the physical and ghost machines take the
same branch, and each surviving branch is either a stay (sound shadow via
`CoverageTouchedShadowReady`) or a responder-to-initiator bump whose target
validity is the post validity transported along the unchanged `dist`.
-/
private theorem coverageTouchedInitiatorBranches
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hL : CoverageTouchedShadowReady kind l gl)
    (hR : CoverageTouchedShadowReady kind r gr)
    (hvalid :
      CoverageTouchedValidAt kind
        (coverageTouchedMoveToken
          hpsi kind l r).1) :
    (coverageTouchedGhostMoveToken
      hpsi kind step site l r gl gr).left ≠ none := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  obtain ⟨u, hu, hvu⟩ := hvalid
  have hvl : coverageTouchedLocalValid kind l u :=
    coverageTouchedLocalValid_of_dist kind _ l u
      (coverageTouchedMoveToken_dist_pair hpsi kind l r).1 hvu
  clear hvu
  intro hnone
  unfold coverageTouchedMoveToken at hu
  unfold coverageTouchedGhostMoveToken at hnone
  cases hl1 : l.last with
  | true =>
      simp only
        [coverageTouchedTokenAt_sourceSet,
         coverageTouchedTokenAt_sourceClear,
         coverageTouchedSourceClear_last,
         coverageTouchedSourceClear_id,
         coverageTouchedSourceClear_dist,
         coverageTouchedSourceSet_id,
         coverageTouchedTokenCode_mk,
         coverageTouchedBirthGhost_value,
         decodeOffset_psi, hpsi1, hpsi2,
         ne_eq, not_true_eq_false, not_false_eq_true,
         and_true, true_and, and_false, false_and, and_self,
         eq_self_iff_true, reduceCtorEq, Option.some.injEq,
         ↓reduceIte, ↓reduceDIte, hl1] at hu hnone
      all_goals
        exact coverageTouched_stay_case kind l gl hL u hu hnone
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [coverageTouchedTokenAt_sourceSet,
           coverageTouchedTokenAt_sourceClear,
           coverageTouchedSourceClear_last,
           coverageTouchedSourceClear_id,
           coverageTouchedSourceClear_dist,
           coverageTouchedSourceSet_id,
           coverageTouchedTokenCode_mk,
           coverageTouchedBirthGhost_value,
           decodeOffset_psi, hpsi1, hpsi2,
           ne_eq, not_true_eq_false, not_false_eq_true,
           and_true, true_and, and_false, false_and, and_self,
           eq_self_iff_true, reduceCtorEq, Option.some.injEq,
           ↓reduceIte, ↓reduceDIte, hl1, hr1] at hu hnone
        all_goals
          exact coverageTouched_stay_case kind l gl hL u hu hnone
    | false =>
      cases hAv : coverageTouchedLiveValue kind l with
      | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : coverageTouchedLiveValue kind r with
            | none =>
                simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
          · cases hBv : coverageTouchedLiveValue kind r with
            | none =>
                simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
      | some a =>
          cases hBv : coverageTouchedLiveValue kind r with
          | none =>
              by_cases h1 : decodeOffset psi (tokenCode a) = 1
              · simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
              · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1, h2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1, h2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
          | some b =>
              by_cases hm1 : decodeOffset psi (tokenCode b) = -1
              · simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
              · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1, hm2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1, hm2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind l gl hL _ hAv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind l _ _ (coverageTouched_stay_case kind r gr hR _ hBv) hvl hnone)


/--
Responder branch classifier, symmetric to `coverageTouchedInitiatorBranches`:
a locally valid physical responder output forces a live ghost responder
output.  Surviving branches are the responder stay, the `c = 1` turn, and the
`c >= 2` move (from a sound left owner or a freshly born owner).
-/
private theorem coverageTouchedResponderBranches
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hL : CoverageTouchedShadowReady kind l gl)
    (hR : CoverageTouchedShadowReady kind r gr)
    (hvalid :
      CoverageTouchedValidAt kind
        (coverageTouchedMoveToken
          hpsi kind l r).2) :
    (coverageTouchedGhostMoveToken
      hpsi kind step site l r gl gr).right ≠ none := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  obtain ⟨u, hu, hvu⟩ := hvalid
  have hvl : coverageTouchedLocalValid kind r u :=
    coverageTouchedLocalValid_of_dist kind _ r u
      (coverageTouchedMoveToken_dist_pair hpsi kind l r).2 hvu
  clear hvu
  intro hnone
  unfold coverageTouchedMoveToken at hu
  unfold coverageTouchedGhostMoveToken at hnone
  cases hl1 : l.last with
  | true =>
      simp only
        [coverageTouchedTokenAt_sourceSet,
         coverageTouchedTokenAt_sourceClear,
         coverageTouchedSourceClear_last,
         coverageTouchedSourceClear_id,
         coverageTouchedSourceClear_dist,
         coverageTouchedSourceSet_id,
         coverageTouchedTokenCode_mk,
         coverageTouchedBirthGhost_value,
         decodeOffset_psi, hpsi1, hpsi2,
         ne_eq, not_true_eq_false, not_false_eq_true,
         and_true, true_and, and_false, false_and, and_self,
         eq_self_iff_true, reduceCtorEq, Option.some.injEq,
         ↓reduceIte, ↓reduceDIte, hl1] at hu hnone
      all_goals
        exact coverageTouched_stay_case kind r gr hR u hu hnone
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [coverageTouchedTokenAt_sourceSet,
           coverageTouchedTokenAt_sourceClear,
           coverageTouchedSourceClear_last,
           coverageTouchedSourceClear_id,
           coverageTouchedSourceClear_dist,
           coverageTouchedSourceSet_id,
           coverageTouchedTokenCode_mk,
           coverageTouchedBirthGhost_value,
           decodeOffset_psi, hpsi1, hpsi2,
           ne_eq, not_true_eq_false, not_false_eq_true,
           and_true, true_and, and_false, false_and, and_self,
           eq_self_iff_true, reduceCtorEq, Option.some.injEq,
           ↓reduceIte, ↓reduceDIte, hl1, hr1] at hu hnone
        all_goals
          exact coverageTouched_stay_case kind r gr hR u hu hnone
    | false =>
      cases hAv : coverageTouchedLiveValue kind l with
      | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : coverageTouchedLiveValue kind r with
            | none =>
                simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
          · cases hBv : coverageTouchedLiveValue kind r with
            | none =>
                simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at hu hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                      | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
      | some a =>
          cases hBv : coverageTouchedLiveValue kind r with
          | none =>
              by_cases h1 : decodeOffset psi (tokenCode a) = 1
              · simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
              · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1, h2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1, h2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
          | some b =>
              by_cases hm1 : decodeOffset psi (tokenCode b) = -1
              · simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1] at hu hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                  | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
              · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1, hm2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1, hm2] at hu hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (coverageTouched_stay_case kind l gl hL _ hAv) hvl hnone)
                    | (subst hu; exact coverageTouchedBump_owner_of_valid kind r _ _ (Option.some_ne_none _) hvl hnone)


private theorem coverageTouchedDecodeUpper
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) :
    decodeOffset psi (tokenCode t) ≤
      ((psi : Nat) : Int) := by
  have hc :=
    decodeOffset_valid psi (by omega) (tokenCode t)
  unfold ValidOffset at hc
  rcases hc with hc | hc <;> omega




/--
At the first C_d site a valid selected-color token has offset +psi.
Every genuine right move writes 1-psi or c-1 < psi, so such a token can only
come from the responder stay branch.
-/
private theorem coverageTouchedResponderFirstBranches
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hR : CoverageTouchedShadowReady kind r gr)
    (t : TokenData psi)
    (htok :
      tokenAt kind
        (coverageTouchedMoveToken
          hpsi kind l r).2 = some t)
    (hoff :
      decodeOffset psi (tokenCode t) =
        ((psi : Nat) : Int)) :
    (coverageTouchedGhostMoveToken
      hpsi kind step site l r gl gr).right ≠ none := by
  classical
  have hpsi1 : ¬ (((psi : Nat) : Int) = 1) := by omega
  have hpsi2 : (2 : Int) ≤ ((psi : Nat) : Int) := by omega
  intro hnone
  unfold coverageTouchedMoveToken at htok
  unfold coverageTouchedGhostMoveToken at hnone
  cases hl1 : l.last with
  | true =>
      simp only
        [coverageTouchedTokenAt_sourceSet,
         coverageTouchedTokenAt_sourceClear,
         coverageTouchedSourceClear_last,
         coverageTouchedSourceClear_id,
         coverageTouchedSourceClear_dist,
         coverageTouchedSourceSet_id,
         coverageTouchedTokenCode_mk,
         coverageTouchedBirthGhost_value,
         decodeOffset_psi, hpsi1, hpsi2,
         ne_eq, not_true_eq_false, not_false_eq_true,
         and_true, true_and, and_false, false_and, and_self,
         eq_self_iff_true, reduceCtorEq, Option.some.injEq,
         ↓reduceIte, ↓reduceDIte, hl1] at htok hnone
      all_goals
        exact coverageTouched_stay_case kind r gr hR t htok hnone
  | false =>
    cases hr1 : r.last with
    | true =>
        simp only
          [coverageTouchedTokenAt_sourceSet,
           coverageTouchedTokenAt_sourceClear,
           coverageTouchedSourceClear_last,
           coverageTouchedSourceClear_id,
           coverageTouchedSourceClear_dist,
           coverageTouchedSourceSet_id,
           coverageTouchedTokenCode_mk,
           coverageTouchedBirthGhost_value,
           decodeOffset_psi, hpsi1, hpsi2,
           ne_eq, not_true_eq_false, not_false_eq_true,
           and_true, true_and, and_false, false_and, and_self,
           eq_self_iff_true, reduceCtorEq, Option.some.injEq,
           ↓reduceIte, ↓reduceDIte, hl1, hr1] at htok hnone
        all_goals
          exact coverageTouched_stay_case kind r gr hR t htok hnone
    | false =>
      cases hAv : coverageTouchedLiveValue kind l with
      | none =>
          by_cases hd : l.dist.val = tokenD' psi kind
          · cases hBv : coverageTouchedLiveValue kind r with
            | none =>
                simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd] at htok hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1] at htok hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at htok hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at htok hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
          · cases hBv : coverageTouchedLiveValue kind r with
            | none =>
                simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd] at htok hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
            | some b =>
                by_cases hm1 : decodeOffset psi (tokenCode b) = -1
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1] at htok hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
                · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at htok hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
                  · simp only
                      [coverageTouchedTokenAt_sourceSet,
                       coverageTouchedTokenAt_sourceClear,
                       coverageTouchedSourceClear_last,
                       coverageTouchedSourceClear_id,
                       coverageTouchedSourceClear_dist,
                       coverageTouchedSourceSet_id,
                       coverageTouchedTokenCode_mk,
                       coverageTouchedBirthGhost_value,
                       decodeOffset_psi, hpsi1, hpsi2,
                       ne_eq, not_true_eq_false, not_false_eq_true,
                       and_true, true_and, and_false, false_and, and_self,
                       eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                       ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hd, hm1, hm2] at htok hnone
                    all_goals
                      first
                      | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                      | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
      | some a =>
          cases hBv : coverageTouchedLiveValue kind r with
          | none =>
              by_cases h1 : decodeOffset psi (tokenCode a) = 1
              · simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1] at htok hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
              · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode a)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1, h2] at htok hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, h1, h2] at htok hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
          | some b =>
              by_cases hm1 : decodeOffset psi (tokenCode b) = -1
              · simp only
                  [coverageTouchedTokenAt_sourceSet,
                   coverageTouchedTokenAt_sourceClear,
                   coverageTouchedSourceClear_last,
                   coverageTouchedSourceClear_id,
                   coverageTouchedSourceClear_dist,
                   coverageTouchedSourceSet_id,
                   coverageTouchedTokenCode_mk,
                   coverageTouchedBirthGhost_value,
                   decodeOffset_psi, hpsi1, hpsi2,
                   ne_eq, not_true_eq_false, not_false_eq_true,
                   and_true, true_and, and_false, false_and, and_self,
                   eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                   ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1] at htok hnone
                all_goals
                  first
                  | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                  | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
              · by_cases hm2 : decodeOffset psi (tokenCode b) ≤ -2
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1, hm2] at htok hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)
                · simp only
                    [coverageTouchedTokenAt_sourceSet,
                     coverageTouchedTokenAt_sourceClear,
                     coverageTouchedSourceClear_last,
                     coverageTouchedSourceClear_id,
                     coverageTouchedSourceClear_dist,
                     coverageTouchedSourceSet_id,
                     coverageTouchedTokenCode_mk,
                     coverageTouchedBirthGhost_value,
                     decodeOffset_psi, hpsi1, hpsi2,
                     ne_eq, not_true_eq_false, not_false_eq_true,
                     and_true, true_and, and_false, false_and, and_self,
                     eq_self_iff_true, reduceCtorEq, Option.some.injEq,
                     ↓reduceIte, ↓reduceDIte, hl1, hr1, hAv, hBv, hm1, hm2] at htok hnone
                  all_goals
                    first
                    | exact coverageTouched_stay_case kind r gr hR _ hBv hnone
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decodeOffset_negPsiPlusOne] at hoff; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; have hup := coverageTouchedDecodeUpper hpsi a; omega)
                    | (subst htok; rw [coverageTouchedTokenCode_mk, decode_encode] at hoff; omega)


/-! ## Cyclic window geometry -/








private theorem coverageTouchedShiftRightZero
    {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n) :
    shiftRight ring x 0 = x := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt x.isLt]








private theorem coverageTouchedShiftRightAdd
    {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n)
    (a b : Nat) :
    shiftRight ring (shiftRight ring x a) b =
      shiftRight ring x (a + b) := by
  apply Fin.ext
  change
    (((x.val + a) % n + b) % n) =
      (x.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]








private theorem coverageTouchedShiftRightSucc
    {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n)
    (d : Nat) :
    shiftRight ring x (d + 1) =
      ring.rightNeighbor (shiftRight ring x d) := by
  calc
    shiftRight ring x (d + 1) =
        shiftRight ring (shiftRight ring x d) 1 :=
      (coverageTouchedShiftRightAdd
        ring x d 1).symm
    _ = ring.rightNeighbor
        (shiftRight ring x d) := rfl








private theorem coverageTouchedRightNeighborInjective
    {n : Nat}
    (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega








private theorem coverageTouchedCd_two_le_n
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
    let x0 : Fin (2 * psi) := ⟨0, by omega⟩
    let x1 : Fin (2 * psi) := ⟨1, by omega⟩
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








private theorem coverageTouchedRightNeighborNeSelf
    {n : Nat}
    (hn2 : 2 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      have he := e.isLt
      omega
    rw [heq, Nat.mod_self] at hv
    omega








private theorem coverageTouchedRightInterior
    {n psi : Nat}
    (ring : DirectedRing n)
    (k e : Fin n)
    (x : Fin (2 * psi))
    (he : e = shiftRight ring k x.val)
    (hx : x.val + 1 < 2 * psi) :
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) := by
  let y : Fin (2 * psi) :=
    ⟨x.val + 1, hx⟩
  refine ⟨y, ?_⟩
  subst e
  dsimp only [y]
  exact
    (coverageTouchedShiftRightSucc
      ring k x.val).symm








private theorem coverageTouchedLeftInterior
    {n psi : Nat}
    (ring : DirectedRing n)
    (k e : Fin n)
    (x : Fin (2 * psi))
    (hr :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hx : 0 < x.val) :
    Lemma4InWindow ring k psi e := by
  let y : Fin (2 * psi) :=
    ⟨x.val - 1, by omega⟩
  refine ⟨y, ?_⟩
  apply coverageTouchedRightNeighborInjective ring
  calc
    ring.rightNeighbor e =
        shiftRight ring k x.val := hr
    _ = ring.rightNeighbor
        (shiftRight ring k (x.val - 1)) := by
      have hs :=
        coverageTouchedShiftRightSucc
          ring k (x.val - 1)
      have hx1 : x.val - 1 + 1 = x.val := by
        omega
      rw [hx1] at hs
      exact hs
    _ = ring.rightNeighbor
        (shiftRight ring k y.val) := by
      rfl








/-! ## The two C_d boundary facts -/








private theorem coverageTouchedTokenDLt
    {psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind) :
    tokenD' psi kind < 2 * psi := by
  cases kind <;>
    simp only [tokenD'] <;>
    omega








private theorem coverageTouchedNegSuccMod
    {psi m : Nat}
    (hpsi : 2 <= psi)
    (hm : m < 2 * psi) :
    (Int.negSucc m) %
        (((2 * psi : Nat)) : Int) =
      (((2 * psi - (m + 1) : Nat)) : Int) := by
  change
    Int.subNatNat
        (2 * psi)
        ((m % (2 * psi)).succ) =
      (((2 * psi - (m + 1) : Nat)) : Int)
  rw [Nat.mod_eq_of_lt hm]
  rw [Int.subNatNat_of_sub_eq_zero (by omega)]








private theorem coverageTouchedFirstTargetPositive
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hpos :
      0 < decodeOffset psi (tokenCode t))
    (hle :
      decodeOffset psi (tokenCode t) <=
        ((psi : Nat) : Int)) :
    tokenTargetCoordinate kind q t =
      decodeOffset psi (tokenCode t) := by
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hpos hle
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
              ((psi : Nat) : Int) +
                    ((m : Nat) : Int) +
                    ((psi : Nat) : Int) =
                ((m : Nat) : Int) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right,
            Int.emod_eq_of_lt (by omega) (by omega)]
  | negSucc m =>
      rw [hc] at hpos
      simp only [Int.negSucc_eq] at hpos
      omega








private theorem coverageTouchedFirstTargetNegative
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hlow :
      1 - ((psi : Nat) : Int) <=
        decodeOffset psi (tokenCode t))
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) <
      tokenTargetCoordinate kind q t := by
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hneg
      simp only [Int.ofNat_eq_coe] at hneg
      omega
  | negSucc m =>
      rw [hc] at hlow hneg
      simp only [Int.negSucc_eq] at hlow hneg
      have hm2 : m + 2 <= psi := by
        omega
      let u : Nat := 2 * psi - (m + 1)
      have hups : psi < u := by
        dsimp [u]
        omega
      have hult : u < 2 * psi := by
        dsimp [u]
        omega
      cases kind with
      | black =>
          simp only [tokenD'] at hdist
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hdist, hc]
          rw [Int.natCast_zero, Int.zero_add, Int.add_zero]
          rw [coverageTouchedNegSuccMod
            hpsi (by omega : m < 2 * psi)]
          exact_mod_cast hups
      | white =>
          simp only [tokenD'] at hdist
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hdist, hc]
          have hcInt :
              Int.negSucc m =
                -(((m + 1 : Nat)) : Int) := by
            omega
          have hnum :
              ((psi : Nat) : Int) +
                    Int.negSucc m +
                    ((psi : Nat) : Int) =
                ((u : Nat) : Int) := by
            rw [hcInt]
            dsimp [u]
            omega
          rw [hnum]
          change
            (((u % (2 * psi) : Nat)) : Int) >
              ((psi : Nat) : Int)
          rw [Nat.mod_eq_of_lt hult]
          exact_mod_cast hups








private theorem coverageTouchedLastDistPlusD
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








private theorem coverageTouchedLastTargetPositive
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hpos :
      0 < decodeOffset psi (tokenCode t))
    (hle :
      decodeOffset psi (tokenCode t) <=
        ((psi : Nat) : Int)) :
    tokenTargetCoordinate kind q t <
      ((psi : Nat) : Int) := by
  have hsum :=
    coverageTouchedLastDistPlusD
      hpsi kind q hdist
  have hsumInt :
      (((q.dist.val + tokenD' psi kind :
        Nat)) : Int) =
        (((2 * psi - 1 : Nat)) : Int) :=
    congrArg (fun a : Nat => (a : Int)) hsum
  cases hc :
      decodeOffset psi (tokenCode t) with
  | ofNat m =>
      rw [hc] at hpos hle
      simp only [Int.ofNat_eq_coe] at hpos hle
      let u : Nat := m - 1
      have hult : u < psi := by
        dsimp [u]
        omega
      have hnum :
          ((q.dist.val : Nat) : Int) +
                ((m : Nat) : Int) +
                ((tokenD' psi kind : Nat) : Int) =
            (((2 * psi + u : Nat)) : Int) := by
        simp only [Int.natCast_add] at hsumInt
        dsimp [u]
        omega
      unfold tokenTargetCoordinate
      rw [hc]
      simp only [Int.ofNat_eq_coe]
      rw [hnum]
      change
        ((((2 * psi + u) % (2 * psi) :
          Nat)) : Int) <
          ((psi : Nat) : Int)
      have hm :
          (2 * psi + u) % (2 * psi) = u := by
        simp
          [Nat.add_mod,
            Nat.mod_eq_of_lt
              (by omega : u < 2 * psi)]
      rw [hm]
      exact_mod_cast hult
  | negSucc m =>
      rw [hc] at hpos
      simp only [Int.negSucc_eq] at hpos
      omega








private theorem coverageTouchedLastTargetNegative
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
      1 - ((psi : Nat) : Int) <=
        decodeOffset psi (tokenCode t))
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) <=
      tokenTargetCoordinate kind q t := by
  have hsum :=
    coverageTouchedLastDistPlusD
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
      simp only [Int.ofNat_eq_coe] at hneg
      omega
  | negSucc m =>
      rw [hc] at hlow hneg
      simp only [Int.negSucc_eq] at hlow hneg
      have hm2 : m + 2 <= psi := by
        omega
      let u : Nat := 2 * psi - m - 2
      have hups : psi <= u := by
        dsimp [u]
        omega
      have hult : u < 2 * psi := by
        dsimp [u]
        omega
      have hcInt :
          Int.negSucc m =
            -(((m + 1 : Nat)) : Int) := by
        omega
      have hnum :
          ((q.dist.val : Nat) : Int) +
                decodeOffset psi (tokenCode t) +
                ((tokenD' psi kind : Nat) : Int) =
            ((u : Nat) : Int) := by
        rw [hc, hcInt]
        simp only [Int.natCast_add] at hsumInt
        dsimp [u]
        omega
      unfold tokenTargetCoordinate
      rw [hnum]
      change
        ((psi : Nat) : Int) <=
          (((u % (2 * psi) : Nat)) : Int)
      rw [Nat.mod_eq_of_lt hult]
      exact_mod_cast hups








private theorem coverageTouchedNoValidLast
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    Not
      (ValidToken kind C
        (shiftRight ring k (2 * psi - 1))) := by
  intro hvalid
  let x : Fin (2 * psi) :=
    ⟨2 * psi - 1, by omega⟩
  have hd := hCd x
  dsimp only [x] at hd
  unfold ValidToken at hvalid
  cases ht :
      tokenAt kind
        (C (shiftRight ring k (2 * psi - 1))) with
  | none =>
      rw [ht] at hvalid
      exact hvalid
  | some t =>
      rw [ht] at hvalid
      dsimp only at hvalid
      have hc :=
        decodeOffset_valid
          psi (by omega) (tokenCode t)
      rcases hc with hcneg | hcpos
      · have htgt :=
          coverageTouchedLastTargetNegative
            hpsi kind
            (C (shiftRight ring k (2 * psi - 1))) t
            hd.1 hcneg.1 (by omega)
        rcases hvalid with hp | hn
        · omega
        · omega
      · have htgt :=
          coverageTouchedLastTargetPositive
            hpsi kind
            (C (shiftRight ring k (2 * psi - 1))) t
            hd.1 (by omega) hcpos.2
        rcases hvalid with hp | hn
        · omega
        · omega








private theorem coverageTouchedValidFirstOffsetPsi
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C)
    (hvalid : ValidToken kind C k) :
    exists t : TokenData psi,
      And
        (tokenAt kind (C k) = some t)
        (decodeOffset psi (tokenCode t) =
          ((psi : Nat) : Int)) := by
  let x : Fin (2 * psi) := ⟨0, by omega⟩
  have hd := hCd x
  dsimp only [x] at hd
  rw [coverageTouchedShiftRightZero ring k] at hd
  have hdist := hd.1
  rw [Nat.zero_add,
    Nat.mod_eq_of_lt
      (coverageTouchedTokenDLt hpsi kind)] at hdist
  unfold ValidToken at hvalid
  cases ht : tokenAt kind (C k) with
  | none =>
      rw [ht] at hvalid
      exact False.elim hvalid
  | some t =>
      rw [ht] at hvalid
      dsimp only at hvalid
      have hc :=
        decodeOffset_valid
          psi (by omega) (tokenCode t)
      refine ⟨t, rfl, ?_⟩
      rcases hc with hcneg | hcpos
      · have htgt :=
          coverageTouchedFirstTargetNegative
            hpsi kind (C k) t
            hdist hcneg.1 (by omega)
        rcases hvalid with hp | hn
        · omega
        · omega
      · have htgt :=
          coverageTouchedFirstTargetPositive
            hpsi kind (C k) t
            hdist (by omega) hcpos.2
        rcases hvalid with hp | hn
        · omega
        · omega








/-! ## Post validity transported to the selected MoveToken row -/








private theorem coverageTouchedSelectedValidLeft
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e) :
    CoverageTouchedValidAt kind
      (coverageTouchedSelectedOutput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1 := by
  have h0 :=
    coverageTouched_validAt_of_validToken
      kind
      (ghostStep hpsi ring step G e).phys
      e hvalid
  rw [coverageTouchedStepLeftState
    hpsi ring step G e] at h0
  have hf :=
    coverageTouchedPplSelectedFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  exact
    (coverageTouched_validAt_transport
      kind
      (ppl hpsi
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1
      (coverageTouchedSelectedOutput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1
      hf.1 hf.2.1).mp h0








private theorem coverageTouchedSelectedValidRight
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e)
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)) :
    CoverageTouchedValidAt kind
      (coverageTouchedSelectedOutput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2 := by
  have h0 :=
    coverageTouched_validAt_of_validToken
      kind
      (ghostStep hpsi ring step G e).phys
      (ring.rightNeighbor e) hvalid
  rw [coverageTouchedStepRightState
    hpsi ring step G e hne] at h0
  have hf :=
    coverageTouchedPplSelectedFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  exact
    (coverageTouched_validAt_transport
      kind
      (ppl hpsi
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2
      (coverageTouchedSelectedOutput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2
      hf.2.2.1 hf.2.2.2).mp h0








private theorem coverageTouchedOwnerLeft
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hnon :
      (coverageTouchedMovedPair
        hpsi ring step G e kind).left ≠ none) :
    exists z : GhostToken n psi,
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) e = some z := by
  cases hm :
      (coverageTouchedMovedPair
        hpsi ring step G e kind).left with
  | none =>
      exact False.elim (hnon hm)
  | some z =>
      refine ⟨z, ?_⟩
      rw [coverageTouchedGhostTokenAtStep]
      simp [coverageTouchedSetTwo, hm]








private theorem coverageTouchedOwnerRight
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e)
    (hnon :
      (coverageTouchedMovedPair
        hpsi ring step G e kind).right ≠ none) :
    exists z : GhostToken n psi,
      ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) = some z := by
  cases hm :
      (coverageTouchedMovedPair
        hpsi ring step G e kind).right with
  | none =>
      exact False.elim (hnon hm)
  | some z =>
      refine ⟨z, ?_⟩
      rw [coverageTouchedGhostTokenAtStep]
      simp [coverageTouchedSetTwo, hne, hm]








/-! ## Endpoint assemblers -/








private theorem coverageTouchedInitiatorEndpoint
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (hwin : Lemma4InWindow ring k psi e)
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e) :
    exists z : GhostToken n psi,
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) e = some z := by
  have hn2 :=
    coverageTouchedCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :=
    coverageTouchedRightNeighborNeSelf
      hn2 ring e
  rcases hwin with ⟨x, hx⟩
  by_cases hinterior : x.val + 1 < 2 * psi
  · have hwinL :
        Lemma4InWindow ring k psi e :=
      ⟨x, hx⟩
    have hwinR :
        Lemma4InWindow ring k psi
          (ring.rightNeighbor e) :=
      coverageTouchedRightInterior
        ring k e x hx hinterior
    have hL :=
      coverageTouchedShadowReadyLeft
        hpsi ring k kind step G e
        hCd hCd' hcovered hsound hwinL
    have hR :=
      coverageTouchedShadowReadyRight
        hpsi ring k kind step G e hne
        hCd hCd' hcovered hsound hwinR
    have hv :=
      coverageTouchedSelectedValidLeft
        hpsi ring step G e kind hvalid
    have hnon :=
      coverageTouchedInitiatorBranches
        hpsi kind step e
        (coverageTouchedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1
        (coverageTouchedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G
          (ring.rightNeighbor e))
        hL hR
        (by
          simpa [coverageTouchedMoveToken_eq,
            coverageTouchedSelectedOutput]
            using hv)
    exact
      coverageTouchedOwnerLeft
        hpsi ring step G e kind hnon
  · have hxlast : x.val = 2 * psi - 1 := by
      have hxlt := x.isLt
      omega
    have he :
        e =
          shiftRight ring k (2 * psi - 1) := by
      rw [hxlast] at hx
      exact hx
    have hvalidLast :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys
          (shiftRight ring k (2 * psi - 1)) := by
      rw [← he]
      exact hvalid
    exact
      False.elim
        (coverageTouchedNoValidLast
          hpsi ring k kind
          (ghostStep hpsi ring step G e).phys
          hCd' hvalidLast)








private theorem coverageTouchedResponderEndpoint
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)) :
    exists z : GhostToken n psi,
      ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) = some z := by
  have hn2 :=
    coverageTouchedCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hne :=
    coverageTouchedRightNeighborNeSelf
      hn2 ring e
  rcases hwin with ⟨x, hx⟩
  by_cases hinterior : 0 < x.val
  · have hwinL :=
      coverageTouchedLeftInterior
        ring k e x hx hinterior
    have hwinR :
        Lemma4InWindow ring k psi
          (ring.rightNeighbor e) :=
      ⟨x, hx⟩
    have hL :=
      coverageTouchedShadowReadyLeft
        hpsi ring k kind step G e
        hCd hCd' hcovered hsound hwinL
    have hR :=
      coverageTouchedShadowReadyRight
        hpsi ring k kind step G e hne
        hCd hCd' hcovered hsound hwinR
    have hv :=
      coverageTouchedSelectedValidRight
        hpsi ring step G e kind hne hvalid
    have hnon :=
      coverageTouchedResponderBranches
        hpsi kind step e
        (coverageTouchedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1
        (coverageTouchedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G
          (ring.rightNeighbor e))
        hL hR
        (by
          simpa [coverageTouchedMoveToken_eq,
            coverageTouchedSelectedOutput]
            using hv)
    exact
      coverageTouchedOwnerRight
        hpsi ring step G e kind hne hnon
  · have hx0 : x.val = 0 := by omega
    have hrk :
        ring.rightNeighbor e = k := by
      rw [hx0] at hx
      exact
        hx.trans
          (coverageTouchedShiftRightZero
            ring k)
    have hvalidK :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys k := by
      rw [← hrk]
      exact hvalid
    obtain ⟨t, htokK, hoff⟩ :=
      coverageTouchedValidFirstOffsetPsi
        hpsi ring k kind
        (ghostStep hpsi ring step G e).phys
        hCd' hvalidK
    have htokR :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
          some t := by
      rw [hrk]
      exact htokK
    have hs :=
      coverageTouchedStepRightState
        hpsi ring step G e hne
    have hp :
        tokenAt kind
            (ppl hpsi
              (G.phys e)
              (G.phys (ring.rightNeighbor e))).2 =
          some t := by
      have hq :=
        congrArg (tokenAt kind) hs
      exact hq.symm.trans htokR
    have hf :=
      coverageTouchedPplSelectedFrame
        hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    have htokSel :
        tokenAt kind
            (coverageTouchedSelectedOutput hpsi kind
              (G.phys e)
              (G.phys (ring.rightNeighbor e))).2 =
          some t :=
      hf.2.2.1.symm.trans hp
    have hR :=
      coverageTouchedShadowReadyRight
        hpsi ring k kind step G e hne
        hCd hCd' hcovered hsound
        ⟨x, hx⟩
    have hnon :=
      coverageTouchedResponderFirstBranches
        hpsi kind step e
        (coverageTouchedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1
        (coverageTouchedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G
          (ring.rightNeighbor e))
        hR t
        (by
          simpa [coverageTouchedMoveToken_eq,
            coverageTouchedSelectedOutput]
            using htokSel)
        hoff
    exact
      coverageTouchedOwnerRight
        hpsi ring step G e kind hne hnon








theorem lemma4CoverageTouchedCoverageSound_proved :
    Lemma4CoverageTouchedCoverageSound := by
  intro n psi kappa hpsi ring k kind step G e i
  intro hCd hCd' hcovered hsound htouched hiwin hvalid
  rcases htouched with hie | hir
  · subst i
    exact
      coverageTouchedInitiatorEndpoint
        hpsi ring k kind step G e
        hCd hCd' hcovered hsound
        hiwin hvalid
  · subst i
    exact
      coverageTouchedResponderEndpoint
        hpsi ring k kind step G e
        hCd hCd' hcovered hsound
        hiwin hvalid








end PPL








#print axioms PPL.lemma4CoverageTouchedCoverageSound_proved
