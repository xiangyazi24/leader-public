import Leader.PPL.TokenCompletion.CoverageRows


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
This file closes the whole-run GhostSound leaf.  The remaining three leaves
are kept explicit at the final adapter; no converse-to-GhostSound statement is
silently assumed.


The proof mirrors only the proof-only selected-colour ghost row and Algorithm 3
through public aliases sourceSet/sourceClear/sourceBirth.  It never names an
inaccessible implementation declaration.
-/


/-! ## Literal public-name mirrors of the selected token row -/


private def coverageLeavesBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def coverageLeavesMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def coverageLeavesLocalValid {psi kappa : Nat}
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


private instance instDecidableCoverageLeavesLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (coverageLeavesLocalValid kind q t) := by
  unfold coverageLeavesLocalValid
  infer_instance


private def coverageLeavesSetToken {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def coverageLeavesClearInvalid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if coverageLeavesLocalValid kind q t then
        q
      else
        coverageLeavesSetToken kind q none


private def coverageLeavesLeaderBirth {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


private theorem coverageLeavesSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      coverageLeavesSetToken kind q t := by
  cases kind <;> rfl


private theorem coverageLeavesSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    sourceClear kind q =
      coverageLeavesClearInvalid kind q := by
  cases kind <;> rfl


private theorem coverageLeavesSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = coverageLeavesLeaderBirth q := by
  rfl


private def coverageLeavesNegTurnNext {psi : Nat}
    (hpsi : 2 <= psi) (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    coverageLeavesMkToken
      (offsetPsiCode psi hpsi)
      (coverageLeavesBitToFin (!sourceBit))
      (coverageLeavesBitToFin sourceBit)
  else
    coverageLeavesMkToken
      (offsetPsiCode psi hpsi)
      (coverageLeavesBitToFin sourceBit)
      (0 : Fin 2)


private def coverageLeavesMoveToken
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
            (coverageLeavesMkToken
              (offsetPsiCode psi hpsi)
              (coverageLeavesBitToFin (!l.id))
              (coverageLeavesBitToFin l.id)))
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
                coverageLeavesNegTurnNext
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
                    (coverageLeavesMkToken
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
                (coverageLeavesMkToken
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
                (coverageLeavesMkToken
                  nextOffset t.1.2 t.2))
          let l := sourceSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)


private theorem coverageLeavesMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa) :
    coverageLeavesMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl


private def coverageLeavesLiveShadow
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
              (coverageLeavesLocalValid kind q t) then
            some z
          else
            none


private def coverageLeavesLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if coverageLeavesLocalValid kind q t then
        some t
      else
        none


private def coverageLeavesBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      coverageLeavesMkToken
        (offsetPsiCode psi hpsi)
        (coverageLeavesBitToFin (!idBit))
        (coverageLeavesBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def coverageLeavesBumpTo
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
        if coverageLeavesLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def coverageLeavesGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := coverageLeavesLiveValue kind l
  let rv0 := coverageLeavesLiveValue kind r
  let gl0 := coverageLeavesLiveShadow kind l gl
  let gr0 := coverageLeavesLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (coverageLeavesBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (coverageLeavesBirthGhost
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
            coverageLeavesMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            coverageLeavesBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            coverageLeavesMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            coverageLeavesBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some t =>
              let c := decodeOffset psi (tokenCode t)
              if hm1 : c = -1 then
                let next :=
                  coverageLeavesNegTurnNext hpsi l.id t
                let b :=
                  coverageLeavesBumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  coverageLeavesMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  coverageLeavesBumpTo kind l next gr0
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
                coverageLeavesNegTurnNext hpsi l.id t
              let b :=
                coverageLeavesBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                coverageLeavesMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                coverageLeavesBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩


private def coverageLeavesPrelude
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


private def coverageLeavesSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := coverageLeavesPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2


private def coverageLeavesSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := coverageLeavesSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2


private def coverageLeavesSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k


private def coverageLeavesMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    coverageLeavesSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  coverageLeavesGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))


private theorem coverageLeavesGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      coverageLeavesSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (coverageLeavesMovedPair
          hpsi ring step G e kind).left
        (coverageLeavesMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl


/-! ## A local owner-soundness relation -/


private def CoverageLeavesOptionSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) : Prop :=
  forall z : GhostToken n psi,
    g = some z ->
    And
      (tokenAt kind q = some z.value)
      (coverageLeavesLocalValid kind q z.value)


private def CoverageLeavesAlignedSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi))
    (g : Option (GhostToken n psi)) : Prop :=
  And
    (tokenAt kind q = v)
    (CoverageLeavesOptionSound kind q g)


private theorem coverageLeavesLocalValid_of_dist_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t : TokenData psi)
    (hdist : q'.dist = q.dist)
    (hvalid : coverageLeavesLocalValid kind q t) :
    coverageLeavesLocalValid kind q' t := by
  unfold coverageLeavesLocalValid at hvalid ⊢
  unfold tokenTargetCoordinate at hvalid ⊢
  rw [hdist]
  exact hvalid


private theorem coverageLeavesSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q t) = t := by
  rw [coverageLeavesSourceSet_eq]
  cases kind <;> rfl


private theorem coverageLeavesSourceSet_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).dist = q.dist := by
  rw [coverageLeavesSourceSet_eq]
  cases kind <;> rfl


private theorem coverageLeavesSourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).id = q.id := by
  rw [coverageLeavesSourceSet_eq]
  cases kind <;> rfl


private theorem coverageLeavesSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      coverageLeavesLiveValue kind q := by
  rw [coverageLeavesSourceClear_eq]
  unfold coverageLeavesClearInvalid
    coverageLeavesLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv :
          coverageLeavesLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold coverageLeavesSetToken
        cases kind <;> rfl


private theorem coverageLeavesSourceClear_fields
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
  rw [coverageLeavesSourceClear_eq]
  unfold coverageLeavesClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      exact ⟨rfl, rfl, rfl⟩
  | some t =>
      by_cases hv :
          coverageLeavesLocalValid kind q t
      · simp only [if_pos hv]
        refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial
      · simp only [if_neg hv]
        unfold coverageLeavesSetToken
        cases kind <;>
          exact ⟨rfl, rfl, rfl⟩


private theorem coverageLeavesLiveShadow_aligned
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    CoverageLeavesAlignedSound
      kind
      (sourceClear kind q)
      (coverageLeavesLiveValue kind q)
      (coverageLeavesLiveShadow kind q g) := by
  constructor
  · exact coverageLeavesSourceClear_token kind q
  · unfold CoverageLeavesOptionSound
    intro z hz
    unfold coverageLeavesLiveShadow at hz
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
                  (coverageLeavesLocalValid kind q t)
            · simp only [if_pos hkeep] at hz
              cases hz
              constructor
              · rw [
                  coverageLeavesSourceClear_token,
                  coverageLeavesLiveValue,
                  ht]
                simp only [if_pos hkeep.2, hkeep.1]
              · rw [hkeep.1]
                exact
                  coverageLeavesLocalValid_of_dist_eq
                    kind q (sourceClear kind q) t
                    (coverageLeavesSourceClear_fields
                      kind q).1
                    hkeep.2
            · simp only [if_neg hkeep] at hz
              cases hz


/-- The liveShadow stay branch, with both endpoint soundness conjuncts. -/
private theorem coverageLeavesGhostMoveToken_liveShadow_stay
    {n psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    And
      (CoverageLeavesOptionSound
        kind (sourceClear kind l)
        (coverageLeavesLiveShadow kind l gl))
      (CoverageLeavesOptionSound
        kind (sourceClear kind r)
        (coverageLeavesLiveShadow kind r gr)) := by
  exact
    And.intro
      (coverageLeavesLiveShadow_aligned
        kind l gl).2
      (coverageLeavesLiveShadow_aligned
        kind r gr).2


private theorem coverageLeavesBirth_localValid
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (q : State psi kappa)
    (hdist :
      q.dist.val = tokenD' psi kind) :
    coverageLeavesLocalValid kind q
      (coverageLeavesBirthGhost
        hpsi kind step site idBit).value := by
  let birth :=
    coverageLeavesBirthGhost
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
  unfold coverageLeavesLocalValid
  rw [hcode, htarget]
  exact
    Or.inl
      ⟨by omega, by omega, by omega⟩


private theorem coverageLeavesBirthGhost_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (q : State psi kappa)
    (hdist :
      q.dist.val = tokenD' psi kind) :
    CoverageLeavesOptionSound kind
      (sourceSet kind q
        (some
          (coverageLeavesBirthGhost
            hpsi kind step site idBit).value))
      (some
        (coverageLeavesBirthGhost
          hpsi kind step site idBit)) := by
  let birth :=
    coverageLeavesBirthGhost
      hpsi kind step site idBit
  unfold CoverageLeavesOptionSound
  intro z hz
  cases hz
  constructor
  · exact
      coverageLeavesSourceSet_token
        kind q (some birth.value)
  · apply
      coverageLeavesBirth_localValid
        hpsi kind step site idBit
        (q :=
          sourceSet kind q (some birth.value))
    have hframe :=
      coverageLeavesSourceSet_dist
        kind q (some birth.value)
    have hval :=
      congrArg Fin.val hframe
    exact hval.trans hdist


/-- The birthGhost branch, with the fresh left owner and right live shadow. -/
private theorem coverageLeavesGhostMoveToken_birthGhost
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
      (CoverageLeavesOptionSound kind
        (sourceSet kind l
          (some
            (coverageLeavesBirthGhost
              hpsi kind step site idBit).value))
        (some
          (coverageLeavesBirthGhost
            hpsi kind step site idBit)))
      (CoverageLeavesOptionSound kind
        (sourceClear kind r)
        (coverageLeavesLiveShadow kind r gr)) := by
  exact
    And.intro
      (coverageLeavesBirthGhost_sound
        hpsi kind step site idBit l hdist)
      (coverageLeavesLiveShadow_aligned
        kind r gr).2


private theorem coverageLeavesOptionSound_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    CoverageLeavesOptionSound
      (n := n) kind q none := by
  unfold CoverageLeavesOptionSound
  intro z hz
  cases hz


/--
The bumpTo movement branch.  The first pair is the right-moving orientation
(gone, destination), and the second pair is the left-moving orientation
(destination, gone).
-/
private theorem coverageLeavesGhostMoveToken_bumpTo_move
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
        (CoverageLeavesOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qGone
          (none : Option (GhostToken n psi)))
        (CoverageLeavesOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qDest
          (coverageLeavesBumpTo
            (n := n) (psi := psi) (kappa := kappa)
            kind base next g).live))
      (And
        (CoverageLeavesOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qDest
          (coverageLeavesBumpTo
            (n := n) (psi := psi) (kappa := kappa)
            kind base next g).live)
        (CoverageLeavesOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qGone
          (none : Option (GhostToken n psi)))) := by
  have hnone :
      CoverageLeavesOptionSound
        (n := n) (psi := psi) (kappa := kappa)
        kind qGone
        (none : Option (GhostToken n psi)) :=
    coverageLeavesOptionSound_none
      (n := n) (psi := psi) (kappa := kappa)
      kind qGone
  have hlive :
      CoverageLeavesOptionSound
        (n := n) (psi := psi) (kappa := kappa)
        kind qDest
        (coverageLeavesBumpTo
          (n := n) (psi := psi) (kappa := kappa)
          kind base next g).live := by
    unfold CoverageLeavesOptionSound
    intro z' hz'
    cases hg : g with
    | none =>
        simp only
          [coverageLeavesBumpTo, hg] at hz'
        cases hz'
    | some z =>
        by_cases hv :
            coverageLeavesLocalValid kind base next
        · simp only
            [coverageLeavesBumpTo,
              hg, if_pos hv] at hz'
          cases hz'
          constructor
          · exact htok
          · exact
              coverageLeavesLocalValid_of_dist_eq
                kind base qDest next hdist hv
        · simp only
            [coverageLeavesBumpTo,
              hg, if_neg hv] at hz'
          cases hz'
  exact
    And.intro
      (And.intro hnone hlive)
      (And.intro hlive hnone)


private def coverageLeavesOneResponder
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) : State psi kappa :=
  if r.mode = true ∧ bit ≠ r.id then
    sourceBirth r
  else if r.mode = false then
    { r with id := bit }
  else
    r


private theorem coverageLeavesOneResponder_dist
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) :
    (coverageLeavesOneResponder r bit).dist =
      r.dist := by
  unfold coverageLeavesOneResponder
  by_cases hbirth :
      r.mode = true ∧ bit ≠ r.id
  · rw [if_pos hbirth, coverageLeavesSourceBirth_eq] <;> rfl
  · rw [if_neg hbirth]
    by_cases hmode : r.mode = false
    · rw [if_pos hmode]
    · rw [if_neg hmode]


private def coverageLeavesPhysicalFinish
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
          if hm1 : c = -1 then
            let next :=
              coverageLeavesNegTurnNext
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
                  (coverageLeavesMkToken
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
          coverageLeavesOneResponder r bit
        let r :=
          sourceSet kind r
            (some
              (coverageLeavesMkToken
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
              (coverageLeavesMkToken
                nextOffset t.1.2 t.2))
        let l := sourceSet kind l none
        (l, r)
      else
        moveLeft l r


private def coverageLeavesGhostFinish
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
      if h1 : c = 1 then
        let next :=
          coverageLeavesMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          coverageLeavesBumpTo kind baseR next gl
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          coverageLeavesMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          coverageLeavesBumpTo kind baseR next gl
        ⟨none, b.live, b.done⟩
      else
        match rv with
        | none =>
            ⟨gl, gr, []⟩
        | some tr =>
            let cr :=
              decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                coverageLeavesNegTurnNext
                  hpsi baseL.id tr
              let b :=
                coverageLeavesBumpTo
                  kind baseL next gr
              ⟨b.live, none, b.done⟩
            else if hm2 : cr <= -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                coverageLeavesMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                coverageLeavesBumpTo
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
          if hm1 : cr = -1 then
            let next :=
              coverageLeavesNegTurnNext
                hpsi baseL.id tr
            let b :=
              coverageLeavesBumpTo
                kind baseL next gr
            ⟨b.live, none, b.done⟩
          else if hm2 : cr <= -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              coverageLeavesMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b :=
              coverageLeavesBumpTo
                kind baseL next gr
            ⟨b.live, none, b.done⟩
          else
            ⟨gl, gr, []⟩


private theorem coverageLeavesGhostMoveToken_finish_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (hleft :
      CoverageLeavesAlignedSound
        kind l lv gl)
    (hright :
      CoverageLeavesAlignedSound
        kind r rv gr)
    (hLdist : l.dist = baseL.dist)
    (hRdist : r.dist = baseR.dist)
    (hLid : l.id = baseL.id) :
    let q :=
      coverageLeavesPhysicalFinish
        hpsi kind l r
    let g :=
      coverageLeavesGhostFinish
        hpsi kind baseL baseR lv rv gl gr
    And
      (CoverageLeavesOptionSound
        kind q.1 g.left)
      (CoverageLeavesOptionSound
        kind q.2 g.right) := by
  cases lv with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [coverageLeavesPhysicalFinish,
            coverageLeavesGhostFinish,
            hleft.1, dif_pos h1]
        let next :=
          coverageLeavesMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let bit := tokenBitBool t
        let r1 := coverageLeavesOneResponder r bit
        have hb :=
          coverageLeavesGhostMoveToken_bumpTo_move
            (n := n) (psi := psi) (kappa := kappa)
            kind baseR
            (sourceSet kind l none)
            (sourceSet kind r1 (some next))
            next gl
            (coverageLeavesSourceSet_token
              kind r1 (some next))
            ((coverageLeavesSourceSet_dist
                kind r1 (some next)).trans
              ((coverageLeavesOneResponder_dist
                  r bit).trans hRdist))
        simpa only [next, bit, r1] using hb.1
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [coverageLeavesPhysicalFinish,
              coverageLeavesGhostFinish,
              hleft.1,
              dif_neg h1, dif_pos h2]
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            coverageLeavesMkToken
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
            coverageLeavesGhostMoveToken_bumpTo_move
              (n := n) (psi := psi) (kappa := kappa)
              kind baseR
              (sourceSet kind l none)
              (sourceSet kind r (some next))
              next gl
              (coverageLeavesSourceSet_token
                kind r (some next))
              ((coverageLeavesSourceSet_dist
                  kind r (some next)).trans hRdist)
          simpa only [next] using hb.1
        · cases rv with
          | none =>
              simp only
                [coverageLeavesPhysicalFinish,
                  coverageLeavesGhostFinish,
                  hleft.1, hright.1,
                  dif_neg h1, dif_neg h2]
              exact ⟨hleft.2, hright.2⟩
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi
                      (tokenCode tr) = -1
              · simp only
                  [coverageLeavesPhysicalFinish,
                    coverageLeavesGhostFinish,
                    hleft.1, hright.1,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1]
                rw [hLid]
                let next :=
                  coverageLeavesNegTurnNext
                    hpsi baseL.id tr
                have hb :=
                  coverageLeavesGhostMoveToken_bumpTo_move
                    (n := n) (psi := psi) (kappa := kappa)
                    kind baseL
                    (sourceSet kind r none)
                    (sourceSet kind l (some next))
                    next gr
                    (coverageLeavesSourceSet_token
                      kind l (some next))
                    ((coverageLeavesSourceSet_dist
                        kind l (some next)).trans hLdist)
                simpa only [next] using hb.2
              · by_cases hm2 :
                  decodeOffset psi
                      (tokenCode tr) <= -2
                · simp only
                    [coverageLeavesPhysicalFinish,
                      coverageLeavesGhostFinish,
                      hleft.1, hright.1,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2]
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    coverageLeavesMkToken
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
                    coverageLeavesGhostMoveToken_bumpTo_move
                      (n := n) (psi := psi) (kappa := kappa)
                      kind baseL
                      (sourceSet kind r none)
                      (sourceSet kind l (some next))
                      next gr
                      (coverageLeavesSourceSet_token
                        kind l (some next))
                      ((coverageLeavesSourceSet_dist
                          kind l (some next)).trans hLdist)
                  simpa only [next] using hb.2
                · simp only
                    [coverageLeavesPhysicalFinish,
                      coverageLeavesGhostFinish,
                      hleft.1, hright.1,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]
                  exact ⟨hleft.2, hright.2⟩
  | none =>
      cases rv with
      | none =>
          simp only
            [coverageLeavesPhysicalFinish,
              coverageLeavesGhostFinish,
              hleft.1, hright.1]
          exact ⟨hleft.2, hright.2⟩
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [coverageLeavesPhysicalFinish,
                coverageLeavesGhostFinish,
                hleft.1, hright.1,
                dif_pos hm1]
            rw [hLid]
            let next :=
              coverageLeavesNegTurnNext
                hpsi baseL.id tr
            have hb :=
              coverageLeavesGhostMoveToken_bumpTo_move
                (n := n) (psi := psi) (kappa := kappa)
                kind baseL
                (sourceSet kind r none)
                (sourceSet kind l (some next))
                next gr
                (coverageLeavesSourceSet_token
                  kind l (some next))
                ((coverageLeavesSourceSet_dist
                    kind l (some next)).trans hLdist)
            simpa only [next] using hb.2
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [coverageLeavesPhysicalFinish,
                  coverageLeavesGhostFinish,
                  hleft.1, hright.1,
                  dif_neg hm1, dif_pos hm2]
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                coverageLeavesMkToken
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
                coverageLeavesGhostMoveToken_bumpTo_move
                  (n := n) (psi := psi) (kappa := kappa)
                  kind baseL
                  (sourceSet kind r none)
                  (sourceSet kind l (some next))
                  next gr
                  (coverageLeavesSourceSet_token
                    kind l (some next))
                  ((coverageLeavesSourceSet_dist
                      kind l (some next)).trans hLdist)
              simpa only [next] using hb.2
            · simp only
                [coverageLeavesPhysicalFinish,
                  coverageLeavesGhostFinish,
                  hleft.1, hright.1,
                  dif_neg hm1, dif_neg hm2]
              exact ⟨hleft.2, hright.2⟩


private theorem coverageLeavesGhostMoveToken_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    let q := moveToken hpsi kind l r
    let g :=
      coverageLeavesGhostMoveToken
        hpsi kind step site l r gl gr
    And
      (CoverageLeavesOptionSound kind q.1 g.left)
      (CoverageLeavesOptionSound kind q.2 g.right) := by
  classical
  dsimp only
  rw [← coverageLeavesMoveToken_eq hpsi kind l r]

  let l0 := sourceClear kind l
  let r0 := sourceClear kind r
  let lv0 := coverageLeavesLiveValue kind l
  let rv0 := coverageLeavesLiveValue kind r
  let gl0 := coverageLeavesLiveShadow kind l gl
  let gr0 := coverageLeavesLiveShadow kind r gr

  have hL0 :
      CoverageLeavesAlignedSound
        kind l0 lv0 gl0 := by
    simpa only [l0, lv0, gl0] using
      coverageLeavesLiveShadow_aligned
        kind l gl
  have hR0 :
      CoverageLeavesAlignedSound
        kind r0 rv0 gr0 := by
    simpa only [r0, rv0, gr0] using
      coverageLeavesLiveShadow_aligned
        kind r gr
  have hL0fields :=
    coverageLeavesSourceClear_fields kind l
  have hR0fields :=
    coverageLeavesSourceClear_fields kind r
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
      coverageLeavesBirthGhost
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
        CoverageLeavesAlignedSound
          kind l1 lv1 gl1 := by
      by_cases hbirth : hb
      · have hdist0 :
            l0.dist.val = tokenD' psi kind := by
          have hval :=
            congrArg Fin.val hL0dist
          exact hval.trans hbirth.1
        have hpair :=
          coverageLeavesGhostMoveToken_birthGhost
            hpsi kind step site l.id
            l0 r gr hdist0
        simp only
          [l1, lv1, gl1, if_pos hbirth]
        exact
          And.intro
            (coverageLeavesSourceSet_token
              kind l0 (some birth.value))
            hpair.1
      · simpa only
          [l1, lv1, gl1, if_neg hbirth]
          using hL0

    have hL1dist : l1.dist = l.dist := by
      by_cases hbirth : hb
      · simp only [l1, if_pos hbirth]
        exact
          (coverageLeavesSourceSet_dist
            kind l0 (some birth.value)).trans
            hL0dist
      · simpa only [l1, if_neg hbirth]
          using hL0dist

    have hL1id : l1.id = l.id := by
      by_cases hbirth : hb
      · simp only [l1, if_pos hbirth]
        exact
          (coverageLeavesSourceSet_id
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
        CoverageLeavesAlignedSound
          kind l2 lv2 gl2 := by
      by_cases hcol : collide
      · simp only
          [l2, lv2, gl2, if_pos hcol]
        exact
          And.intro
            (coverageLeavesSourceSet_token
              kind l1 none)
            (coverageLeavesOptionSound_none
              kind (sourceSet kind l1 none))
      · simpa only
          [l2, lv2, gl2, if_neg hcol]
          using hL1

    have hL2dist : l2.dist = l.dist := by
      by_cases hcol : collide
      · simp only [l2, if_pos hcol]
        exact
          (coverageLeavesSourceSet_dist
            kind l1 none).trans hL1dist
      · simpa only [l2, if_neg hcol]
          using hL1dist

    have hL2id : l2.id = l.id := by
      by_cases hcol : collide
      · simp only [l2, if_pos hcol]
        exact
          (coverageLeavesSourceSet_id
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
        coverageLeavesMoveToken hpsi kind l r =
          coverageLeavesPhysicalFinish
            hpsi kind l2 r0 := by
      by_cases hbirth : hb
      · have hbirth0 :=
          hBirthPhysIff.mpr hbirth
        by_cases hcol : collide
        · have hcol0 :=
            hCollPhysIff.mpr hcol
          simp only
            [l1, l0, r0, birth,
              coverageLeavesBirthGhost,
              if_pos hbirth] at hcol0
          unfold coverageLeavesMoveToken
            coverageLeavesPhysicalFinish
            coverageLeavesOneResponder
          rw [dif_pos hlast0, if_pos hbirth0]
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
              coverageLeavesBirthGhost,
              if_pos hbirth] at hcol0
          unfold coverageLeavesMoveToken
            coverageLeavesPhysicalFinish
            coverageLeavesOneResponder
          rw [dif_pos hlast0, if_pos hbirth0]
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
          unfold coverageLeavesMoveToken
            coverageLeavesPhysicalFinish
            coverageLeavesOneResponder
          rw [dif_pos hlast0, if_neg hbirth0]
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
          unfold coverageLeavesMoveToken
            coverageLeavesPhysicalFinish
            coverageLeavesOneResponder
          rw [dif_pos hlast0, if_neg hbirth0]
          simp only [if_neg hcol0]
          try simp only
            [l2, l1, if_neg hcol,
              if_neg hbirth] <;> rfl

    have hghost :
        coverageLeavesGhostMoveToken
            hpsi kind step site l r gl gr =
          coverageLeavesGhostFinish
            hpsi kind l r lv2 rv0 gl2 gr0 := by
      unfold coverageLeavesGhostMoveToken
        coverageLeavesGhostFinish
      rw [dif_pos hlast] <;> rfl

    have hfinish :=
      coverageLeavesGhostMoveToken_finish_sound
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
        coverageLeavesMoveToken hpsi kind l r =
          (l0, r0) := by
      unfold coverageLeavesMoveToken
      rw [dif_neg hlast0] <;> rfl
    have hghost :
        coverageLeavesGhostMoveToken
            hpsi kind step site l r gl gr =
          ⟨gl0, gr0, []⟩ := by
      unfold coverageLeavesGhostMoveToken
      rw [dif_neg hlast] <;> rfl
    have hstay :=
      coverageLeavesGhostMoveToken_liveShadow_stay
        kind l r gl gr
    rw [hphys, hghost]
    simpa only [l0, r0, gl0, gr0]
      using hstay


/-! ## Public physical suffix frame -/


private theorem coverageLeavesMoveToken_dist
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


private theorem coverageLeavesElimFrame
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


private theorem coverageLeavesWhitePreservesBlack
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


private theorem coverageLeavesPplSelectedFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let s :=
      coverageLeavesSelectedOutput hpsi kind l r
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
      let p := coverageLeavesPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hwTok :=
        coverageLeavesWhitePreservesBlack
          hpsi b.1 b.2
      have hwDist :=
        coverageLeavesMoveToken_dist
          hpsi .white b.1 b.2
      have he :=
        coverageLeavesElimFrame
          TokenKind.black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          coverageLeavesSelectedOutput
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
      let p := coverageLeavesPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        coverageLeavesElimFrame
          TokenKind.white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          coverageLeavesSelectedOutput
              hpsi TokenKind.white l r =
            w := by
        rfl
      dsimp only at he
      rw [hfull, hselected]
      exact he


private theorem coverageLeavesOptionSound_transport
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (g : Option (GhostToken n psi))
    (hs : CoverageLeavesOptionSound kind q g)
    (htok : tokenAt kind q' = tokenAt kind q)
    (hdist : q'.dist = q.dist) :
    CoverageLeavesOptionSound kind q' g := by
  intro z hz
  have h := hs z hz
  refine And.intro ?_ ?_
  · exact htok.trans h.1
  · unfold coverageLeavesLocalValid at h ⊢
    unfold tokenTargetCoordinate at h ⊢
    rw [hdist]
    exact h.2


private theorem coverageLeavesMovedPair_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    let q :=
      ppl hpsi
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    let g :=
      coverageLeavesMovedPair
        hpsi ring step G e kind
    And
      (CoverageLeavesOptionSound kind q.1 g.left)
      (CoverageLeavesOptionSound kind q.2 g.right) := by
  let p :=
    coverageLeavesSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hm :=
    coverageLeavesGhostMoveToken_sound
      hpsi kind step e p.1 p.2
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
  have hf :=
    coverageLeavesPplSelectedFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  dsimp only at hm hf
  have hmLeft :
      CoverageLeavesOptionSound kind
        (coverageLeavesSelectedOutput
          hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1
        (coverageLeavesMovedPair
          hpsi ring step G e kind).left := by
    simpa [coverageLeavesSelectedOutput,
      coverageLeavesMovedPair, p] using hm.1
  have hmRight :
      CoverageLeavesOptionSound kind
        (coverageLeavesSelectedOutput
          hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2
        (coverageLeavesMovedPair
          hpsi ring step G e kind).right := by
    simpa [coverageLeavesSelectedOutput,
      coverageLeavesMovedPair, p] using hm.2
  exact
    And.intro
      (coverageLeavesOptionSound_transport
        kind _ _ _
        hmLeft hf.1 hf.2.1)
      (coverageLeavesOptionSound_transport
        kind _ _ _
        hmRight hf.2.2.1 hf.2.2.2)


/-! ## GhostSound: initial state and one literal step -/


private def CoverageLeavesColorSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa) : Prop :=
  forall i z,
    ghostTokenAt kind G i = some z ->
    And
      (tokenAt kind (G.phys i) = some z.value)
      (coverageLeavesLocalValid
        kind (G.phys i) z.value)


private theorem coverageLeavesGhostSound_iff
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa) :
    GhostSound G <->
      And
        (CoverageLeavesColorSound .black G)
        (CoverageLeavesColorSound .white G) := by
  rfl


private noncomputable def coverageLeavesInitialOwned
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (i : Fin n) :
    Option (GhostToken n psi) := by
  classical
  exact
    match tokenAt kind (C i) with
    | none => none
    | some t =>
        if coverageLeavesLocalValid kind (C i) t then
          some
            { value := t
              lmeta :=
                { id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0 } }
        else
          none


private theorem coverageLeavesGhostTokenAtInitial
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind (initialGhost C) i =
      coverageLeavesInitialOwned kind C i := by
  cases kind <;> rfl


private theorem coverageLeavesInitialGhost_sound
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    GhostSound (initialGhost C) := by
  rw [coverageLeavesGhostSound_iff]
  constructor <;> intro i z hz
  all_goals
    rw [coverageLeavesGhostTokenAtInitial] at hz
    unfold coverageLeavesInitialOwned at hz
    split at hz
    · contradiction
    · rename_i t ht
      split at hz
      · rename_i hv
        cases hz
        have hphys :
            (initialGhost C).phys = C := rfl
        rw [hphys]
        exact
          And.intro
            (by simpa only using ht)
            (by simpa only using hv)
      · contradiction


private theorem coverageLeavesGhostStep_color_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hG : CoverageLeavesColorSound kind G) :
    CoverageLeavesColorSound kind
      (ghostStep hpsi ring step G e) := by
  intro i z hz
  have hm :=
    coverageLeavesMovedPair_sound
      hpsi ring step G e kind


  by_cases hie : i = e
  · subst i
    rw [
      coverageLeavesGhostTokenAtStep
        hpsi ring step G e kind e] at hz
    simp only
      [coverageLeavesSetTwo, if_pos rfl] at hz
    dsimp only at hm
    have hs := hm.1 z hz
    have hphys :
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
    rw [hphys]
    exact hs


  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hne :
          ring.rightNeighbor e ≠ e := by
        exact hie
      rw [
        coverageLeavesGhostTokenAtStep
          hpsi ring step G e kind
            (ring.rightNeighbor e)] at hz
      simp only
        [coverageLeavesSetTwo,
          if_neg hne, if_pos rfl] at hz
      dsimp only at hm
      have hs := hm.2 z hz
      have hphys :
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
      rw [hphys]
      exact hs


    · have hz0 :
          ghostTokenAt kind G i = some z := by
        rw [
          coverageLeavesGhostTokenAtStep
            hpsi ring step G e kind i] at hz
        simpa
          [coverageLeavesSetTwo, hie, hir]
          using hz
      have hs := hG i z hz0
      have hphys :
          (ghostStep hpsi ring step G e).phys i =
            G.phys i := by
        change
          PopulationProtocol.step
              (protocol psi kappa)
              ring G.phys e i =
            G.phys i
        simp [PopulationProtocol.step, hie, hir]
      rw [hphys]
      exact hs


private theorem coverageLeavesGhostStep_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hG : GhostSound G) :
    GhostSound (ghostStep hpsi ring step G e) := by
  rw [coverageLeavesGhostSound_iff] at hG ⊢
  exact
    And.intro
      (coverageLeavesGhostStep_color_sound
        hpsi ring step G e .black hG.1)
      (coverageLeavesGhostStep_color_sound
        hpsi ring step G e .white hG.2)


private theorem coverageLeavesGhostRun_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) :
    forall (t : Nat)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      GhostSound G ->
      GhostSound
        (ghostRun hpsi ring t G schedule) := by
  intro t G schedule hG
  induction schedule generalizing t G with
  | nil =>
      exact hG
  | cons e es ih =>
      simp only [ghostRun]
      exact
        ih (t + 1)
          (ghostStep hpsi ring t G e)
          (coverageLeavesGhostStep_sound
            hpsi ring t G e hG)


/-! ## Closed leaf and exact remaining adapter -/


theorem lemma4CoverageGhostRunSound_proved :
    Lemma4CoverageGhostRunSound := by
  unfold Lemma4CoverageGhostRunSound
  intro n psi kappa hpsi ring C0 pre
  exact
    coverageLeavesGhostRun_sound
      hpsi ring 0 (initialGhost C0) pre
      (coverageLeavesInitialGhost_sound C0)


theorem lemma4CoverageStep_of_remaining
    (htouched : Lemma4CoverageTouchedCoverageSound)
    (hleft : Lemma4CoverageOriginInitiatorRow)
    (hright : Lemma4CoverageOriginResponderRow) :
    Lemma4CoverageStep :=
  lemma4CoverageStep_of_repaired_endpoint_rows
    lemma4CoverageGhostRunSound_proved
    htouched hleft hright


end PPL


#print axioms PPL.lemma4CoverageGhostRunSound_proved
#print axioms PPL.lemma4CoverageStep_of_remaining

