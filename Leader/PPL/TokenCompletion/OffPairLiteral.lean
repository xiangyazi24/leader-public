import Leader.PPL.TokenCompletion.RightmostResponder
import Leader.PPL.TokenCompletion.GhostStepMirror


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


private def offPairBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def offPairMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def offPairLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
        target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
        target ≤ (((psi - 1 : Nat)) : Int))


private instance instDecidableOffPairLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (offPairLocalValid kind q t) := by
  unfold offPairLocalValid
  infer_instance


private def offPairLiveShadow
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
              offPairLocalValid kind q t then
            some z
          else
            none


private def offPairLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if offPairLocalValid kind q t then
        some t
      else
        none


private def offPairBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      offPairMkToken
        (offsetPsiCode psi hpsi)
        (offPairBitToFin (!idBit))
        (offPairBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def offPairBumpTo
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
        if offPairLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def offPairNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    offPairMkToken
      (offsetPsiCode psi hpsi)
      (offPairBitToFin (!sourceBit))
      (offPairBitToFin sourceBit)
  else
    offPairMkToken
      (offsetPsiCode psi hpsi)
      (offPairBitToFin sourceBit)
      (0 : Fin 2)


private def offPairFinishMove
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match lv2 with
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let next :=
          offPairMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := offPairBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          offPairMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := offPairBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                offPairNegTurnNext hpsi l.id tr
              let b := offPairBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                offPairMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := offPairBumpTo kind l next gr0
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
              offPairNegTurnNext hpsi l.id tr
            let b := offPairBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              offPairMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := offPairBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩


private def offPairGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := offPairLiveValue kind l
  let rv0 := offPairLiveValue kind r
  let gl0 := offPairLiveShadow kind l gl
  let gr0 := offPairLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (offPairBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (offPairBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    offPairFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩


private def offPairTokenPrelude
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


private def offPairSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := offPairTokenPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2


private def offPairSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let p :=
    offPairSelectedInput hpsi kind
      (G.phys e) (G.phys rsite)
  offPairGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G rsite)


private theorem offPairSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    offPairSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl


private theorem offPairMoveTokenDist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := moveToken hpsi kind l r
    q.1.dist = l.dist ∧ q.2.dist = r.dist := by
  dsimp only
  have hi :=
    moveToken_initiator_fields
      hpsi kind l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.dist) hi
  have hl :
      (moveToken hpsi kind l r).1.dist = l.dist := by
    cases kind <;>
      simpa [eraseKindToken] using hil
  rcases
      moveToken_responder_fields
        hpsi kind l r with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.dist) hr
    have hr' :
        (moveToken hpsi kind l r).2.dist = r.dist := by
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken] using hrr
    exact ⟨hl, hr'⟩
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.dist) hr
    have hr' :
        (moveToken hpsi kind l r).2.dist = r.dist := by
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken, birthFields] using hrr
    exact ⟨hl, hr'⟩


private theorem offPairElimDist
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
    ⟨congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.dist) hr⟩


private theorem offPairPplSelectedDist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := offPairSelectedInput hpsi kind l r
    (ppl hpsi l r).1.dist = p.1.dist ∧
      (ppl hpsi l r).2.dist = p.2.dist := by
  cases kind with
  | black =>
      let p := offPairTokenPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hb :=
        offPairMoveTokenDist
          hpsi .black p.1 p.2
      have hw :=
        offPairMoveTokenDist
          hpsi .white b.1 b.2
      have he :=
        offPairElimDist w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          offPairSelectedInput
              hpsi .black l r =
            p := by
        rfl
      dsimp only at hb hw he
      rw [hfull, hselected]
      exact
        ⟨he.1.trans (hw.1.trans hb.1),
          he.2.trans (hw.2.trans hb.2)⟩
  | white =>
      let p := offPairTokenPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw :=
        offPairMoveTokenDist
          hpsi .white b.1 b.2
      have he :=
        offPairElimDist w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          offPairSelectedInput
              hpsi .white l r =
            b := by
        rfl
      dsimp only at hw he
      rw [hfull, hselected]
      exact
        ⟨he.1.trans hw.1,
          he.2.trans hw.2⟩


private theorem offPairStepSelectedDist
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    ((ghostStep hpsi ring step G e).phys e).dist =
        p.1.dist ∧
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        p.2.dist := by
  dsimp only
  have hp :=
    offPairPplSelectedDist
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
    ⟨(congrArg
        (fun q : State psi kappa => q.dist) hl).trans hp.1,
      (congrArg
        (fun q : State psi kappa => q.dist) hr).trans hp.2⟩


private theorem offPairCdTwoLe
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


private theorem offPairRightNeighborNe
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


private theorem offPairRightNeighborInjective
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
    · have hbeq : b.val + 1 = n := by
        omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by
      omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by
        omega
      omega


private theorem offPairRightNeighborShiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) (d : Nat) :
    ring.rightNeighbor (shiftRight ring k d) =
      shiftRight ring k (d + 1) := by
  apply Fin.ext
  simp only
    [DirectedRing.rightNeighbor, shiftRight]
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem offPairCanonicalBase
    {psi : Nat}
    (hpsi : 2 ≤ psi)
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
          2 * psi ≤ x.val + psi := by
          omega
        have hsub :
            x.val + psi - 2 * psi <
              2 * psi := by
          omega
        rw [Nat.mod_eq_sub_mod hge,
          Nat.mod_eq_of_lt hsub] at hcanon
        omega


private theorem offPairCanonicalNotSource
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (x : Fin (2 * psi))
    (hx : 0 < x.val)
    (q : State psi kappa)
    (hcanon :
      q.dist.val =
        (x.val + tokenD' psi kind) %
          (2 * psi)) :
    q.dist.val ≠ tokenD' psi kind := by
  intro hsource
  have heq :
      (x.val + tokenD' psi kind) %
          (2 * psi) =
        tokenD' psi kind :=
    hcanon.symm.trans hsource
  have hx0 :=
    offPairCanonicalBase
      hpsi kind x heq
  omega


private structure OffPairPrefix
    (n psi : Nat) where
  lv2 : Option (TokenData psi)
  rv0 : Option (TokenData psi)
  gl2 : Option (GhostToken n psi)
  gr0 : Option (GhostToken n psi)


private def offPairPrefix
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    OffPairPrefix n psi :=
  let lv0 := offPairLiveValue kind l
  let rv0 := offPairLiveValue kind r
  let gl0 := offPairLiveShadow kind l gl
  let gr0 := offPairLiveShadow kind r gr
  let birthGuard :=
    l.dist.val = tokenD' psi kind ∧
      lv0 = none
  let birth :=
    offPairBirthGhost hpsi kind step site l.id
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


private theorem offPairGhostMoveToken_eq_finish
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hlast : l.last = false ∧ r.last = false) :
    offPairGhostMoveToken
        hpsi kind step site l r gl gr =
      offPairFinishMove
        hpsi kind l r
        (offPairPrefix
          hpsi kind step site l r gl gr).lv2
        (offPairPrefix
          hpsi kind step site l r gl gr).rv0
        (offPairPrefix
          hpsi kind step site l r gl gr).gl2
        (offPairPrefix
          hpsi kind step site l r gl gr).gr0 := by
  unfold offPairGhostMoveToken offPairPrefix
  rw [if_pos hlast]


private theorem offPairGhostMoveToken_eq_shadow
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hlast : ¬ (l.last = false ∧ r.last = false)) :
    offPairGhostMoveToken
        hpsi kind step site l r gl gr =
      ⟨offPairLiveShadow kind l gl,
        offPairLiveShadow kind r gr, []⟩ := by
  unfold offPairGhostMoveToken
  rw [if_neg hlast]


private theorem offPairPrefix_left_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (hnotSource :
      l.dist.val ≠ tokenD' psi kind) :
    (offPairPrefix
        hpsi kind step site l r none gr).gl2 =
      none := by
  unfold offPairPrefix
  simp [offPairLiveShadow, hnotSource]


private theorem offPairPrefix_right_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi)) :
    (offPairPrefix
        hpsi kind step site l r gl none).gr0 =
      none := by
  unfold offPairPrefix
  simp [offPairLiveShadow]


private theorem offPairFinishMove_none_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi)) :
    let q :=
      offPairFinishMove (n := n)
        hpsi kind l r lv2 rv0 none none
    q.left = none ∧ q.right = none := by
  dsimp only
  cases lv2 with
  | none =>
      cases rv0 with
      | none =>
          simp [offPairFinishMove]
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [offPairFinishMove,
                dif_pos hm1, offPairBumpTo, and_self]
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · simp only
                [offPairFinishMove,
                  dif_neg hm1, dif_pos hm2,
                  offPairBumpTo, and_self]
            · simp only
                [offPairFinishMove,
                  dif_neg hm1, dif_neg hm2, and_self]
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [offPairFinishMove,
            dif_pos h1, offPairBumpTo, and_self]
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · simp only
            [offPairFinishMove,
              dif_neg h1, dif_pos h2,
              offPairBumpTo, and_self]
        · cases rv0 with
          | none =>
              simp only
                [offPairFinishMove,
                  dif_neg h1, dif_neg h2, and_self]
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [offPairFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1, offPairBumpTo, and_self]
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · simp only
                    [offPairFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2,
                      offPairBumpTo, and_self]
                · simp only
                    [offPairFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2, and_self]


private theorem offPairGhostMoveToken_none_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (hnotSource :
      l.dist.val ≠ tokenD' psi kind) :
    let q :=
      offPairGhostMoveToken
        hpsi kind step site l r none none
    q.left = none ∧ q.right = none := by
  dsimp only
  by_cases hlast :
      l.last = false ∧ r.last = false
  · rw [offPairGhostMoveToken_eq_finish
      hpsi kind step site l r none none hlast]
    have hleft :=
      offPairPrefix_left_none
        hpsi kind step site l r none hnotSource
    have hright :=
      offPairPrefix_right_none
        hpsi kind step site l r none
    rw [hleft, hright]
    exact
      offPairFinishMove_none_none
        hpsi kind l r
        (offPairPrefix
          hpsi kind step site l r none none).lv2
        (offPairPrefix
          hpsi kind step site l r none none).rv0
  · rw [offPairGhostMoveToken_eq_shadow
      hpsi kind step site l r none none hlast]
    simp [offPairLiveShadow]


private def offPairLeftMovedShape
    {psi : Nat}
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  c = ((psi : Nat) : Int) ∨
    (1 - ((psi : Nat) : Int) < c ∧ c < 0)


private theorem offPairThreePsiMinusOneMod
    {psi : Nat}
    (hpsi : 2 ≤ psi) :
    (3 * psi - 1) % (2 * psi) =
      psi - 1 := by
  have hge :
      2 * psi ≤ 3 * psi - 1 := by
    omega
  rw [Nat.mod_eq_sub_mod hge]
  have heq :
      3 * psi - 1 - 2 * psi =
        psi - 1 := by
    omega
  rw [heq]
  rw [Nat.mod_eq_of_lt (by omega)]


private theorem offPairLastDistPlusD
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


private theorem offPairLastLeftTargetTurn
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
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
    offPairLastDistPlusD
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
  rw [offPairThreePsiMinusOneMod hpsi]


private theorem offPairLastLeftTargetNegative
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
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
    offPairLastDistPlusD
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
        (((psi : Nat) : Int)) <
          (((s % (2 * psi) : Nat)) : Int)
      rw [Nat.mod_eq_of_lt hslt]
      exact_mod_cast hspsi


private theorem offPairLeftMovedNotLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hlocal : offPairLocalValid kind q t)
    (hshape : offPairLeftMovedShape t) :
    False := by
  unfold offPairLeftMovedShape at hshape
  dsimp only at hshape
  unfold offPairLocalValid at hlocal
  dsimp only at hlocal
  rcases hshape with hturn | hneg
  · have ht :=
      offPairLastLeftTargetTurn
        hpsi kind q t hdist hturn
    rw [hturn, ht] at hlocal
    rcases hlocal with hp | hn <;>
      omega
  · have ht :=
      offPairLastLeftTargetNegative
        hpsi kind q t hdist
        hneg.1 hneg.2
    rcases hlocal with hp | hn <;>
      omega


private theorem offPairBumpTo_live_none_of_invalid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (next : TokenData psi)
    (g : Option (GhostToken n psi))
    (hbad : ¬ offPairLocalValid kind q next) :
    (offPairBumpTo kind q next g).live = none := by
  cases g with
  | none =>
      rfl
  | some z =>
      simp [offPairBumpTo, hbad]


private theorem offPairNegTurnBump_none_at_last
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l : State psi kappa)
    (tr : TokenData psi)
    (gr : Option (GhostToken n psi))
    (hdist :
      l.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi)) :
    let next := offPairNegTurnNext hpsi l.id tr
    (offPairBumpTo kind l next gr).live = none := by
  let next := offPairNegTurnNext hpsi l.id tr
  have hshape :
      offPairLeftMovedShape next := by
    unfold offPairLeftMovedShape
    unfold next offPairNegTurnNext
    by_cases hcarry : tr.2 = (1 : Fin 2)
    · rw [if_pos hcarry]
      dsimp [offPairMkToken, tokenCode]
      left
      exact decodeOffset_psi psi hpsi
    · rw [if_neg hcarry]
      dsimp [offPairMkToken, tokenCode]
      left
      exact decodeOffset_psi psi hpsi
  have hbad :
      ¬ offPairLocalValid kind l next := by
    intro hlocal
    exact
      offPairLeftMovedNotLast
        hpsi kind l next hdist hlocal hshape
  exact
    offPairBumpTo_live_none_of_invalid
      kind l next gr hbad


private theorem offPairNegStepBump_none_at_last
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l : State psi kappa)
    (tr : TokenData psi)
    (gr : Option (GhostToken n psi))
    (hdist :
      l.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hm2 :
      decodeOffset psi (tokenCode tr) ≤ -2) :
    let c := decodeOffset psi (tokenCode tr)
    have hc : ValidOffset psi c :=
      decodeOffset_valid
        psi (by omega) (tokenCode tr)
    let next :=
      offPairMkToken
        (encodeOffset psi (c + 1) (by
          rcases hc with hn | hp
          · left
            omega
          · exfalso
            omega))
        tr.1.2 tr.2
    (offPairBumpTo kind l next gr).live = none := by
  let c := decodeOffset psi (tokenCode tr)
  have hc : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode tr)
  let next :=
    offPairMkToken
      (encodeOffset psi (c + 1) (by
        rcases hc with hn | hp
        · left
          omega
        · exfalso
          omega))
      tr.1.2 tr.2
  have hnext :
      decodeOffset psi (tokenCode next) =
        c + 1 := by
    dsimp [next, offPairMkToken, tokenCode]
    exact decode_encode _ _ _
  have hshape :
      offPairLeftMovedShape next := by
    unfold offPairLeftMovedShape
    dsimp only
    rw [hnext]
    right
    rcases hc with hn | hp
    · omega
    · omega
  have hbad :
      ¬ offPairLocalValid kind l next := by
    intro hlocal
    exact
      offPairLeftMovedNotLast
        hpsi kind l next hdist hlocal hshape
  exact
    offPairBumpTo_live_none_of_invalid
      kind l next gr hbad


private theorem offPairFinishMove_left_none_at_last
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gr0 : Option (GhostToken n psi))
    (hdist :
      l.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi)) :
    (offPairFinishMove
        hpsi kind l r lv2 rv0 none gr0).left =
      none := by
  cases lv2 with
  | none =>
      cases rv0 with
      | none =>
          rfl
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · have hb :=
              offPairNegTurnBump_none_at_last
                hpsi kind l tr gr0 hdist
            simpa
              [offPairFinishMove,
                dif_pos hm1] using hb
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · have hb :=
                offPairNegStepBump_none_at_last
                  hpsi kind l tr gr0 hdist hm2
              simpa
                [offPairFinishMove,
                  dif_neg hm1, dif_pos hm2] using hb
            · simp only
                [offPairFinishMove,
                  dif_neg hm1, dif_neg hm2]
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [offPairFinishMove, dif_pos h1]
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · simp only
            [offPairFinishMove,
              dif_neg h1, dif_pos h2]
        · cases rv0 with
          | none =>
              simp only
                [offPairFinishMove,
                  dif_neg h1, dif_neg h2]
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · have hb :=
                  offPairNegTurnBump_none_at_last
                    hpsi kind l tr gr0 hdist
                simpa
                  [offPairFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1] using hb
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · have hb :=
                    offPairNegStepBump_none_at_last
                      hpsi kind l tr gr0 hdist hm2
                  simpa
                    [offPairFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2] using hb
                · simp only
                    [offPairFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]


private theorem offPairGhostMoveToken_left_none_at_last
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (hnotSource :
      l.dist.val ≠ tokenD' psi kind)
    (hdist :
      l.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi)) :
    (offPairGhostMoveToken
        hpsi kind step site l r none gr).left =
      none := by
  by_cases hlast :
      l.last = false ∧ r.last = false
  · rw [offPairGhostMoveToken_eq_finish
      hpsi kind step site l r none gr hlast]
    have hleft :=
      offPairPrefix_left_none
        hpsi kind step site l r gr hnotSource
    rw [hleft]
    exact
      offPairFinishMove_left_none_at_last
        hpsi kind l r
        (offPairPrefix
          hpsi kind step site l r none gr).lv2
        (offPairPrefix
          hpsi kind step site l r none gr).rv0
        (offPairPrefix
          hpsi kind step site l r none gr).gr0
        hdist
  · rw [offPairGhostMoveToken_eq_shadow
      hpsi kind step site l r none gr hlast]
    simp [offPairLiveShadow]


private theorem offPairSelectedPair_none_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hleft :
      ghostTokenAt kind G e = none)
    (hright :
      ghostTokenAt kind G
        (ring.rightNeighbor e) = none)
    (hnotSource :
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1.dist.val ≠
          tokenD' psi kind) :
    (offPairSelectedPair
        hpsi ring step G e kind).left = none ∧
      (offPairSelectedPair
        hpsi ring step G e kind).right = none := by
  unfold offPairSelectedPair
  dsimp only
  rw [hleft, hright]
  exact
    offPairGhostMoveToken_none_none
      hpsi kind step e
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2
      hnotSource


private theorem offPairSelectedPair_left_none_at_last
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hleft :
      ghostTokenAt kind G e = none)
    (hnotSource :
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1.dist.val ≠
          tokenD' psi kind)
    (hdist :
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi)) :
    (offPairSelectedPair
        hpsi ring step G e kind).left = none := by
  unfold offPairSelectedPair
  rw [hleft]
  exact
    offPairGhostMoveToken_left_none_at_last
      hpsi kind step e
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).1
      (offPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))).2
      (ghostTokenAt kind G (ring.rightNeighbor e))
      hnotSource hdist


private theorem offPairInitiatorInterior
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hright :
      Lemma4RightmostAt ring k kind G x z)
    (hy : x.val < y.val)
    (he : shiftRight ring k y.val = e)
    (hinterior : y.val + 1 < 2 * psi) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (shiftRight ring k y.val) =
      none := by
  have hn2 :=
    offPairCdTwoLe
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    offPairRightNeighborNe ring hn2 e
  unfold Lemma4RightmostAt at hright
  have hnoneY :
      ghostTokenAt kind G
          (shiftRight ring k y.val) = none :=
    hright.2.2 y hy
  let ys : Fin (2 * psi) :=
    ⟨y.val + 1, hinterior⟩
  have hxys : x.val < ys.val := by
    dsimp [ys]
    omega
  have hnoneS :
      ghostTokenAt kind G
          (shiftRight ring k ys.val) = none :=
    hright.2.2 ys hxys
  have hrs :
      ring.rightNeighbor e =
        shiftRight ring k ys.val := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor
            (shiftRight ring k y.val) :=
        congrArg
          (fun u : Fin n => ring.rightNeighbor u)
          he.symm
      _ = shiftRight ring k (y.val + 1) :=
        offPairRightNeighborShiftRight
          ring k y.val
      _ = shiftRight ring k ys.val := by
        rfl
  have hgl :
      ghostTokenAt kind G e = none := by
    simpa [he] using hnoneY
  have hgr :
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none := by
    simpa [hrs] using hnoneS
  let p :=
    offPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hdist :
      ((ghostStep hpsi ring step G e).phys e).dist =
          p.1.dist ∧
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          p.2.dist := by
    simpa [p] using
      offPairStepSelectedDist
        hpsi ring step G e kind hne
  have hrow := hCd' y
  dsimp only at hrow
  have hpost :
      ((ghostStep hpsi ring step G e).phys e).dist.val =
        (y.val + tokenD' psi kind) %
          (2 * psi) := by
    simpa [he] using hrow.1
  have hpCanon :
      p.1.dist.val =
        (y.val + tokenD' psi kind) %
          (2 * psi) :=
    (congrArg Fin.val hdist.1).symm.trans hpost
  have hnotSource :
      p.1.dist.val ≠ tokenD' psi kind :=
    offPairCanonicalNotSource
      hpsi kind y (by omega) p.1 hpCanon
  have hlocal :=
    offPairSelectedPair_none_none
      hpsi ring step G e kind
      hgl hgr
      (by simpa [p] using hnotSource)
  have hpublic :
      (ghostStepSelectedPair
          hpsi ring step G e kind).left =
        none := by
    rw [← offPairSelectedPair_eq_export
      hpsi ring step G e kind]
    exact hlocal.1
  calc
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (shiftRight ring k y.val) =
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) e := by
          rw [he]
    _ =
      (ghostStepSelectedPair
          hpsi ring step G e kind).left :=
        ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind
    _ = none := hpublic


private theorem offPairInitiatorLast
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hright :
      Lemma4RightmostAt ring k kind G x z)
    (hy : x.val < y.val)
    (he : shiftRight ring k y.val = e)
    (hlast : y.val = 2 * psi - 1) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (shiftRight ring k y.val) =
      none := by
  have hn2 :=
    offPairCdTwoLe
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    offPairRightNeighborNe ring hn2 e
  unfold Lemma4RightmostAt at hright
  have hnoneY :
      ghostTokenAt kind G
          (shiftRight ring k y.val) = none :=
    hright.2.2 y hy
  have hgl :
      ghostTokenAt kind G e = none := by
    simpa [he] using hnoneY
  let p :=
    offPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hdist :
      ((ghostStep hpsi ring step G e).phys e).dist =
          p.1.dist ∧
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          p.2.dist := by
    simpa [p] using
      offPairStepSelectedDist
        hpsi ring step G e kind hne
  have hrow := hCd' y
  dsimp only at hrow
  have hpost :
      ((ghostStep hpsi ring step G e).phys e).dist.val =
        (y.val + tokenD' psi kind) %
          (2 * psi) := by
    simpa [he] using hrow.1
  have hpCanon :
      p.1.dist.val =
        (y.val + tokenD' psi kind) %
          (2 * psi) :=
    (congrArg Fin.val hdist.1).symm.trans hpost
  have hnotSource :
      p.1.dist.val ≠ tokenD' psi kind :=
    offPairCanonicalNotSource
      hpsi kind y (by omega) p.1 hpCanon
  have hlastDist :
      p.1.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi) := by
    simpa [hlast] using hpCanon
  have hlocal :=
    offPairSelectedPair_left_none_at_last
      hpsi ring step G e kind
      hgl
      (by simpa [p] using hnotSource)
      (by simpa [p] using hlastDist)
  have hpublic :
      (ghostStepSelectedPair
          hpsi ring step G e kind).left =
        none := by
    rw [← offPairSelectedPair_eq_export
      hpsi ring step G e kind]
    exact hlocal
  calc
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (shiftRight ring k y.val) =
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) e := by
          rw [he]
    _ =
      (ghostStepSelectedPair
          hpsi ring step G e kind).left :=
        ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind
    _ = none := hpublic


private theorem offPairResponderEndpoint
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hright :
      Lemma4RightmostAt ring k kind G x z)
    (hie :
      e ≠ shiftRight ring k x.val)
    (hy : x.val < y.val)
    (hr :
      shiftRight ring k y.val =
        ring.rightNeighbor e) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (shiftRight ring k y.val) =
      none := by
  have hn2 :=
    offPairCdTwoLe
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor e ≠ e :=
    offPairRightNeighborNe ring hn2 e
  unfold Lemma4RightmostAt at hright
  have hnoneY :
      ghostTokenAt kind G
          (shiftRight ring k y.val) = none :=
    hright.2.2 y hy
  have hypos : 0 < y.val := by
    omega
  let yp : Fin (2 * psi) :=
    ⟨y.val - 1, by omega⟩
  have hrPred :
      ring.rightNeighbor
          (shiftRight ring k yp.val) =
        shiftRight ring k y.val := by
    have hstep :=
      offPairRightNeighborShiftRight
        ring k yp.val
    have harg : yp.val + 1 = y.val := by
      dsimp [yp]
      omega
    simpa [harg] using hstep
  have hePred :
      e = shiftRight ring k yp.val := by
    apply offPairRightNeighborInjective ring
    calc
      ring.rightNeighbor e =
          shiftRight ring k y.val :=
        hr.symm
      _ =
          ring.rightNeighbor
            (shiftRight ring k yp.val) :=
        hrPred.symm
  have hxyp : x.val < yp.val := by
    have hle : x.val ≤ yp.val := by
      dsimp [yp]
      omega
    by_cases heq : x.val = yp.val
    · have heFront :
          e = shiftRight ring k x.val := by
        calc
          e = shiftRight ring k yp.val := hePred
          _ = shiftRight ring k x.val := by
            rw [← heq]
      exact False.elim (hie heFront)
    · omega
  have hnoneP :
      ghostTokenAt kind G
          (shiftRight ring k yp.val) = none :=
    hright.2.2 yp hxyp
  have hgl :
      ghostTokenAt kind G e = none := by
    simpa [hePred] using hnoneP
  have hgr :
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none := by
    simpa [hr] using hnoneY
  let p :=
    offPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hdist :
      ((ghostStep hpsi ring step G e).phys e).dist =
          p.1.dist ∧
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          p.2.dist := by
    simpa [p] using
      offPairStepSelectedDist
        hpsi ring step G e kind hne
  have hrow := hCd' yp
  dsimp only at hrow
  have hpost :
      ((ghostStep hpsi ring step G e).phys e).dist.val =
        (yp.val + tokenD' psi kind) %
          (2 * psi) := by
    simpa [hePred] using hrow.1
  have hpCanon :
      p.1.dist.val =
        (yp.val + tokenD' psi kind) %
          (2 * psi) :=
    (congrArg Fin.val hdist.1).symm.trans hpost
  have hnotSource :
      p.1.dist.val ≠ tokenD' psi kind :=
    offPairCanonicalNotSource
      hpsi kind yp (by omega) p.1 hpCanon
  have hlocal :=
    offPairSelectedPair_none_none
      hpsi ring step G e kind
      hgl hgr
      (by simpa [p] using hnotSource)
  have hpublic :
      (ghostStepSelectedPair
          hpsi ring step G e kind).right =
        none := by
    rw [← offPairSelectedPair_eq_export
      hpsi ring step G e kind]
    exact hlocal.2
  calc
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (shiftRight ring k y.val) =
      ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) := by
          rw [hr]
    _ =
      (ghostStepSelectedPair
          hpsi ring step G e kind).right :=
        ghostTokenAt_ghostStep_responder_of_ne
          hpsi ring step G e kind hne
    _ = none := hpublic


theorem lemma4RightmostOffPairLiteralCases_proved :
    Lemma4RightmostOffPairLiteralCases := by
  unfold Lemma4RightmostOffPairLiteralCases
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd'
  intro _hcovered _hsound _huniq _hkin
  intro hright hie _hir
  intro y hy hendpoint
  rcases hendpoint with he | hr
  · by_cases hinterior :
        y.val + 1 < 2 * psi
    · exact
        offPairInitiatorInterior
          hpsi ring k kind step G e x y z
          hCd hCd' hright hy he hinterior
    · have hlast :
          y.val = 2 * psi - 1 := by
        have hylt := y.isLt
        omega
      exact
        offPairInitiatorLast
          hpsi ring k kind step G e x y z
          hCd hCd' hright hy he hlast
  · exact
      offPairResponderEndpoint
        hpsi ring k kind step G e x y z
        hCd hCd' hright hie hy hr


end PPL


#print axioms PPL.lemma4RightmostOffPairLiteralCases_proved
