import Leader.PPL.TokenCompletion.RightmostResponderLiteral

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

private def selPairBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)
private def selPairMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)
private def selPairLocalValid
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
private instance instDecidableSweepRespLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (selPairLocalValid kind q t) := by
  unfold selPairLocalValid
  infer_instance
private def selPairSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }
private def selPairClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if selPairLocalValid kind q t then
        q
      else
        selPairSetToken kind q none
private def selPairLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }
private theorem selPairSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      selPairSetToken kind q t := by
  cases kind <;> rfl
private theorem selPairSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      selPairClearInvalid kind q := by
  cases kind <;> rfl
private theorem selPairSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = selPairLeaderBirth q := by
  rfl
private def selPairNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    selPairMkToken
      (offsetPsiCode psi hpsi)
      (selPairBitToFin (!sourceBit))
      (selPairBitToFin sourceBit)
  else
    selPairMkToken
      (offsetPsiCode psi hpsi)
      (selPairBitToFin sourceBit)
      (0 : Fin 2)
private def selPairLiveShadow
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
              selPairLocalValid kind q t then
            some z
          else
            none
private def selPairLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if selPairLocalValid kind q t then
        some t
      else
        none
private def selPairBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      selPairMkToken
        (offsetPsiCode psi hpsi)
        (selPairBitToFin (!idBit))
        (selPairBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }
private def selPairBumpTo
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
        if selPairLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩
private def selPairGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := selPairLiveValue kind l
  let rv0 := selPairLiveValue kind r
  let gl0 := selPairLiveShadow kind l gl
  let gr0 := selPairLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (selPairBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (selPairBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if c = 1 then
          let next :=
            selPairMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            selPairBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            selPairMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            selPairBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some t =>
              let c :=
                decodeOffset psi (tokenCode t)
              if c = -1 then
                let next :=
                  selPairNegTurnNext
                    hpsi l.id t
                let b :=
                  selPairBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c ≤ -2 then
                have hbranch : c ≤ -2 := hm2
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  selPairMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  selPairBumpTo
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
            if c = -1 then
              let next :=
                selPairNegTurnNext
                  hpsi l.id t
              let b :=
                selPairBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                selPairMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                selPairBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩
/-
Literal Algorithm 3, expressed through the public sourceSet/sourceClear/
sourceBirth aliases.  This is used only to prove value soundness of the local
ghost mirror.
-/
private def selPairMoveToken
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := sourceClear kind l
  let r := sourceClear kind r
  if l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧
          tokenAt kind l = none then
        sourceSet kind l
          (some
            (selPairMkToken
              (offsetPsiCode psi hpsi)
              (selPairBitToFin (!l.id))
              (selPairBitToFin l.id)))
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
            if c = -1 then
              let next :=
                selPairNegTurnNext hpsi l.id t
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                selPairMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else
              (l, r)
    match tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if c = 1 then
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
                (selPairMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2)))
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            selPairMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          (sourceSet kind l none,
            sourceSet kind r (some next))
        else
          moveLeft l r
  else
    (l, r)
private theorem selPairMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    selPairMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl
private def selPairPrelude
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
private def selPairSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := selPairPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2
private def selPairSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    selPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  selPairGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))
private theorem selPairSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    selPairSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl
/-! -----------------------------------------------------------------------
    Finite ghost-row facts
------------------------------------------------------------------------ -/
/-
Small deterministic projections used by the responder-row proofs below.
They keep sourceClear/sourceSet opaque and expose only the fields Algorithm 3
actually reads after the selected token has been validated.
-/
private theorem selPairLiveValue_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (htok : tokenAt kind q = some t)
    (hvalid : selPairLocalValid kind q t) :
    selPairLiveValue kind q = some t := by
  unfold selPairLiveValue
  rw [htok]
  simp only [if_pos hvalid]

private theorem selPairLiveShadow_some
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hg : g = some z)
    (htok : tokenAt kind q = some z.value)
    (hvalid : selPairLocalValid kind q z.value) :
    selPairLiveShadow kind q g = some z := by
  rw [hg]
  unfold selPairLiveShadow
  rw [htok]
  simp only [true_and, if_pos hvalid]

private theorem selPairSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q v) = v := by
  rw [selPairSourceSet_eq]
  unfold selPairSetToken
  cases kind <;> rfl

private theorem selPairSourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi)) :
    (sourceSet kind q v).id = q.id := by
  rw [selPairSourceSet_eq]
  unfold selPairSetToken
  cases kind <;> rfl

private theorem selPairSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      selPairLiveValue kind q := by
  rw [selPairSourceClear_eq]
  unfold selPairClearInvalid selPairLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : selPairLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold selPairSetToken
        cases kind <;> rfl

private theorem selPairSourceClear_last
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).last = q.last := by
  rw [selPairSourceClear_eq]
  unfold selPairClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : selPairLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold selPairSetToken
        cases kind <;> rfl

private theorem selPairSourceClear_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).id = q.id := by
  rw [selPairSourceClear_eq]
  unfold selPairClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : selPairLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold selPairSetToken
        cases kind <;> rfl

/-! -----------------------------------------------------------------------
    Physical selected-token and last-field projections
------------------------------------------------------------------------ -/
private theorem selPairElimTokenLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (eliminateLeaders l r).1 =
      tokenAt kind l := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left l r
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
private theorem selPairElimTokenRight
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (eliminateLeaders l r).2 =
      tokenAt kind r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right l r
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
private theorem selPairWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black
        (moveToken hpsi .white l r).1 =
      tokenAt .black l ∧
    tokenAt .black
        (moveToken hpsi .white l r).2 =
      tokenAt .black r := by
  have hi :=
    moveToken_initiator_fields
      hpsi .white l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  constructor
  · simpa [eraseKindToken, tokenAt]
      using hil
  · rcases
      moveToken_responder_fields
        hpsi .white l r with hr | hr
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
private theorem selPairPplTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := selPairSelectedInput hpsi kind l r
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).2 := by
  cases kind with
  | black =>
      let p := selPairPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw :=
        selPairWhitePreservesBlack
          hpsi b.1 b.2
      have hel :=
        selPairElimTokenLeft .black w.1 w.2
      have her :=
        selPairElimTokenRight .black w.1 w.2
      change
        tokenAt .black
            (eliminateLeaders w.1 w.2).1 =
              tokenAt .black b.1 ∧
          tokenAt .black
            (eliminateLeaders w.1 w.2).2 =
              tokenAt .black b.2
      exact
        ⟨hel.trans hw.1,
          her.trans hw.2⟩
  | white =>
      let p := selPairPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hel :=
        selPairElimTokenLeft .white w.1 w.2
      have her :=
        selPairElimTokenRight .white w.1 w.2
      change
        tokenAt .white
            (eliminateLeaders w.1 w.2).1 =
              tokenAt .white w.1 ∧
          tokenAt .white
            (eliminateLeaders w.1 w.2).2 =
              tokenAt .white w.2
      exact ⟨hel, her⟩
private theorem selPairMoveTokenLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.last = l.last ∧
      (moveToken hpsi kind l r).2.last = r.last := by
  have hi :=
    moveToken_initiator_fields hpsi kind l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.last) hi
  have hleft :
      (moveToken hpsi kind l r).1.last = l.last := by
    cases kind <;>
      simpa [eraseKindToken] using hil
  rcases
      moveToken_responder_fields hpsi kind l r
    with hr | hr
  · have hir :=
      congrArg
        (fun q : State psi kappa => q.last) hr
    have hright :
        (moveToken hpsi kind l r).2.last = r.last := by
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken]
          using hir
    exact ⟨hleft, hright⟩
  · have hir :=
      congrArg
        (fun q : State psi kappa => q.last) hr
    have hright :
        (moveToken hpsi kind l r).2.last = r.last := by
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken,
            birthFields]
          using hir
    exact ⟨hleft, hright⟩
private theorem selPairElimLast
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (eliminateLeaders l r).1.last = l.last ∧
      (eliminateLeaders l r).2.last = r.last := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    ⟨congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hl,
      congrArg
        (fun q : PPL.Elim.OtherFields
          psi kappa => q.last) hr⟩
private theorem selPairPplLastPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := selPairSelectedInput hpsi kind l r
    (ppl hpsi l r).1.last = p.1.last ∧
      (ppl hpsi l r).2.last = p.2.last := by
  cases kind with
  | black =>
      let p := selPairPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hb := selPairMoveTokenLast hpsi .black p.1 p.2
      have hw := selPairMoveTokenLast hpsi .white b.1 b.2
      have he := selPairElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            p.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            p.2.last
      exact
        ⟨he.1.trans (hw.1.trans hb.1),
          he.2.trans (hw.2.trans hb.2)⟩
  | white =>
      let p := selPairPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw := selPairMoveTokenLast hpsi .white b.1 b.2
      have he := selPairElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            b.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            b.2.last
      exact
        ⟨he.1.trans hw.1,
          he.2.trans hw.2⟩
private theorem selPairGhostStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      selPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    tokenAt kind
        ((ghostStep hpsi ring 0 G e).phys e) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind
        ((ghostStep hpsi ring 0 G e).phys
          (ring.rightNeighbor e)) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).2 := by
  dsimp only
  rw [ghostStep_phys_export]
  have hp :=
    selPairPplTokenPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    ⟨by rw [hl]; exact hp.1,
      by rw [hr]; exact hp.2⟩
private theorem selPairGhostStepTokenPairAt
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      selPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys e) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)) =
          tokenAt kind
            (moveToken hpsi kind p.1 p.2).2 := by
  have hphys :
      (ghostStep hpsi ring step G e).phys =
        (ghostStep hpsi ring 0 G e).phys := by
    calc
      (ghostStep hpsi ring step G e).phys =
          PopulationProtocol.step
            (protocol psi kappa) ring G.phys e :=
        ghostStep_phys_export hpsi ring step G e
      _ = (ghostStep hpsi ring 0 G e).phys :=
        (ghostStep_phys_export hpsi ring 0 G e).symm
  rw [hphys]
  exact
    selPairGhostStepTokenPair
      hpsi ring G e kind hne
private theorem selPairGhostStepLastPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      selPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    ((ghostStep hpsi ring step G e).phys e).last =
        p.1.last ∧
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).last =
        p.2.last := by
  dsimp only
  rw [ghostStep_phys_export]
  have hp :=
    selPairPplLastPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    ⟨by rw [hl]; exact hp.1,
      by rw [hr]; exact hp.2⟩
/-! -----------------------------------------------------------------------
    C_d geometry
------------------------------------------------------------------------ -/
private theorem selPairCd_fit
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 * psi ≤ n := by
  by_cases hfit : 2 * psi ≤ n
  · exact hfit
  · have hnlt : n < 2 * psi := by
      omega
    have hnpos : 0 < n := ring.hn
    let x0 : Fin (2 * psi) :=
      ⟨0, by omega⟩
    let xn : Fin (2 * psi) :=
      ⟨n, hnlt⟩
    have h0 := (hCd x0).1
    have hn := (hCd xn).1
    have hs :
        shiftRight ring k x0.val =
          shiftRight ring k xn.val := by
      apply Fin.ext
      dsimp [x0, xn]
      simp [shiftRight]
    rw [hs] at h0
    dsimp only [x0, xn] at h0 hn
    cases kind with
    | black =>
        have hmn :
            n % (2 * psi) = n :=
          Nat.mod_eq_of_lt hnlt
        simp only [tokenD'] at h0 hn
        have hzero :
            0 % (2 * psi) = 0 :=
          Nat.zero_mod (by omega)
        have h0' :
            (C (shiftRight ring k n)).dist.val = 0 := by
          calc
            (C (shiftRight ring k n)).dist.val =
                0 % (2 * psi) := h0
            _ = 0 := hzero
        have hn' :
            (C (shiftRight ring k n)).dist.val = n := by
          calc
            (C (shiftRight ring k n)).dist.val =
                (n + 0) % (2 * psi) := hn
            _ = n % (2 * psi) := by rw [Nat.add_zero]
            _ = n := hmn
        omega
    | white =>
        have hmpsi :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        simp only [tokenD'] at h0 hn
        rw [Nat.zero_add, hmpsi] at h0
        have heq :
            psi =
              (n + psi) % (2 * psi) := by
          omega
        by_cases hsmall :
            n + psi < 2 * psi
        · rw [Nat.mod_eq_of_lt hsmall] at heq
          omega
        · have hge :
              2 * psi ≤ n + psi := by
            omega
          have hrem :
              n + psi - 2 * psi <
                2 * psi := by
            omega
          rw [Nat.mod_eq_sub_mod hge,
            Nat.mod_eq_of_lt hrem] at heq
          omega
private theorem selPairRightNeighbor_ne
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
private theorem selPairLeftNeighborRightNeighbor
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
private theorem selPairRightNeighborShiftRight
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
private theorem selPairGhostSound_token
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value := by
  cases kind with
  | black =>
      exact (hsound.1 i z howner).1
  | white =>
      exact (hsound.2 i z howner).1
private theorem selPairOwner_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
private theorem selPairFirstNegativeTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) <
      tokenTargetCoordinate kind q t := by
  let c :=
    decodeOffset psi (tokenCode t)
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  have hb :
      1 - ((psi : Nat) : Int) ≤ c ∧
        c ≤ -1 := by
    rcases hv with hn | hp
    · exact hn
    · exfalso
      have hnegc : c < 0 := by
        simpa only [c] using hneg
      omega
  cases kind with
  | black =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist]
      simp only
        [Int.natCast_zero, Int.zero_add, Int.add_zero]
      change
        ((psi : Nat) : Int) <
          c % (((2 * psi : Nat)) : Int)
      have hperiod :
          c % (((2 * psi : Nat)) : Int) =
            (c + (((2 * psi : Nat)) : Int)) %
              (((2 * psi : Nat)) : Int) := by
        rw [Int.add_emod_right]
      rw [hperiod]
      rw [Int.emod_eq_of_lt
        (by omega) (by omega)]
      omega
  | white =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist]
      have hsum :
          ((psi : Nat) : Int) +
                c +
                ((psi : Nat) : Int) =
            c + (((2 * psi : Nat)) : Int) := by
        omega
      change
        ((psi : Nat) : Int) <
          (((psi : Nat) : Int) +
              c +
              ((psi : Nat) : Int)) %
            (((2 * psi : Nat)) : Int)
      rw [hsum]
      rw [Int.emod_eq_of_lt
        (by omega) (by omega)]
      omega
private theorem selPairNegative_not_first
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hsound : GhostSound G)
    (hx :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    x.val ≠ 0 := by
  intro hx0
  have htok :=
    selPairGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hvalid :=
    selPairOwner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner
  unfold ValidToken at hvalid
  rw [htok] at hvalid
  dsimp only at hvalid
  rcases hvalid with hp | hn
  · omega
  · have hrow := (hCd x).1
    rw [← hx] at hrow
    have hdist :
        (G.phys (ring.rightNeighbor e)).dist.val =
          tokenD' psi kind := by
      cases kind with
      | black =>
          simp only [tokenD'] at hrow ⊢
          have hmod : 0 % (2 * psi) = 0 :=
            Nat.zero_mod (by omega)
          rw [hx0, Nat.zero_add, hmod] at hrow
          exact hrow
      | white =>
          simp only [tokenD'] at hrow ⊢
          rw [hx0, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega)] at hrow
          exact hrow
    have ht :=
      selPairFirstNegativeTarget
        hpsi kind
        (G.phys (ring.rightNeighbor e))
        z.value hdist hneg
    omega
private theorem selPairPredecessorData
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hsound : GhostSound G)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    ∃ x : Fin (2 * psi), ∃ y : Fin (2 * psi),
      ring.rightNeighbor e =
          shiftRight ring k x.val ∧
        e = shiftRight ring k y.val ∧
        y.val + 1 = x.val := by
  rcases hwin with ⟨x, hx⟩
  have hx0 :=
    selPairNegative_not_first
      hpsi ring k kind G e x z
      hCd hsound hx howner hneg
  let y : Fin (2 * psi) :=
    ⟨x.val - 1, by omega⟩
  have hstep :
      ring.rightNeighbor
          (shiftRight ring k y.val) =
        shiftRight ring k x.val := by
    calc
      ring.rightNeighbor
            (shiftRight ring k y.val) =
          shiftRight ring k (y.val + 1) :=
        selPairRightNeighborShiftRight
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
  rw [selPairLeftNeighborRightNeighbor,
    selPairLeftNeighborRightNeighbor] at he
  exact
    ⟨x, y, hx, he,
      by dsimp [y]; omega⟩
private theorem selPairCd_last_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C)
    (i : Fin n)
    (hwin : Lemma4InWindow ring k psi i) :
    (C i).last = false := by
  rcases hwin with ⟨x, hx⟩
  have h := (hCd x).2
  rw [← hx] at h
  exact h
private theorem selPairCd_dist_same
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (hCd : Cd ring k kind C)
    (hCd' : Cd ring k kind C')
    (i : Fin n)
    (hwin : Lemma4InWindow ring k psi i) :
    (C' i).dist = (C i).dist := by
  rcases hwin with ⟨x, hx⟩
  have h0 := (hCd x).1
  have h1 := (hCd' x).1
  rw [← hx] at h0 h1
  apply Fin.ext
  exact h1.trans h0.symm
private theorem selPairProgress_dist_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t : TokenData psi)
    (hdist : q'.dist = q.dist) :
    lemma4TokenProgress kind q' t =
      lemma4TokenProgress kind q t := by
  unfold lemma4TokenProgress lemma4TokenStage
  unfold tokenTargetCoordinate
  rw [hdist]
private theorem selPairValid_same_dist
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
    (hvalid : ValidToken kind C i) :
    ValidToken kind C' i := by
  unfold ValidToken at hvalid ⊢
  rw [htok] at hvalid
  rw [htok']
  dsimp only at hvalid ⊢
  unfold tokenTargetCoordinate at hvalid ⊢
  rw [hdist]
  exact hvalid
private theorem selPairFresh_advance
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (z z' : GhostToken n psi)
    (hmeta :
      z'.lmeta = ghostStepLineageAdvance z.lmeta) :
    FreshAt kind k z.lmeta →
      FreshAt kind k z'.lmeta := by
  intro hfresh
  rcases hfresh with ⟨t, hid, hsite⟩
  refine ⟨t, ?_, ?_⟩
  · rw [hmeta]
    simpa [ghostStepLineageAdvance] using hid
  · rw [hmeta]
    simpa [ghostStepLineageAdvance] using hsite
private theorem selPairNegativeAbs
    {psi : Nat}
    {c : Int}
    (hvalid : ValidOffset psi c)
    (hc : c ≤ -2) :
    (c + 1).natAbs + 1 = c.natAbs ∧
      c.natAbs ≤ psi - 1 := by
  constructor
  · cases c with
    | ofNat m =>
        omega
    | negSucc m =>
        cases m with
        | zero =>
            omega
        | succ u =>
            rfl
  · rcases hvalid with hn | hp
    · cases c with
      | ofNat m =>
          have hmnonneg : (0 : Int) ≤ Int.ofNat m := by
            exact Int.natCast_nonneg m
          exfalso
          omega
      | negSucc m =>
          simp at hn ⊢
          omega
    · omega
private theorem selPairNegativeStep_target
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (t t' : TokenData psi)
    (hCd : Cd ring k kind C)
    (hCd' : Cd ring k kind C')
    (hxr :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hye :
      e = shiftRight ring k y.val)
    (hyx :
      y.val + 1 = x.val)
    (hc :
      decodeOffset psi (tokenCode t) ≤ -2)
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) + 1) :
    tokenTargetCoordinate kind (C' e) t' =
      tokenTargetCoordinate kind
        (C (ring.rightNeighbor e)) t := by
  have hpre := (hCd x).1
  have hpost := (hCd' y).1
  rw [← hxr] at hpre
  rw [← hye] at hpost
  cases kind with
  | black =>
      simp only [tokenD'] at hpre hpost
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt x.isLt] at hpre
      rw [Nat.add_zero,
        Nat.mod_eq_of_lt y.isLt] at hpost
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hpre, hpost, hc']
      congr 1
      omega
  | white =>
      simp only [tokenD'] at hpre hpost
      by_cases hxlt : x.val < psi
      · have hylt : y.val + psi < 2 * psi := by
          omega
        have hxl :
            x.val + psi < 2 * psi := by
          omega
        rw [Nat.mod_eq_of_lt hxl] at hpre
        rw [Nat.mod_eq_of_lt hylt] at hpost
        unfold tokenTargetCoordinate
        simp only [tokenD']
        rw [hpre, hpost, hc']
        congr 1
        omega
      · by_cases hxeq : x.val = psi
        · have hyval :
              y.val = psi - 1 := by
            omega
          have hpreSum :
              x.val + psi = 2 * psi := by
            omega
          have hpostSum :
              y.val + psi = 2 * psi - 1 := by
            omega
          rw [hpreSum, Nat.mod_self] at hpre
          rw [hpostSum,
            Nat.mod_eq_of_lt (by omega)] at hpost
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpre, hpost, hc']
          have hsum :
              (((2 * psi - 1 : Nat) : Int) +
                    (decodeOffset psi
                        (tokenCode t) + 1) +
                    ((psi : Nat) : Int)) =
                ((0 : Int) +
                    decodeOffset psi (tokenCode t) +
                    ((psi : Nat) : Int)) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right]
          rfl
        · have hxgt : psi < x.val := by
            omega
          have hpreGe :
              2 * psi ≤ x.val + psi := by
            omega
          have hpostGe :
              2 * psi ≤ y.val + psi := by
            omega
          have hpreLt :
              x.val + psi - 2 * psi <
                2 * psi := by
            omega
          have hpostLt :
              y.val + psi - 2 * psi <
                2 * psi := by
            omega
          rw [Nat.mod_eq_sub_mod hpreGe,
            Nat.mod_eq_of_lt hpreLt] at hpre
          rw [Nat.mod_eq_sub_mod hpostGe,
            Nat.mod_eq_of_lt hpostLt] at hpost
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpre, hpost, hc']
          congr 1
          omega
private theorem selPairNegativeStep_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (i j : Fin n)
    (t t' : TokenData psi)
    (htok :
      tokenAt kind (C i) = some t)
    (htok' :
      tokenAt kind (C' j) = some t')
    (hvalid :
      ValidToken kind C i)
    (hc :
      decodeOffset psi (tokenCode t) ≤ -2)
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) + 1)
    (htarget :
      tokenTargetCoordinate kind (C' j) t' =
        tokenTargetCoordinate kind (C i) t) :
    ValidToken kind C' j := by
  unfold ValidToken at hvalid ⊢
  rw [htok] at hvalid
  rw [htok']
  dsimp only at hvalid ⊢
  rcases hvalid with hp | hn
  · omega
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [hc']
      omega
    · rw [htarget]
      exact hn.2.1
    · rw [htarget]
      exact hn.2.2
private theorem selPairNegativeStep_progress
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) ≤ -2)
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) + 1)
    (htarget :
      tokenTargetCoordinate kind q' t' =
        tokenTargetCoordinate kind q t) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  let c :=
    decodeOffset psi (tokenCode t)
  have hpsi0 : 0 < psi := by
    have hcode := (tokenCode t).isLt
    omega
  have hv :=
    decodeOffset_valid
      psi hpsi0 (tokenCode t)
  have habs :=
    selPairNegativeAbs
      hv (by simpa [c] using hc)
  have hnot :
      ¬ 0 < decodeOffset psi (tokenCode t) := by
    omega
  have hcnew :
      decodeOffset psi (tokenCode t') ≤ -1 := by
    rw [hc']
    omega
  have hnot' :
      ¬ 0 < decodeOffset psi (tokenCode t') := by
    omega
  unfold lemma4TokenProgress lemma4TokenStage
  simp only [hnot, hnot', if_false]
  rw [hc', htarget]
  generalize
    ((tokenTargetCoordinate kind q t).toNat +
        psi - 1 - psi) *
      (2 * psi - 1) = B
  omega
private theorem selPairServiceEdge_negative
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    e =
      lemma4ServiceEdge
        ring kind G (ring.rightNeighbor e) z := by
  unfold lemma4ServiceEdge
  rw [if_neg (by omega)]
  exact
    (selPairLeftNeighborRightNeighbor
      ring e).symm

private theorem selPairTurn_negTurnGeometry
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (t t' : TokenData psi)
    (hCd : Cd ring k kind C)
    (hCd' : Cd ring k kind C')
    (hxr :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hye :
      e = shiftRight ring k y.val)
    (hyx :
      y.val + 1 = x.val)
    (htok :
      tokenAt kind (C (ring.rightNeighbor e)) =
        some t)
    (hvalid :
      ValidToken kind C (ring.rightNeighbor e))
    (hc :
      decodeOffset psi (tokenCode t) = -1)
    (hc' :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int)) :
    1 ≤ y.val ∧
      y.val < psi ∧
      tokenTargetCoordinate
          kind (C (ring.rightNeighbor e)) t =
        (y.val : Int) ∧
      tokenTargetCoordinate kind (C' e) t' =
        ((y.val + psi : Nat) : Int) := by
  have hvalid' := hvalid
  unfold ValidToken at hvalid'
  rw [htok] at hvalid'
  dsimp only at hvalid'
  rcases hvalid' with hp | hn
  · rw [hc] at hp
    omega
  · have hpre := (hCd x).1
    have hpost := (hCd' y).1
    rw [← hxr] at hpre
    rw [← hye] at hpost

    cases kind with
    | black =>
        simp only [tokenD'] at hpre hpost

        rw [Nat.add_zero,
          Nat.mod_eq_of_lt x.isLt] at hpre
        rw [Nat.add_zero,
          Nat.mod_eq_of_lt y.isLt] at hpost

        have hold :
            tokenTargetCoordinate
                .black
                (C (ring.rightNeighbor e)) t =
              (y.val : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpre, hc]
          have heq :
              (x.val : Int) + (-1 : Int) +
                    ((0 : Nat) : Int) =
                (y.val : Int) := by
            omega
          rw [heq]
          rw [Int.emod_eq_of_lt
            (by omega) (by
              have hy := y.isLt
              omega)]

        have hylo : 1 ≤ y.val := by
          rw [hold] at hn
          omega
        have hylt : y.val < psi := by
          rw [hold] at hn
          omega

        have hnew :
            tokenTargetCoordinate
                .black (C' e) t' =
              ((y.val + psi : Nat) : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpost, hc']
          have heq :
              (y.val : Int) +
                    ((psi : Nat) : Int) +
                    ((0 : Nat) : Int) =
                ((y.val + psi : Nat) : Int) := by
            omega
          rw [heq]
          rw [Int.emod_eq_of_lt
            (by omega) (by omega)]

        exact
          ⟨hylo, hylt, hold, hnew⟩

    | white =>
        simp only [tokenD'] at hpre hpost

        have hold :
            tokenTargetCoordinate
                .white
                (C (ring.rightNeighbor e)) t =
              (y.val : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hc]

          by_cases hxlt : x.val < psi
          · have hsumlt :
                x.val + psi < 2 * psi := by
              omega
            rw [Nat.mod_eq_of_lt hsumlt] at hpre
            rw [hpre]
            have heq :
                ((x.val + psi : Nat) : Int) +
                      (-1 : Int) +
                      ((psi : Nat) : Int) =
                  (y.val : Int) +
                    (((2 * psi : Nat)) : Int) := by
              omega
            rw [heq, Int.add_emod_right]
            rw [Int.emod_eq_of_lt
              (by omega) (by
                have hy := y.isLt
                omega)]

          · by_cases hxeq : x.val = psi
            · have hsum :
                  x.val + psi = 2 * psi := by
                omega
              rw [hsum, Nat.mod_self] at hpre
              rw [hpre]
              have heq :
                  ((0 : Nat) : Int) + (-1 : Int) +
                        ((psi : Nat) : Int) =
                    (y.val : Int) := by
                omega
              rw [heq]
              rw [Int.emod_eq_of_lt
                (by omega) (by
                  have hy := y.isLt
                  omega)]

            · have hxge :
                  2 * psi ≤ x.val + psi := by
                omega
              have hrem :
                  x.val + psi - 2 * psi <
                    2 * psi := by
                omega
              rw [Nat.mod_eq_sub_mod hxge,
                Nat.mod_eq_of_lt hrem] at hpre
              rw [hpre]
              have heq :
                  ((x.val + psi - 2 * psi : Nat) : Int) +
                        (-1 : Int) +
                        ((psi : Nat) : Int) =
                    (y.val : Int) := by
                omega
              rw [heq]
              rw [Int.emod_eq_of_lt
                (by omega) (by
                  have hy := y.isLt
                  omega)]

        have hylo : 1 ≤ y.val := by
          rw [hold] at hn
          omega
        have hylt : y.val < psi := by
          rw [hold] at hn
          omega

        have hpostlt :
            y.val + psi < 2 * psi := by
          omega
        rw [Nat.mod_eq_of_lt hpostlt] at hpost

        have hnew :
            tokenTargetCoordinate
                .white (C' e) t' =
              ((y.val + psi : Nat) : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpost, hc']
          have hsum :
              ((y.val + psi : Nat) : Int) +
                    ((psi : Nat) : Int) +
                    ((psi : Nat) : Int) =
                ((y.val + psi : Nat) : Int) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right]
          rw [Int.emod_eq_of_lt
            (by omega) (by omega)]

        exact
          ⟨hylo, hylt, hold, hnew⟩

private theorem selPairTurn_negTurn_valid
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (C' : Config n psi kappa)
    (e : Fin n)
    (t' : TokenData psi)
    (htok' :
      tokenAt kind (C' e) = some t')
    (hc' :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int))
    (y : Nat)
    (hylt : y < psi)
    (htarget :
      tokenTargetCoordinate kind (C' e) t' =
        ((y + psi : Nat) : Int)) :
    ValidToken kind C' e := by
  unfold ValidToken
  rw [htok']
  dsimp only
  left
  refine And.intro ?_ (And.intro ?_ ?_)
  · rw [hc']
    omega
  · rw [htarget]
    omega
  · rw [htarget]
    omega

/--
The public rank increases by exactly one across the c=-1 -> +psi turn.
The calculation uses only the two target coordinates supplied by C_d.
-/
private theorem selPairTurn_negTurn_progress
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (y : Nat)
    (hypos : 0 < y)
    (hc :
      decodeOffset psi (tokenCode t) = -1)
    (hc' :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int))
    (hold :
      tokenTargetCoordinate kind q t =
        (y : Int))
    (hnew :
      tokenTargetCoordinate kind q' t' =
        ((y + psi : Nat) : Int)) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  have hneg :
      ¬ 0 < decodeOffset psi (tokenCode t) := by
    rw [hc]
    omega
  have hpos :
      0 < decodeOffset psi (tokenCode t') := by
    rw [hc']
    omega
  have habs :
      (decodeOffset psi (tokenCode t)).natAbs = 1 := by
    rw [hc]
    rfl
  have hto :
      (decodeOffset psi (tokenCode t')).toNat = psi := by
    rw [hc']
    simp
  have holdNat :
      (tokenTargetCoordinate kind q t).toNat = y := by
    rw [hold]
    simp
  have hnewNat :
      (tokenTargetCoordinate kind q' t').toNat =
        y + psi := by
    rw [hnew]
    change (Int.ofNat (y + psi)).toNat = y + psi
    rfl

  unfold lemma4TokenProgress lemma4TokenStage
  simp only [hneg, hpos, if_false, if_true]
  rw [holdNat, hnewNat, habs, hto]

  have hstageOld :
      y + psi - 1 - psi = y - 1 := by
    omega
  have hstageNew :
      y + psi - psi = y := by
    omega
  rw [hstageOld, hstageNew]
  simp only [Nat.sub_self, Nat.add_zero]

  let D : Nat := 2 * psi - 1
  have hDpos : 0 < D := by
    dsimp [D]
    omega
  have hydec :
      y = (y - 1) + 1 := by
    omega
  change
    y * D =
      (y - 1) * D + (D - 1) + 1
  calc
    y * D =
        ((y - 1) + 1) * D := by
      rw [← hydec]
    _ = (y - 1) * D + D := by
      rw [Nat.add_mul, Nat.one_mul]
    _ = (y - 1) * D + (D - 1) + 1 := by
      omega

/-! -----------------------------------------------------------------------
    Selected-input frames used by the direct responder classifier
------------------------------------------------------------------------ -/

private theorem selPairBlackPreservesWhite
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

private theorem selPairPreludeTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := selPairPrelude hpsi l r
    And
      (tokenAt kind p.1 = tokenAt kind l)
      (tokenAt kind p.2 = tokenAt kind r) := by
  have hd :
      tokenAt kind (determineMode l r).1 =
          tokenAt kind l ∧
        tokenAt kind (determineMode l r).2 =
          tokenAt kind r := by
    cases kind with
    | black =>
        simp only [tokenAt, determineMode]
        repeat' (first
          | split <;> try dsimp only
          | rfl)
        all_goals exact And.intro rfl rfl
    | white =>
        simp only [tokenAt, determineMode]
        repeat' (first
          | split <;> try dsimp only
          | rfl)
        all_goals exact And.intro rfl rfl
  have hs :
      let q := createLeaderThroughLine6 hpsi l r
      tokenAt kind q.left = tokenAt kind l ∧
        tokenAt kind q.right = tokenAt kind r := by
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
        rw [selPairSourceBirth_eq]
        cases kind <;>
          simpa only [selPairLeaderBirth, tokenAt]
            using hd.2
      · simp only
          [createLeaderThroughLine6, if_neg hguard]
        exact hd.2
  dsimp only at hs
  have hp :
      tokenAt kind (selPairPrelude hpsi l r).1 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).left ∧
        tokenAt kind (selPairPrelude hpsi l r).2 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).right := by
    cases kind with
    | black =>
        simp only [selPairPrelude, tokenAt]
        repeat' (first
          | split <;> try dsimp only
          | rfl)
        all_goals exact And.intro rfl rfl
    | white =>
        simp only [selPairPrelude, tokenAt]
        repeat' (first
          | split <;> try dsimp only
          | rfl)
        all_goals exact And.intro rfl rfl
  exact
    And.intro
      (hp.1.trans hs.1)
      (hp.2.trans hs.2)

private theorem selPairSelectedInputTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := selPairSelectedInput hpsi kind l r
    And
      (tokenAt kind p.1 = tokenAt kind l)
      (tokenAt kind p.2 = tokenAt kind r) := by
  cases kind with
  | black =>
      exact
        selPairPreludeTokenFrame
          hpsi .black l r
  | white =>
      let p := selPairPrelude hpsi l r
      have hp :=
        selPairPreludeTokenFrame
          hpsi .white l r
      have hb :=
        selPairBlackPreservesWhite
          hpsi p.1 p.2
      dsimp only [selPairSelectedInput]
      exact
        And.intro
          (hb.1.trans hp.1)
          (hb.2.trans hp.2)

private theorem selPairMoveTokenDist
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
  have hil :=
    congrArg
      (fun q : State psi kappa => q.dist) hi
  have hl :
      (moveToken hpsi kind l r).1.dist =
        l.dist := by
    cases kind <;>
      simpa [eraseKindToken] using hil
  have hrCases :=
    moveToken_responder_fields
      hpsi kind l r
  have hr :
      (moveToken hpsi kind l r).2.dist =
        r.dist := by
    rcases hrCases with hstay | hborn
    · have h :=
        congrArg
          (fun q : State psi kappa => q.dist) hstay
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken]
          using h
    · have h :=
        congrArg
          (fun q : State psi kappa => q.dist) hborn
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken,
            birthFields]
          using h
  exact And.intro hl hr

private theorem selPairElimDist
    {psi kappa : Nat}
    (l r : State psi kappa) :
    And
      ((eliminateLeaders l r).1.dist = l.dist)
      ((eliminateLeaders l r).2.dist = r.dist) := by
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

private theorem selPairPplDistPair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := selPairSelectedInput hpsi kind l r
    And
      ((ppl hpsi l r).1.dist = p.1.dist)
      ((ppl hpsi l r).2.dist = p.2.dist) := by
  cases kind with
  | black =>
      let p := selPairPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hb := selPairMoveTokenDist hpsi .black p.1 p.2
      have hw := selPairMoveTokenDist hpsi .white b.1 b.2
      have he := selPairElimDist w.1 w.2
      change
        And
          ((eliminateLeaders w.1 w.2).1.dist =
            p.1.dist)
          ((eliminateLeaders w.1 w.2).2.dist =
            p.2.dist)
      exact
        And.intro
          (he.1.trans (hw.1.trans hb.1))
          (he.2.trans (hw.2.trans hb.2))
  | white =>
      let p := selPairPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw := selPairMoveTokenDist hpsi .white b.1 b.2
      have he := selPairElimDist w.1 w.2
      change
        And
          ((eliminateLeaders w.1 w.2).1.dist =
            b.1.dist)
          ((eliminateLeaders w.1 w.2).2.dist =
            b.2.dist)
      exact
        And.intro
          (he.1.trans hw.1)
          (he.2.trans hw.2)

private theorem selPairGhostStepDistPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      selPairSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    And
      (((ghostStep hpsi ring step G e).phys e).dist =
        p.1.dist)
      (((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).dist =
        p.2.dist) := by
  dsimp only
  rw [ghostStep_phys_export]
  have hp :=
    selPairPplDistPair
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hl :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  have hr :
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]
  exact
    And.intro
      (by rw [hl]; exact hp.1)
      (by rw [hr]; exact hp.2)

private theorem selPairSelectedInputDistLeft
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
    (hwin : Lemma4InWindow ring k psi e) :
    (selPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).1.dist =
      (G.phys e).dist := by
  have hp :=
    selPairGhostStepDistPair
      hpsi ring step G e kind hne
  have hc :=
    selPairCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' e hwin
  exact hp.1.symm.trans hc

private theorem selPairSelectedInputDistRight
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
    (selPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).2.dist =
      (G.phys (ring.rightNeighbor e)).dist := by
  have hp :=
    selPairGhostStepDistPair
      hpsi ring step G e kind hne
  have hc :=
    selPairCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd'
      (ring.rightNeighbor e) hwin
  exact hp.2.symm.trans hc

private theorem selPairShiftRightInjectiveLt
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (a b : Nat)
    (ha : a < n)
    (hb : b < n)
    (h :
      shiftRight ring k a =
        shiftRight ring k b) :
    a = b := by
  have hv := congrArg Fin.val h
  simp only [shiftRight] at hv
  by_cases hka : k.val + a < n
  · rw [Nat.mod_eq_of_lt hka] at hv
    by_cases hkb : k.val + b < n
    · rw [Nat.mod_eq_of_lt hkb] at hv
      omega
    · have hgeb : n <= k.val + b := by omega
      have hltb : k.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hgeb,
        Nat.mod_eq_of_lt hltb] at hv
      omega
  · have hgea : n <= k.val + a := by omega
    have hlta : k.val + a - n < n := by omega
    rw [Nat.mod_eq_sub_mod hgea,
      Nat.mod_eq_of_lt hlta] at hv
    by_cases hkb : k.val + b < n
    · rw [Nat.mod_eq_of_lt hkb] at hv
      omega
    · have hgeb : n <= k.val + b := by omega
      have hltb : k.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hgeb,
        Nat.mod_eq_of_lt hltb] at hv
      omega

private def selPairNegStepNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) <= -2) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hv : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  selPairMkToken
    (encodeOffset psi (c + 1) (by
      rcases hv with hn | hp
      · left
        omega
      · exfalso
        omega))
    t.1.2 t.2

private theorem selPairNegStepNext_offset
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) <= -2) :
    decodeOffset psi
        (tokenCode
          (selPairNegStepNext hpsi t hc)) =
      decodeOffset psi (tokenCode t) + 1 := by
  dsimp [selPairNegStepNext, selPairMkToken, tokenCode]
  exact decode_encode _ _ _

private theorem selPairNegTurnNext_offset
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (selPairNegTurnNext hpsi sourceBit t)) =
      ((psi : Nat) : Int) := by
  unfold selPairNegTurnNext
  by_cases hcarry : t.2 = (1 : Fin 2)
  · rw [if_pos hcarry]
    dsimp [selPairMkToken, tokenCode]
    exact decodeOffset_psi psi hpsi
  · rw [if_neg hcarry]
    dsimp [selPairMkToken, tokenCode]
    exact decodeOffset_psi psi hpsi

private def selPairGhostFinish
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
      if c = 1 then
        let next :=
          selPairMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          selPairBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hbranch : 2 ≤ c := h2
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          selPairMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          selPairBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if cr = -1 then
              let next :=
                selPairNegTurnNext hpsi l.id tr
              let b :=
                selPairBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hbranch : cr ≤ -2 := hm2
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                selPairMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                selPairBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  | none =>
      match rv0 with
      | none =>
          ⟨gl2, gr0, []⟩
      | some tr =>
          let cr := decodeOffset psi (tokenCode tr)
          if cr = -1 then
            let next :=
              selPairNegTurnNext hpsi l.id tr
            let b :=
              selPairBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hbranch : cr ≤ -2 := hm2
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              selPairMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b :=
              selPairBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private theorem selPairMoveToken_positive
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (htok : tokenAt kind r = some t)
    (hvalid : selPairLocalValid kind r t)
    (hc : 0 < decodeOffset psi (tokenCode t)) :
    tokenAt kind (moveToken hpsi kind l r).2 =
      some t := by
  have hrv :
      selPairLiveValue kind r = some t :=
    selPairLiveValue_some kind r t htok hvalid
  have hm1 :
      decodeOffset psi (tokenCode t) ≠ -1 := by
    omega
  have hm2 :
      ¬ decodeOffset psi (tokenCode t) ≤ -2 := by
    omega
  rw [← selPairMoveToken_eq hpsi kind l r]
  by_cases hgate : l.last = false ∧ r.last = false
  · cases hlv : selPairLiveValue kind l with
    | none =>
        by_cases hd :
            (sourceClear kind l).dist.val =
              tokenD' psi kind
        · unfold selPairMoveToken
          simp
            [selPairSourceClear_token,
              selPairSourceClear_last,
              selPairSourceSet_token,
              hgate, hlv, hrv, hd, hm1, hm2]
        · unfold selPairMoveToken
          simp
            [selPairSourceClear_token,
              selPairSourceClear_last,
              selPairSourceSet_token,
              hgate, hlv, hrv, hd, hm1, hm2]
    | some u =>
        unfold selPairMoveToken
        simp
          [selPairSourceClear_token,
            selPairSourceClear_last,
            selPairSourceSet_token,
            hgate, hlv, hrv, hm1, hm2]
  · unfold selPairMoveToken
    simp
      [selPairSourceClear_token,
        selPairSourceClear_last,
        hgate, hrv]

private theorem selPairMoveToken_negTurn
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind r = some t)
    (hvalid : selPairLocalValid kind r t)
    (hc : decodeOffset psi (tokenCode t) = -1) :
    tokenAt kind (moveToken hpsi kind l r).1 =
      some (selPairNegTurnNext hpsi l.id t) := by
  have hrv :
      selPairLiveValue kind r = some t :=
    selPairLiveValue_some kind r t htok hvalid
  rw [← selPairMoveToken_eq hpsi kind l r]
  cases hlv : selPairLiveValue kind l with
  | none =>
      by_cases hd :
          (sourceClear kind l).dist.val =
            tokenD' psi kind
      · unfold selPairMoveToken
        simp
          [selPairSourceClear_token,
            selPairSourceClear_last,
            selPairSourceClear_id,
            selPairSourceSet_token,
            selPairSourceSet_id,
            hgate, hlv, hrv, hd, hc]
      · unfold selPairMoveToken
        simp
          [selPairSourceClear_token,
            selPairSourceClear_last,
            selPairSourceClear_id,
            selPairSourceSet_token,
            selPairSourceSet_id,
            hgate, hlv, hrv, hd, hc]
  | some u =>
      unfold selPairMoveToken
      simp
        [selPairSourceClear_token,
          selPairSourceClear_last,
          selPairSourceClear_id,
          selPairSourceSet_token,
          selPairSourceSet_id,
          hgate, hlv, hrv, hc]

private theorem selPairMoveToken_negStep
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hc : decodeOffset psi (tokenCode t) ≤ -2)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind r = some t)
    (hvalid : selPairLocalValid kind r t) :
    tokenAt kind (moveToken hpsi kind l r).1 =
      some (selPairNegStepNext hpsi t hc) := by
  have hrv :
      selPairLiveValue kind r = some t :=
    selPairLiveValue_some kind r t htok hvalid
  have hm1 :
      decodeOffset psi (tokenCode t) ≠ -1 := by
    omega
  rw [← selPairMoveToken_eq hpsi kind l r]
  cases hlv : selPairLiveValue kind l with
  | none =>
      by_cases hd :
          (sourceClear kind l).dist.val =
            tokenD' psi kind
      · unfold selPairMoveToken
        simp
          [selPairSourceClear_token,
            selPairSourceClear_last,
            selPairSourceSet_token,
            hgate, hlv, hrv, hd, hm1, hc,
            selPairNegStepNext]
      · unfold selPairMoveToken
        simp
          [selPairSourceClear_token,
            selPairSourceClear_last,
            selPairSourceSet_token,
            hgate, hlv, hrv, hd, hm1, hc,
            selPairNegStepNext]
  | some u =>
      unfold selPairMoveToken
      simp
        [selPairSourceClear_token,
          selPairSourceClear_last,
          selPairSourceSet_token,
          hgate, hlv, hrv, hm1, hc,
          selPairNegStepNext]

private theorem selPairPositiveShape
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgr : gr = some z)
    (htok : tokenAt kind r = some z.value)
    (hvalid : selPairLocalValid kind r z.value)
    (hc : 0 < decodeOffset psi (tokenCode z.value)) :
    (selPairGhostMoveToken
        hpsi kind step site l r gl gr).right =
          some z ∧
      tokenAt kind (moveToken hpsi kind l r).2 =
          some z.value ∧
      (gl = none →
        (selPairGhostMoveToken
          hpsi kind step site l r gl gr).left =
            none) := by
  classical
  have hphys :
      tokenAt kind (moveToken hpsi kind l r).2 =
        some z.value :=
    selPairMoveToken_positive
      hpsi kind l r z.value htok hvalid hc
  have hm1 :
      decodeOffset psi (tokenCode z.value) ≠ -1 := by
    omega
  have hm2 :
      ¬ decodeOffset psi (tokenCode z.value) ≤ -2 := by
    omega
  by_cases hgate : l.last = false ∧ r.last = false
  · let lv0 := selPairLiveValue kind l
    let rv0 := selPairLiveValue kind r
    let gl0 := selPairLiveShadow kind l gl
    let gr0 := selPairLiveShadow kind r gr
    let guard :=
      l.dist.val = tokenD' psi kind ∧ lv0 = none
    let birth :=
      selPairBirthGhost hpsi kind step site l.id
    let lv1 :=
      if guard then some birth.value else lv0
    let gl1 :=
      if guard then some birth else gl0
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    have hrv0 : rv0 = some z.value := by
      dsimp only [rv0]
      exact
        selPairLiveValue_some
          kind r z.value htok hvalid
    have hgr0 : gr0 = some z := by
      dsimp only [gr0]
      exact
        selPairLiveShadow_some
          kind r gr z hgr htok hvalid
    have hlv2 : lv2 = none := by
      cases hlv1 : lv1 with
      | none =>
          have hcol : ¬ collide := by
            simp [collide, hlv1]
          simp [lv2, hcol, hlv1]
      | some u =>
          have hcol : collide := by
            simp [collide, hlv1, hrv0]
          simp [lv2, hcol]
    have hMoveEq :
        selPairGhostMoveToken
            hpsi kind step site l r gl gr =
          selPairGhostFinish
            hpsi kind l r lv2 rv0 gl2 gr0 := by
      unfold selPairGhostMoveToken
      simp only [if_pos hgate]
      rfl
    have hright :
        (selPairGhostMoveToken
          hpsi kind step site l r gl gr).right =
            some z := by
      rw [hMoveEq, hlv2, hrv0, hgr0]
      unfold selPairGhostFinish
      simp only [if_neg hm1, dif_neg hm2]
    have hleft :
        gl = none →
          (selPairGhostMoveToken
            hpsi kind step site l r gl gr).left =
              none := by
      intro hgl
      have hgl0 : gl0 = none := by
        dsimp only [gl0]
        rw [hgl]
        rfl
      have hgl2 : gl2 = none := by
        by_cases hg : guard
        · have hcol : collide := by
            simp [collide, lv1, hg, hrv0]
          simp [gl2, hcol]
        · have hgl1 : gl1 = none := by
            simp [gl1, hg, hgl0]
          by_cases hcol : collide
          · simp [gl2, hcol]
          · simp [gl2, hcol, hgl1]
      rw [hMoveEq, hgl2, hlv2, hrv0, hgr0]
      unfold selPairGhostFinish
      simp only [if_neg hm1, dif_neg hm2]
    exact ⟨hright, hphys, hleft⟩
  · have hgr0 :
        selPairLiveShadow kind r gr = some z :=
      selPairLiveShadow_some
        kind r gr z hgr htok hvalid
    have hright :
        (selPairGhostMoveToken
          hpsi kind step site l r gl gr).right =
            some z := by
      unfold selPairGhostMoveToken
      simp only [if_neg hgate]
      exact hgr0
    have hleft :
        gl = none →
          (selPairGhostMoveToken
            hpsi kind step site l r gl gr).left =
              none := by
      intro hgl
      unfold selPairGhostMoveToken
      simp only [if_neg hgate]
      rw [hgl]
      rfl
    exact ⟨hright, hphys, hleft⟩

private theorem selPairNegTurnShape
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgr : gr = some z)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind r = some z.value)
    (hvalid : selPairLocalValid kind r z.value)
    (hc : decodeOffset psi (tokenCode z.value) = -1)
    (hnext :
      selPairLocalValid kind l
        (selPairNegTurnNext hpsi l.id z.value)) :
    (selPairGhostMoveToken
        hpsi kind step site l r gl gr).left =
          some
            { value := selPairNegTurnNext hpsi l.id z.value
              lmeta := ghostStepLineageAdvance z.lmeta } ∧
      (selPairGhostMoveToken
        hpsi kind step site l r gl gr).right =
          none ∧
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (selPairNegTurnNext hpsi l.id z.value) := by
  classical
  let lv0 := selPairLiveValue kind l
  let rv0 := selPairLiveValue kind r
  let gl0 := selPairLiveShadow kind l gl
  let gr0 := selPairLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    selPairBirthGhost hpsi kind step site l.id
  let lv1 :=
    if guard then some birth.value else lv0
  let gl1 :=
    if guard then some birth else gl0
  let collide := lv1 ≠ none ∧ rv0 ≠ none
  let lv2 := if collide then none else lv1
  let gl2 := if collide then none else gl1
  have hrv0 : rv0 = some z.value := by
    dsimp only [rv0]
    exact
      selPairLiveValue_some
        kind r z.value htok hvalid
  have hgr0 : gr0 = some z := by
    dsimp only [gr0]
    exact
      selPairLiveShadow_some
        kind r gr z hgr htok hvalid
  have hlv2 : lv2 = none := by
    cases hlv1 : lv1 with
    | none =>
        have hcol : ¬ collide := by
          simp [collide, hlv1]
        simp [lv2, hcol, hlv1]
    | some u =>
        have hcol : collide := by
          simp [collide, hlv1, hrv0]
        simp [lv2, hcol]
  have hMoveEq :
      selPairGhostMoveToken
          hpsi kind step site l r gl gr =
        selPairGhostFinish
          hpsi kind l r lv2 rv0 gl2 gr0 := by
    unfold selPairGhostMoveToken
    simp only [if_pos hgate]
    rfl
  have hghost :
      (selPairGhostMoveToken
          hpsi kind step site l r gl gr).left =
            some
              { value := selPairNegTurnNext hpsi l.id z.value
                lmeta := ghostStepLineageAdvance z.lmeta } ∧
        (selPairGhostMoveToken
          hpsi kind step site l r gl gr).right =
            none := by
    rw [hMoveEq, hlv2, hrv0, hgr0]
    unfold selPairGhostFinish
    simp only
      [if_pos hc, selPairBumpTo, if_pos hnext, and_self]
  have hphys :
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (selPairNegTurnNext hpsi l.id z.value) :=
    selPairMoveToken_negTurn
      hpsi kind l r z.value
      hgate htok hvalid hc
  exact ⟨hghost.1, hghost.2, hphys⟩

private theorem selPairNegStepShape
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hc : decodeOffset psi (tokenCode z.value) ≤ -2)
    (hgr : gr = some z)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind r = some z.value)
    (hvalid : selPairLocalValid kind r z.value)
    (hnext :
      selPairLocalValid kind l
        (selPairNegStepNext hpsi z.value hc)) :
    (selPairGhostMoveToken
        hpsi kind step site l r gl gr).left =
          some
            { value := selPairNegStepNext hpsi z.value hc
              lmeta := ghostStepLineageAdvance z.lmeta } ∧
      (selPairGhostMoveToken
        hpsi kind step site l r gl gr).right =
          none ∧
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (selPairNegStepNext hpsi z.value hc) := by
  classical
  have hm1 :
      decodeOffset psi (tokenCode z.value) ≠ -1 := by
    omega
  let lv0 := selPairLiveValue kind l
  let rv0 := selPairLiveValue kind r
  let gl0 := selPairLiveShadow kind l gl
  let gr0 := selPairLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    selPairBirthGhost hpsi kind step site l.id
  let lv1 :=
    if guard then some birth.value else lv0
  let gl1 :=
    if guard then some birth else gl0
  let collide := lv1 ≠ none ∧ rv0 ≠ none
  let lv2 := if collide then none else lv1
  let gl2 := if collide then none else gl1
  have hrv0 : rv0 = some z.value := by
    dsimp only [rv0]
    exact
      selPairLiveValue_some
        kind r z.value htok hvalid
  have hgr0 : gr0 = some z := by
    dsimp only [gr0]
    exact
      selPairLiveShadow_some
        kind r gr z hgr htok hvalid
  have hlv2 : lv2 = none := by
    cases hlv1 : lv1 with
    | none =>
        have hcol : ¬ collide := by
          simp [collide, hlv1]
        simp [lv2, hcol, hlv1]
    | some u =>
        have hcol : collide := by
          simp [collide, hlv1, hrv0]
        simp [lv2, hcol]
  have hMoveEq :
      selPairGhostMoveToken
          hpsi kind step site l r gl gr =
        selPairGhostFinish
          hpsi kind l r lv2 rv0 gl2 gr0 := by
    unfold selPairGhostMoveToken
    simp only [if_pos hgate]
    rfl
  have hghost :
      (selPairGhostMoveToken
          hpsi kind step site l r gl gr).left =
            some
              { value := selPairNegStepNext hpsi z.value hc
                lmeta := ghostStepLineageAdvance z.lmeta } ∧
        (selPairGhostMoveToken
          hpsi kind step site l r gl gr).right =
            none := by
    have hnext' := hnext
    unfold selPairNegStepNext at hnext'
    rw [hMoveEq, hlv2, hrv0, hgr0]
    unfold selPairGhostFinish
    simp only
      [if_neg hm1, dif_pos hc,
        selPairBumpTo, if_pos hnext,
        selPairNegStepNext, if_pos hnext', and_self]
  have hphys :
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (selPairNegStepNext hpsi z.value hc) :=
    selPairMoveToken_negStep
      hpsi kind l r z.value hc
      hgate htok hvalid
  exact ⟨hghost.1, hghost.2, hphys⟩

private theorem selPairRightmostPositive
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi)
    (hfit : 2 * psi <= n)
    (hne : ring.rightNeighbor e ≠ e)
    (hright : Lemma4RightmostAt ring k kind G x z)
    (htrack :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right =
        some z)
    (hleftNone :
      ghostTokenAt kind G e = none ->
        (ghostStepSelectedPair
          hpsi ring step G e kind).left = none)
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)) :
    Lemma4RightmostAt ring k kind
      (ghostStep hpsi ring step G e) x z := by
  have hright0 := hright
  unfold Lemma4RightmostAt at hright0
  dsimp only at hright0
  unfold Lemma4RightmostAt
  dsimp only
  refine And.intro ?_ (And.intro ?_ ?_)
  · rw [← htrack]
    exact
      (ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e kind hne).trans
        hpairRight
  · rw [← htrack]
    exact hvalid
  · intro y hy
    let j := shiftRight ring k y.val
    have hpreNone :
        ghostTokenAt kind G j = none := by
      exact hright0.2.2 y hy
    by_cases hje : j = e
    · have hpreE :
          ghostTokenAt kind G e = none := by
        rw [← hje]
        exact hpreNone
      have hp := hleftNone hpreE
      change
        ghostTokenAt kind
          (ghostStep hpsi ring step G e) j = none
      rw [hje]
      exact
        (ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind).trans hp
    · have hjr : j ≠ ring.rightNeighbor e := by
        intro hj
        have hs :
            shiftRight ring k y.val =
              shiftRight ring k x.val := by
          calc
            shiftRight ring k y.val = j := rfl
            _ = ring.rightNeighbor e := hj
            _ = shiftRight ring k x.val := htrack
        have hv :=
          selPairShiftRightInjectiveLt
            ring k y.val x.val
            (by omega) (by omega) hs
        omega
      rw [ghostTokenAt_ghostStep_frame
        hpsi ring step G e j kind hje hjr]
      exact hpreNone

private theorem selPairRightmostMovedLeft
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (z z' : GhostToken n psi)
    (hfit : 2 * psi <= n)
    (hne : ring.rightNeighbor e ≠ e)
    (hright : Lemma4RightmostAt ring k kind G x z)
    (htrack :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hye :
      e = shiftRight ring k y.val)
    (hyx : y.val + 1 = x.val)
    (hpairLeft :
      (ghostStepSelectedPair
        hpsi ring step G e kind).left =
        some z')
    (hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right =
        none)
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e) :
    Lemma4RightmostAt ring k kind
      (ghostStep hpsi ring step G e) y z' := by
  have hright0 := hright
  unfold Lemma4RightmostAt at hright0
  dsimp only at hright0
  unfold Lemma4RightmostAt
  dsimp only
  refine And.intro ?_ (And.intro ?_ ?_)
  · rw [← hye]
    exact
      (ghostTokenAt_ghostStep_initiator
        hpsi ring step G e kind).trans hpairLeft
  · rw [← hye]
    exact hvalid
  · intro q hyq
    let j := shiftRight ring k q.val
    have hje : j ≠ e := by
      intro hj
      have hs :
          shiftRight ring k q.val =
            shiftRight ring k y.val := by
        calc
          shiftRight ring k q.val = j := rfl
          _ = e := hj
          _ = shiftRight ring k y.val := hye
      have hv :=
        selPairShiftRightInjectiveLt
          ring k q.val y.val
          (by omega) (by omega) hs
      omega
    by_cases hjr : j = ring.rightNeighbor e
    · change
        ghostTokenAt kind
          (ghostStep hpsi ring step G e) j = none
      rw [hjr]
      rw [ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e kind hne]
      exact hpairRight
    · have hqx : q.val ≠ x.val := by
        intro hval
        apply hjr
        have hfin : q = x := Fin.ext hval
        dsimp [j]
        rw [hfin]
        exact htrack.symm
      have hxq : x.val < q.val := by
        omega
      have hpreNone :
          ghostTokenAt kind G j = none := by
        exact hright0.2.2 q hxq
      rw [ghostTokenAt_ghostStep_frame
        hpsi ring step G e j kind hje hjr]
      exact hpreNone

/-! -----------------------------------------------------------------------
    The selected-pair classifier
------------------------------------------------------------------------ -/

theorem lemma4RightmostResponderSelectedPairCases_proved :
    Lemma4RightmostResponderSelectedPairCases := by
  unfold Lemma4RightmostResponderSelectedPairCases
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' _hcovered hsound _huniq _hkin
  intro hright htrack
  dsimp only

  have hfit :
      2 * psi <= n :=
    selPairCd_fit
      hpsi ring k kind G.phys hCd
  have hn2 : 2 <= n := by
    omega
  have hne :
      ring.rightNeighbor e ≠ e :=
    selPairRightNeighbor_ne ring hn2 e
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨x, htrack⟩
  have howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z := by
    have hr := hright
    unfold Lemma4RightmostAt at hr
    dsimp only at hr
    rw [htrack]
    exact hr.1
  have htokPre :
      tokenAt kind
          (G.phys (ring.rightNeighbor e)) =
        some z.value :=
    selPairGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hvalidPre :
      ValidToken kind G.phys
        (ring.rightNeighbor e) :=
    selPairOwner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hlocalPre :
      selPairLocalValid kind
        (G.phys (ring.rightNeighbor e))
        z.value := by
    unfold ValidToken at hvalidPre
    rw [htokPre] at hvalidPre
    exact hvalidPre

  let p :=
    selPairSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have htokFrame :=
    selPairSelectedInputTokenFrame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  change
    And
      (tokenAt kind p.1 =
        tokenAt kind (G.phys e))
      (tokenAt kind p.2 =
        tokenAt kind
          (G.phys (ring.rightNeighbor e)))
      at htokFrame
  have htokSelR :
      tokenAt kind p.2 = some z.value :=
    htokFrame.2.trans htokPre
  have hdistSelR :
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist := by
    exact
      selPairSelectedInputDistRight
        hpsi ring k kind step G e hne
        hCd hCd' hwinR
  have hlocalSelR :
      selPairLocalValid kind p.2 z.value := by
    unfold selPairLocalValid at hlocalPre ⊢
    unfold tokenTargetCoordinate at hlocalPre ⊢
    rw [hdistSelR]
    exact hlocalPre

  let c :=
    decodeOffset psi (tokenCode z.value)
  have hcvalid : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode z.value)

  rcases hcvalid with hcneg | hcpos
  · by_cases hcm1 : c = -1
    · have hneg :
          decodeOffset psi (tokenCode z.value) < 0 := by
        dsimp [c] at hcm1 ⊢
        omega
      rcases
          selPairPredecessorData
            hpsi ring k kind G e z
            hCd hsound hwinR howner hneg with
        ⟨x0, y, hxr, hye, hyx0⟩
      have hxx :
          x0.val = x.val := by
        have hs :
            shiftRight ring k x0.val =
              shiftRight ring k x.val :=
          hxr.symm.trans htrack
        exact
          selPairShiftRightInjectiveLt
            ring k x0.val x.val
            (by omega) (by omega) hs
      have hyx :
          y.val + 1 = x.val := by
        omega
      have hwinE :
          Lemma4InWindow ring k psi e :=
        ⟨y, hye⟩
      have hlastPair :=
        selPairGhostStepLastPair
          hpsi ring step G e kind hne
      change
        And
          (((ghostStep hpsi ring step G e).phys e).last =
            p.1.last)
          (((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)).last =
            p.2.last)
          at hlastPair
      have hlastE :
          ((ghostStep hpsi ring step G e).phys e).last =
            false :=
        selPairCd_last_false
          ring k kind
          (ghostStep hpsi ring step G e).phys
          hCd' e hwinE
      have hlastR :
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).last =
            false :=
        selPairCd_last_false
          ring k kind
          (ghostStep hpsi ring step G e).phys
          hCd' (ring.rightNeighbor e) hwinR
      have hgate :
          And (p.1.last = false) (p.2.last = false) :=
        And.intro
          (hlastPair.1.symm.trans hlastE)
          (hlastPair.2.symm.trans hlastR)

      let next :=
        selPairNegTurnNext hpsi p.1.id z.value
      let z' : GhostToken n psi :=
        { value := next
          lmeta := ghostStepLineageAdvance z.lmeta }
      have hc0 :
          decodeOffset psi (tokenCode z.value) = -1 := by
        exact hcm1
      have hcnext :
          decodeOffset psi (tokenCode next) =
            ((psi : Nat) : Int) := by
        dsimp [next]
        exact
          selPairNegTurnNext_offset
            hpsi p.1.id z.value
      have hgeom :=
        selPairTurn_negTurnGeometry
          hpsi ring k kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          e x0 y z.value next
          hCd hCd' hxr hye hyx0
          htokPre hvalidPre hc0 hcnext
      rcases hgeom with
        ⟨hylo, hylt, htargetOld, htargetNew⟩
      have hlocalPost :
          selPairLocalValid kind
            ((ghostStep hpsi ring step G e).phys e)
            next := by
        unfold selPairLocalValid
        left
        refine And.intro ?_
          (And.intro ?_ ?_)
        · rw [hcnext]
          omega
        · rw [htargetNew]
          omega
        · rw [htargetNew]
          omega
      have hdistSelLPre :
          p.1.dist = (G.phys e).dist := by
        exact
          selPairSelectedInputDistLeft
            hpsi ring k kind step G e hne
            hCd hCd' hwinE
      have hdistPostPre :=
        selPairCd_dist_same
          ring k kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          hCd hCd' e hwinE
      have hdistSelLPost :
          p.1.dist =
            ((ghostStep hpsi ring step G e).phys e).dist :=
        hdistSelLPre.trans hdistPostPre.symm
      have hlocalSelL :
          selPairLocalValid kind p.1 next := by
        unfold selPairLocalValid at hlocalPost ⊢
        unfold tokenTargetCoordinate at hlocalPost ⊢
        rw [hdistSelLPost]
        exact hlocalPost
      have hshape :=
        selPairNegTurnShape
          hpsi kind step e p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))
          z howner hgate htokSelR hlocalSelR
          hc0 hlocalSelL
      change
        And
          ((selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).left =
            some z')
          (And
            ((selPairGhostMoveToken
              hpsi kind step e p.1 p.2
              (ghostTokenAt kind G e)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
              none)
            (tokenAt kind
                (moveToken hpsi kind p.1 p.2).1 =
              some z'.value))
          at hshape
      have hmLeft :
          (selPairSelectedPair
            hpsi ring step G e kind).left =
            some z' := by
        change
          (selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).left =
            some z'
        exact hshape.1
      have hmRight :
          (selPairSelectedPair
            hpsi ring step G e kind).right =
            none := by
        change
          (selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).right =
            none
        exact hshape.2.1
      have hpairEq :=
        selPairSelectedPair_eq_export
          hpsi ring step G e kind
      have hpairLeft :
          (ghostStepSelectedPair
            hpsi ring step G e kind).left =
            some z' := by
        rw [← hpairEq]
        exact hmLeft
      have hpairRight :
          (ghostStepSelectedPair
            hpsi ring step G e kind).right =
            none := by
        rw [← hpairEq]
        exact hmRight
      have htokStep :=
        selPairGhostStepTokenPairAt
          hpsi ring step G e kind hne
      change
        And
          (tokenAt kind
            ((ghostStep hpsi ring step G e).phys e) =
              tokenAt kind
                (moveToken hpsi kind p.1 p.2).1)
          (tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
              tokenAt kind
                (moveToken hpsi kind p.1 p.2).2)
          at htokStep
      have htokSelected :
          tokenAt kind (moveToken hpsi kind p.1 p.2).1 =
            some z'.value :=
        hshape.2.2
      have htokPost :
          tokenAt kind
              ((ghostStep hpsi ring step G e).phys e) =
            some z'.value :=
        htokStep.1.trans htokSelected
      have hvalidPost :
          ValidToken kind
            (ghostStep hpsi ring step G e).phys e := by
        unfold ValidToken
        rw [htokPost]
        change
          selPairLocalValid kind
            ((ghostStep hpsi ring step G e).phys e)
            z'.value
        simpa [z'] using hlocalPost
      have hprog :
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              z'.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1 := by
        change
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              next =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1
        exact
          selPairTurn_negTurn_progress
            hpsi kind
            (G.phys (ring.rightNeighbor e))
            ((ghostStep hpsi ring step G e).phys e)
            z.value next y.val
            (by omega) hc0 hcnext
            htargetOld htargetNew
      have hrightPost :=
        selPairRightmostMovedLeft
          hpsi ring k kind step G e x y z z'
          hfit hne hright htrack hye hyx
          hpairLeft hpairRight hvalidPost
      have hmeta :
          z'.lmeta =
            ghostStepLineageAdvance z.lmeta := by
        rfl
      have hid :
          z'.lmeta.id = z.lmeta.id := by
        rw [hmeta]
        simp [ghostStepLineageAdvance]
      have hfresh :
          FreshAt kind k z.lmeta ->
            FreshAt kind k z'.lmeta :=
        selPairFresh_advance kind k z z' hmeta
      have hmono :
          lemma4TokenProgress
              kind
              (G.phys (shiftRight ring k x.val))
              z.value <=
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys
                (shiftRight ring k y.val))
              z'.value := by
        rw [← htrack, ← hye, hprog]
        omega
      have hservice :
          e =
              lemma4ServiceEdge
                ring kind G
                (shiftRight ring k x.val) z ->
            lemma4TokenProgress
                kind
                ((ghostStep hpsi ring step G e).phys
                  (shiftRight ring k y.val))
                z'.value =
              lemma4TokenProgress
                  kind
                  (G.phys (shiftRight ring k x.val))
                  z.value +
                1 := by
        intro _hs
        rw [← htrack, ← hye]
        exact hprog
      refine Or.inr (Or.inl ?_)
      refine And.intro hcm1 ?_
      exact
        ⟨y, z', hrightPost, hid, hfresh,
          hmono, hservice⟩

    · have hc2 : c <= -2 := by
        omega
      have hneg :
          decodeOffset psi (tokenCode z.value) < 0 := by
        dsimp [c] at hc2 ⊢
        omega
      rcases
          selPairPredecessorData
            hpsi ring k kind G e z
            hCd hsound hwinR howner hneg with
        ⟨x0, y, hxr, hye, hyx0⟩
      have hxx :
          x0.val = x.val := by
        have hs :
            shiftRight ring k x0.val =
              shiftRight ring k x.val :=
          hxr.symm.trans htrack
        exact
          selPairShiftRightInjectiveLt
            ring k x0.val x.val
            (by omega) (by omega) hs
      have hyx :
          y.val + 1 = x.val := by
        omega
      have hwinE :
          Lemma4InWindow ring k psi e :=
        ⟨y, hye⟩
      have hlastPair :=
        selPairGhostStepLastPair
          hpsi ring step G e kind hne
      change
        And
          (((ghostStep hpsi ring step G e).phys e).last =
            p.1.last)
          (((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)).last =
            p.2.last)
          at hlastPair
      have hlastE :
          ((ghostStep hpsi ring step G e).phys e).last =
            false :=
        selPairCd_last_false
          ring k kind
          (ghostStep hpsi ring step G e).phys
          hCd' e hwinE
      have hlastR :
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).last =
            false :=
        selPairCd_last_false
          ring k kind
          (ghostStep hpsi ring step G e).phys
          hCd' (ring.rightNeighbor e) hwinR
      have hgate :
          And (p.1.last = false) (p.2.last = false) :=
        And.intro
          (hlastPair.1.symm.trans hlastE)
          (hlastPair.2.symm.trans hlastR)

      have hc2' :
          decodeOffset psi (tokenCode z.value) <= -2 := by
        exact hc2
      let next :=
        selPairNegStepNext hpsi z.value hc2'
      let z' : GhostToken n psi :=
        { value := next
          lmeta := ghostStepLineageAdvance z.lmeta }
      have hcnext :
          decodeOffset psi (tokenCode next) =
            decodeOffset psi (tokenCode z.value) + 1 := by
        dsimp [next]
        exact
          selPairNegStepNext_offset
            hpsi z.value hc2'
      have htarget :=
        selPairNegativeStep_target
          hpsi ring k kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          e x0 y z.value next
          hCd hCd' hxr hye hyx0
          hc2' hcnext
      have hlocalPost :
          selPairLocalValid kind
            ((ghostStep hpsi ring step G e).phys e)
            next := by
        have hlocal := hlocalPre
        unfold selPairLocalValid at hlocal ⊢
        rcases hlocal with hp | hn
        · exfalso
          omega
        · right
          refine And.intro ?_
            (And.intro ?_ ?_)
          · rw [hcnext]
            omega
          · rw [htarget]
            exact hn.2.1
          · rw [htarget]
            exact hn.2.2
      have hdistSelLPre :
          p.1.dist = (G.phys e).dist := by
        exact
          selPairSelectedInputDistLeft
            hpsi ring k kind step G e hne
            hCd hCd' hwinE
      have hdistPostPre :=
        selPairCd_dist_same
          ring k kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          hCd hCd' e hwinE
      have hdistSelLPost :
          p.1.dist =
            ((ghostStep hpsi ring step G e).phys e).dist :=
        hdistSelLPre.trans hdistPostPre.symm
      have hlocalSelL :
          selPairLocalValid kind p.1 next := by
        unfold selPairLocalValid at hlocalPost ⊢
        unfold tokenTargetCoordinate at hlocalPost ⊢
        rw [hdistSelLPost]
        exact hlocalPost
      have hshape :=
        selPairNegStepShape
          hpsi kind step e p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))
          z hc2' howner hgate
          htokSelR hlocalSelR hlocalSelL
      change
        And
          ((selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).left =
            some z')
          (And
            ((selPairGhostMoveToken
              hpsi kind step e p.1 p.2
              (ghostTokenAt kind G e)
              (ghostTokenAt kind G
                (ring.rightNeighbor e))).right =
              none)
            (tokenAt kind
                (moveToken hpsi kind p.1 p.2).1 =
              some z'.value))
          at hshape
      have hmLeft :
          (selPairSelectedPair
            hpsi ring step G e kind).left =
            some z' := by
        change
          (selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).left =
            some z'
        exact hshape.1
      have hmRight :
          (selPairSelectedPair
            hpsi ring step G e kind).right =
            none := by
        change
          (selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).right =
            none
        exact hshape.2.1
      have hpairEq :=
        selPairSelectedPair_eq_export
          hpsi ring step G e kind
      have hpairLeft :
          (ghostStepSelectedPair
            hpsi ring step G e kind).left =
            some z' := by
        rw [← hpairEq]
        exact hmLeft
      have hpairRight :
          (ghostStepSelectedPair
            hpsi ring step G e kind).right =
            none := by
        rw [← hpairEq]
        exact hmRight
      have htokStep :=
        selPairGhostStepTokenPairAt
          hpsi ring step G e kind hne
      change
        And
          (tokenAt kind
            ((ghostStep hpsi ring step G e).phys e) =
              tokenAt kind
                (moveToken hpsi kind p.1 p.2).1)
          (tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
              tokenAt kind
                (moveToken hpsi kind p.1 p.2).2)
          at htokStep
      have htokSelected :
          tokenAt kind (moveToken hpsi kind p.1 p.2).1 =
            some z'.value :=
        hshape.2.2
      have htokPost :
          tokenAt kind
              ((ghostStep hpsi ring step G e).phys e) =
            some z'.value :=
        htokStep.1.trans htokSelected
      have hvalidPost :
          ValidToken kind
            (ghostStep hpsi ring step G e).phys e := by
        unfold ValidToken
        rw [htokPost]
        change
          selPairLocalValid kind
            ((ghostStep hpsi ring step G e).phys e)
            z'.value
        simpa [z'] using hlocalPost
      have hprog :
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              z'.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1 := by
        change
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              next =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1
        exact
          selPairNegativeStep_progress
            kind
            (G.phys (ring.rightNeighbor e))
            ((ghostStep hpsi ring step G e).phys e)
            z.value next hc2' hcnext htarget
      have hrightPost :=
        selPairRightmostMovedLeft
          hpsi ring k kind step G e x y z z'
          hfit hne hright htrack hye hyx
          hpairLeft hpairRight hvalidPost
      have hmeta :
          z'.lmeta =
            ghostStepLineageAdvance z.lmeta := by
        rfl
      have hid :
          z'.lmeta.id = z.lmeta.id := by
        rw [hmeta]
        simp [ghostStepLineageAdvance]
      have hfresh :
          FreshAt kind k z.lmeta ->
            FreshAt kind k z'.lmeta :=
        selPairFresh_advance kind k z z' hmeta
      have hmono :
          lemma4TokenProgress
              kind
              (G.phys (shiftRight ring k x.val))
              z.value <=
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys
                (shiftRight ring k y.val))
              z'.value := by
        rw [← htrack, ← hye, hprog]
        omega
      have hservice :
          e =
              lemma4ServiceEdge
                ring kind G
                (shiftRight ring k x.val) z ->
            lemma4TokenProgress
                kind
                ((ghostStep hpsi ring step G e).phys
                  (shiftRight ring k y.val))
                z'.value =
              lemma4TokenProgress
                  kind
                  (G.phys (shiftRight ring k x.val))
                  z.value +
                1 := by
        intro _hs
        rw [← htrack, ← hye]
        exact hprog
      refine Or.inr (Or.inr ?_)
      refine And.intro hc2 ?_
      exact
        ⟨y, z', hrightPost, hid, hfresh,
          hmono, hservice⟩

  · have hpos :
        0 < c := by
      omega
    have hpos0 :
        0 <
          decodeOffset psi (tokenCode z.value) := by
      exact hpos
    have hshape :=
      selPairPositiveShape
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G
          (ring.rightNeighbor e))
        z howner htokSelR hlocalSelR hpos0
    have hmRight :
        (selPairSelectedPair
          hpsi ring step G e kind).right =
          some z := by
      change
        (selPairGhostMoveToken
          hpsi kind step e p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).right =
          some z
      exact hshape.1
    have hpairEq :=
      selPairSelectedPair_eq_export
        hpsi ring step G e kind
    have hpairRight :
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z := by
      rw [← hpairEq]
      exact hmRight
    have hleftNone :
        ghostTokenAt kind G e = none ->
          (ghostStepSelectedPair
            hpsi ring step G e kind).left =
            none := by
      intro hnone
      have hm := hshape.2.2 hnone
      have hmLeft :
          (selPairSelectedPair
            hpsi ring step G e kind).left =
            none := by
        change
          (selPairGhostMoveToken
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G
              (ring.rightNeighbor e))).left =
            none
        exact hm
      rw [← hpairEq]
      exact hmLeft
    have htokStep :=
      selPairGhostStepTokenPairAt
        hpsi ring step G e kind hne
    change
      And
        (tokenAt kind
          ((ghostStep hpsi ring step G e).phys e) =
            tokenAt kind
              (moveToken hpsi kind p.1 p.2).1)
        (tokenAt kind
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)) =
            tokenAt kind
              (moveToken hpsi kind p.1 p.2).2)
        at htokStep
    have htokSelected :
        tokenAt kind (moveToken hpsi kind p.1 p.2).2 =
          some z.value :=
      hshape.2.1
    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
          some z.value :=
      htokStep.2.trans htokSelected
    have hdist :
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          (G.phys (ring.rightNeighbor e)).dist :=
      selPairCd_dist_same
        ring k kind
        G.phys
        (ghostStep hpsi ring step G e).phys
        hCd hCd'
        (ring.rightNeighbor e) hwinR
    have hvalidPost :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) :=
      selPairValid_same_dist
        kind
        G.phys
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        z.value htokPre htokPost hdist hvalidPre
    have hprogEq :
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z.value =
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value :=
      selPairProgress_dist_eq
        kind
        (G.phys (ring.rightNeighbor e))
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value hdist
    have hrightPost :=
      selPairRightmostPositive
        hpsi ring k kind step G e x z
        hfit hne hright htrack
        hpairRight hleftNone hvalidPost
    have hmono :
        lemma4TokenProgress
            kind
            (G.phys (shiftRight ring k x.val))
            z.value <=
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys
              (shiftRight ring k x.val))
            z.value := by
      rw [← htrack]
      exact Nat.le_of_eq hprogEq.symm
    have hservice :
        e =
            lemma4ServiceEdge
              ring kind G
              (shiftRight ring k x.val) z ->
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys
                (shiftRight ring k x.val))
              z.value =
            lemma4TokenProgress
                kind
                (G.phys (shiftRight ring k x.val))
                z.value +
              1 := by
      intro hs
      have hfalse : False := by
        unfold lemma4ServiceEdge at hs
        rw [if_pos hpos0] at hs
        have her :
            e = ring.rightNeighbor e :=
          hs.trans htrack.symm
        exact hne her.symm
      exact False.elim hfalse
    exact
      Or.inl
        (And.intro hpos
          (And.intro hrightPost
            (And.intro hmono hservice)))

end PPL

#print axioms PPL.lemma4RightmostResponderSelectedPairCases_proved
