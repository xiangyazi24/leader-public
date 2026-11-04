import Leader.PPL.TokenCompletion.RightmostInitiatorSurvivalLocal
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
Leaves: the three offset-local rows of the rightmost-initiator
survival residual, proved directly.

Proof shape.  Rightmostness empties the responder ghost slot; coverage plus
pre/post C_d (same dist through the selected input) forbids a live
selected-colour physical responder.  The tracked initiator is live in the
selected input (token frame plus same dist), so the birth guard is off and no
collision happens.  The selected ghost pair is then computed literally:
c = 1 and c >= 2 bump the tracked lineage to the responder, c < 0 keeps it on
the initiator.  No ID uniqueness or history premise is used.

Helpers below are mirrored (renamed) from
TokenCorrectnessLemma4RightmostResponderSelectedPair.lean,
TokenCorrectnessLemma4SweepInitiatorArrival.lean and
TokenCorrectnessLemma4SweepInitiatorRows.lean, whose helpers are private.
-/

private def risvBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)
private def risvMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)
private def risvLocalValid
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
private instance instDecidableRisvLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (risvLocalValid kind q t) := by
  unfold risvLocalValid
  infer_instance
private def risvSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }
private def risvClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if risvLocalValid kind q t then
        q
      else
        risvSetToken kind q none
private def risvLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }
private theorem risvSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      risvSetToken kind q t := by
  cases kind <;> rfl
private theorem risvSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      risvClearInvalid kind q := by
  cases kind <;> rfl
private theorem risvSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = risvLeaderBirth q := by
  rfl
private def risvNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    risvMkToken
      (offsetPsiCode psi hpsi)
      (risvBitToFin (!sourceBit))
      (risvBitToFin sourceBit)
  else
    risvMkToken
      (offsetPsiCode psi hpsi)
      (risvBitToFin sourceBit)
      (0 : Fin 2)
private def risvLiveShadow
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
              risvLocalValid kind q t then
            some z
          else
            none
private def risvLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if risvLocalValid kind q t then
        some t
      else
        none
private def risvBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      risvMkToken
        (offsetPsiCode psi hpsi)
        (risvBitToFin (!idBit))
        (risvBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }
private def risvBumpTo
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
        if risvLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩
private def risvGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := risvLiveValue kind l
  let rv0 := risvLiveValue kind r
  let gl0 := risvLiveShadow kind l gl
  let gr0 := risvLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (risvBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (risvBirthGhost
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
            risvMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            risvBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            risvMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            risvBumpTo kind r next gl2
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
                  risvNegTurnNext
                    hpsi l.id t
                let b :=
                  risvBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c ≤ -2 then
                have hbranch : c ≤ -2 := hm2
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  risvMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  risvBumpTo
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
                risvNegTurnNext
                  hpsi l.id t
              let b :=
                risvBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                risvMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                risvBumpTo
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
private def risvMoveToken
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
            (risvMkToken
              (offsetPsiCode psi hpsi)
              (risvBitToFin (!l.id))
              (risvBitToFin l.id)))
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
                risvNegTurnNext hpsi l.id t
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                risvMkToken
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
                (risvMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2)))
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            risvMkToken
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
private theorem risvMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    risvMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl
private def risvPrelude
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
private def risvSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := risvPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2
private def risvSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    risvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  risvGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))
private theorem risvSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    risvSelectedPair
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
private theorem risvLiveValue_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (htok : tokenAt kind q = some t)
    (hvalid : risvLocalValid kind q t) :
    risvLiveValue kind q = some t := by
  unfold risvLiveValue
  rw [htok]
  simp only [if_pos hvalid]

private theorem risvLiveShadow_some
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hg : g = some z)
    (htok : tokenAt kind q = some z.value)
    (hvalid : risvLocalValid kind q z.value) :
    risvLiveShadow kind q g = some z := by
  rw [hg]
  unfold risvLiveShadow
  rw [htok]
  simp only [true_and, if_pos hvalid]

private theorem risvSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q v) = v := by
  rw [risvSourceSet_eq]
  unfold risvSetToken
  cases kind <;> rfl

private theorem risvSourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi)) :
    (sourceSet kind q v).id = q.id := by
  rw [risvSourceSet_eq]
  unfold risvSetToken
  cases kind <;> rfl

private theorem risvSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      risvLiveValue kind q := by
  rw [risvSourceClear_eq]
  unfold risvClearInvalid risvLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : risvLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold risvSetToken
        cases kind <;> rfl

private theorem risvSourceClear_last
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).last = q.last := by
  rw [risvSourceClear_eq]
  unfold risvClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : risvLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold risvSetToken
        cases kind <;> rfl

private theorem risvSourceClear_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).id = q.id := by
  rw [risvSourceClear_eq]
  unfold risvClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : risvLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold risvSetToken
        cases kind <;> rfl

/-! -----------------------------------------------------------------------
    Physical selected-token and last-field projections
------------------------------------------------------------------------ -/
private theorem risvElimTokenLeft
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
private theorem risvElimTokenRight
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
private theorem risvWhitePreservesBlack
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
private theorem risvPplTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := risvSelectedInput hpsi kind l r
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).2 := by
  cases kind with
  | black =>
      let p := risvPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw :=
        risvWhitePreservesBlack
          hpsi b.1 b.2
      have hel :=
        risvElimTokenLeft .black w.1 w.2
      have her :=
        risvElimTokenRight .black w.1 w.2
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
      let p := risvPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hel :=
        risvElimTokenLeft .white w.1 w.2
      have her :=
        risvElimTokenRight .white w.1 w.2
      change
        tokenAt .white
            (eliminateLeaders w.1 w.2).1 =
              tokenAt .white w.1 ∧
          tokenAt .white
            (eliminateLeaders w.1 w.2).2 =
              tokenAt .white w.2
      exact ⟨hel, her⟩
private theorem risvMoveTokenLast
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
private theorem risvElimLast
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
private theorem risvPplLastPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := risvSelectedInput hpsi kind l r
    (ppl hpsi l r).1.last = p.1.last ∧
      (ppl hpsi l r).2.last = p.2.last := by
  cases kind with
  | black =>
      let p := risvPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hb := risvMoveTokenLast hpsi .black p.1 p.2
      have hw := risvMoveTokenLast hpsi .white b.1 b.2
      have he := risvElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            p.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            p.2.last
      exact
        ⟨he.1.trans (hw.1.trans hb.1),
          he.2.trans (hw.2.trans hb.2)⟩
  | white =>
      let p := risvPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw := risvMoveTokenLast hpsi .white b.1 b.2
      have he := risvElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            b.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            b.2.last
      exact
        ⟨he.1.trans hw.1,
          he.2.trans hw.2⟩
private theorem risvGhostStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      risvSelectedInput hpsi kind
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
    risvPplTokenPair
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
private theorem risvGhostStepTokenPairAt
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      risvSelectedInput hpsi kind
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
    risvGhostStepTokenPair
      hpsi ring G e kind hne
private theorem risvGhostStepLastPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      risvSelectedInput hpsi kind
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
    risvPplLastPair
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
private theorem risvCd_fit
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
private theorem risvRightNeighbor_ne
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
private theorem risvLeftNeighborRightNeighbor
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
private theorem risvRightNeighborShiftRight
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
private theorem risvGhostSound_token
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
private theorem risvOwner_valid
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
private theorem risvFirstNegativeTarget
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
private theorem risvNegative_not_first
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
    risvGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hvalid :=
    risvOwner_valid
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
      risvFirstNegativeTarget
        hpsi kind
        (G.phys (ring.rightNeighbor e))
        z.value hdist hneg
    omega
private theorem risvPredecessorData
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
    risvNegative_not_first
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
        risvRightNeighborShiftRight
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
  rw [risvLeftNeighborRightNeighbor,
    risvLeftNeighborRightNeighbor] at he
  exact
    ⟨x, y, hx, he,
      by dsimp [y]; omega⟩
private theorem risvCd_last_false
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
private theorem risvCd_dist_same
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
private theorem risvProgress_dist_eq
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
private theorem risvValid_same_dist
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
private theorem risvFresh_advance
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
private theorem risvNegativeAbs
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
private theorem risvNegativeStep_target
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
private theorem risvNegativeStep_valid
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
private theorem risvNegativeStep_progress
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
    risvNegativeAbs
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
private theorem risvServiceEdge_negative
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
    (risvLeftNeighborRightNeighbor
      ring e).symm

private theorem risvTurn_negTurnGeometry
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

private theorem risvTurn_negTurn_valid
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
private theorem risvTurn_negTurn_progress
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

private theorem risvBlackPreservesWhite
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

private theorem risvPreludeTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := risvPrelude hpsi l r
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
        rw [risvSourceBirth_eq]
        cases kind <;>
          simpa only [risvLeaderBirth, tokenAt]
            using hd.2
      · simp only
          [createLeaderThroughLine6, if_neg hguard]
        exact hd.2
  dsimp only at hs
  have hp :
      tokenAt kind (risvPrelude hpsi l r).1 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).left ∧
        tokenAt kind (risvPrelude hpsi l r).2 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).right := by
    cases kind with
    | black =>
        simp only [risvPrelude, tokenAt]
        repeat' (first
          | split <;> try dsimp only
          | rfl)
        all_goals exact And.intro rfl rfl
    | white =>
        simp only [risvPrelude, tokenAt]
        repeat' (first
          | split <;> try dsimp only
          | rfl)
        all_goals exact And.intro rfl rfl
  exact
    And.intro
      (hp.1.trans hs.1)
      (hp.2.trans hs.2)

private theorem risvSelectedInputTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := risvSelectedInput hpsi kind l r
    And
      (tokenAt kind p.1 = tokenAt kind l)
      (tokenAt kind p.2 = tokenAt kind r) := by
  cases kind with
  | black =>
      exact
        risvPreludeTokenFrame
          hpsi .black l r
  | white =>
      let p := risvPrelude hpsi l r
      have hp :=
        risvPreludeTokenFrame
          hpsi .white l r
      have hb :=
        risvBlackPreservesWhite
          hpsi p.1 p.2
      dsimp only [risvSelectedInput]
      exact
        And.intro
          (hb.1.trans hp.1)
          (hb.2.trans hp.2)

private theorem risvMoveTokenDist
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

private theorem risvElimDist
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

private theorem risvPplDistPair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := risvSelectedInput hpsi kind l r
    And
      ((ppl hpsi l r).1.dist = p.1.dist)
      ((ppl hpsi l r).2.dist = p.2.dist) := by
  cases kind with
  | black =>
      let p := risvPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hb := risvMoveTokenDist hpsi .black p.1 p.2
      have hw := risvMoveTokenDist hpsi .white b.1 b.2
      have he := risvElimDist w.1 w.2
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
      let p := risvPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw := risvMoveTokenDist hpsi .white b.1 b.2
      have he := risvElimDist w.1 w.2
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

private theorem risvGhostStepDistPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      risvSelectedInput hpsi kind
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
    risvPplDistPair
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

private theorem risvSelectedInputDistLeft
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
    (risvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).1.dist =
      (G.phys e).dist := by
  have hp :=
    risvGhostStepDistPair
      hpsi ring step G e kind hne
  have hc :=
    risvCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' e hwin
  exact hp.1.symm.trans hc

private theorem risvSelectedInputDistRight
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
    (risvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))).2.dist =
      (G.phys (ring.rightNeighbor e)).dist := by
  have hp :=
    risvGhostStepDistPair
      hpsi ring step G e kind hne
  have hc :=
    risvCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd'
      (ring.rightNeighbor e) hwin
  exact hp.2.symm.trans hc

private theorem risvShiftRightInjectiveLt
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

private def risvNegStepNext
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
  risvMkToken
    (encodeOffset psi (c + 1) (by
      rcases hv with hn | hp
      · left
        omega
      · exfalso
        omega))
    t.1.2 t.2

private theorem risvNegStepNext_offset
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) <= -2) :
    decodeOffset psi
        (tokenCode
          (risvNegStepNext hpsi t hc)) =
      decodeOffset psi (tokenCode t) + 1 := by
  dsimp [risvNegStepNext, risvMkToken, tokenCode]
  exact decode_encode _ _ _

private theorem risvNegTurnNext_offset
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (risvNegTurnNext hpsi sourceBit t)) =
      ((psi : Nat) : Int) := by
  unfold risvNegTurnNext
  by_cases hcarry : t.2 = (1 : Fin 2)
  · rw [if_pos hcarry]
    dsimp [risvMkToken, tokenCode]
    exact decodeOffset_psi psi hpsi
  · rw [if_neg hcarry]
    dsimp [risvMkToken, tokenCode]
    exact decodeOffset_psi psi hpsi

private def risvGhostFinish
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
          risvMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          risvBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hbranch : 2 ≤ c := h2
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          risvMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          risvBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if cr = -1 then
              let next :=
                risvNegTurnNext hpsi l.id tr
              let b :=
                risvBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hbranch : cr ≤ -2 := hm2
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                risvMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                risvBumpTo kind l next gr0
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
              risvNegTurnNext hpsi l.id tr
            let b :=
              risvBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hbranch : cr ≤ -2 := hm2
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              risvMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b :=
              risvBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private theorem risvMoveToken_positive
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (htok : tokenAt kind r = some t)
    (hvalid : risvLocalValid kind r t)
    (hc : 0 < decodeOffset psi (tokenCode t)) :
    tokenAt kind (moveToken hpsi kind l r).2 =
      some t := by
  have hrv :
      risvLiveValue kind r = some t :=
    risvLiveValue_some kind r t htok hvalid
  have hm1 :
      decodeOffset psi (tokenCode t) ≠ -1 := by
    omega
  have hm2 :
      ¬ decodeOffset psi (tokenCode t) ≤ -2 := by
    omega
  rw [← risvMoveToken_eq hpsi kind l r]
  by_cases hgate : l.last = false ∧ r.last = false
  · cases hlv : risvLiveValue kind l with
    | none =>
        by_cases hd :
            (sourceClear kind l).dist.val =
              tokenD' psi kind
        · unfold risvMoveToken
          simp
            [risvSourceClear_token,
              risvSourceClear_last,
              risvSourceSet_token,
              hgate, hlv, hrv, hd, hm1, hm2]
        · unfold risvMoveToken
          simp
            [risvSourceClear_token,
              risvSourceClear_last,
              risvSourceSet_token,
              hgate, hlv, hrv, hd, hm1, hm2]
    | some u =>
        unfold risvMoveToken
        simp
          [risvSourceClear_token,
            risvSourceClear_last,
            risvSourceSet_token,
            hgate, hlv, hrv, hm1, hm2]
  · unfold risvMoveToken
    simp
      [risvSourceClear_token,
        risvSourceClear_last,
        hgate, hrv]

private theorem risvMoveToken_negTurn
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind r = some t)
    (hvalid : risvLocalValid kind r t)
    (hc : decodeOffset psi (tokenCode t) = -1) :
    tokenAt kind (moveToken hpsi kind l r).1 =
      some (risvNegTurnNext hpsi l.id t) := by
  have hrv :
      risvLiveValue kind r = some t :=
    risvLiveValue_some kind r t htok hvalid
  rw [← risvMoveToken_eq hpsi kind l r]
  cases hlv : risvLiveValue kind l with
  | none =>
      by_cases hd :
          (sourceClear kind l).dist.val =
            tokenD' psi kind
      · unfold risvMoveToken
        simp
          [risvSourceClear_token,
            risvSourceClear_last,
            risvSourceClear_id,
            risvSourceSet_token,
            risvSourceSet_id,
            hgate, hlv, hrv, hd, hc]
      · unfold risvMoveToken
        simp
          [risvSourceClear_token,
            risvSourceClear_last,
            risvSourceClear_id,
            risvSourceSet_token,
            risvSourceSet_id,
            hgate, hlv, hrv, hd, hc]
  | some u =>
      unfold risvMoveToken
      simp
        [risvSourceClear_token,
          risvSourceClear_last,
          risvSourceClear_id,
          risvSourceSet_token,
          risvSourceSet_id,
          hgate, hlv, hrv, hc]

private theorem risvMoveToken_negStep
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hc : decodeOffset psi (tokenCode t) ≤ -2)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind r = some t)
    (hvalid : risvLocalValid kind r t) :
    tokenAt kind (moveToken hpsi kind l r).1 =
      some (risvNegStepNext hpsi t hc) := by
  have hrv :
      risvLiveValue kind r = some t :=
    risvLiveValue_some kind r t htok hvalid
  have hm1 :
      decodeOffset psi (tokenCode t) ≠ -1 := by
    omega
  rw [← risvMoveToken_eq hpsi kind l r]
  cases hlv : risvLiveValue kind l with
  | none =>
      by_cases hd :
          (sourceClear kind l).dist.val =
            tokenD' psi kind
      · unfold risvMoveToken
        simp
          [risvSourceClear_token,
            risvSourceClear_last,
            risvSourceSet_token,
            hgate, hlv, hrv, hd, hm1, hc,
            risvNegStepNext]
      · unfold risvMoveToken
        simp
          [risvSourceClear_token,
            risvSourceClear_last,
            risvSourceSet_token,
            hgate, hlv, hrv, hd, hm1, hc,
            risvNegStepNext]
  | some u =>
      unfold risvMoveToken
      simp
        [risvSourceClear_token,
          risvSourceClear_last,
          risvSourceSet_token,
          hgate, hlv, hrv, hm1, hc,
          risvNegStepNext]

private theorem risvPositiveShape
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
    (hvalid : risvLocalValid kind r z.value)
    (hc : 0 < decodeOffset psi (tokenCode z.value)) :
    (risvGhostMoveToken
        hpsi kind step site l r gl gr).right =
          some z ∧
      tokenAt kind (moveToken hpsi kind l r).2 =
          some z.value ∧
      (gl = none →
        (risvGhostMoveToken
          hpsi kind step site l r gl gr).left =
            none) := by
  classical
  have hphys :
      tokenAt kind (moveToken hpsi kind l r).2 =
        some z.value :=
    risvMoveToken_positive
      hpsi kind l r z.value htok hvalid hc
  have hm1 :
      decodeOffset psi (tokenCode z.value) ≠ -1 := by
    omega
  have hm2 :
      ¬ decodeOffset psi (tokenCode z.value) ≤ -2 := by
    omega
  by_cases hgate : l.last = false ∧ r.last = false
  · let lv0 := risvLiveValue kind l
    let rv0 := risvLiveValue kind r
    let gl0 := risvLiveShadow kind l gl
    let gr0 := risvLiveShadow kind r gr
    let guard :=
      l.dist.val = tokenD' psi kind ∧ lv0 = none
    let birth :=
      risvBirthGhost hpsi kind step site l.id
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
        risvLiveValue_some
          kind r z.value htok hvalid
    have hgr0 : gr0 = some z := by
      dsimp only [gr0]
      exact
        risvLiveShadow_some
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
        risvGhostMoveToken
            hpsi kind step site l r gl gr =
          risvGhostFinish
            hpsi kind l r lv2 rv0 gl2 gr0 := by
      unfold risvGhostMoveToken
      simp only [if_pos hgate]
      rfl
    have hright :
        (risvGhostMoveToken
          hpsi kind step site l r gl gr).right =
            some z := by
      rw [hMoveEq, hlv2, hrv0, hgr0]
      unfold risvGhostFinish
      simp only [if_neg hm1, dif_neg hm2]
    have hleft :
        gl = none →
          (risvGhostMoveToken
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
      unfold risvGhostFinish
      simp only [if_neg hm1, dif_neg hm2]
    exact ⟨hright, hphys, hleft⟩
  · have hgr0 :
        risvLiveShadow kind r gr = some z :=
      risvLiveShadow_some
        kind r gr z hgr htok hvalid
    have hright :
        (risvGhostMoveToken
          hpsi kind step site l r gl gr).right =
            some z := by
      unfold risvGhostMoveToken
      simp only [if_neg hgate]
      exact hgr0
    have hleft :
        gl = none →
          (risvGhostMoveToken
            hpsi kind step site l r gl gr).left =
              none := by
      intro hgl
      unfold risvGhostMoveToken
      simp only [if_neg hgate]
      rw [hgl]
      rfl
    exact ⟨hright, hphys, hleft⟩

private theorem risvNegTurnShape
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
    (hvalid : risvLocalValid kind r z.value)
    (hc : decodeOffset psi (tokenCode z.value) = -1)
    (hnext :
      risvLocalValid kind l
        (risvNegTurnNext hpsi l.id z.value)) :
    (risvGhostMoveToken
        hpsi kind step site l r gl gr).left =
          some
            { value := risvNegTurnNext hpsi l.id z.value
              lmeta := ghostStepLineageAdvance z.lmeta } ∧
      (risvGhostMoveToken
        hpsi kind step site l r gl gr).right =
          none ∧
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (risvNegTurnNext hpsi l.id z.value) := by
  classical
  let lv0 := risvLiveValue kind l
  let rv0 := risvLiveValue kind r
  let gl0 := risvLiveShadow kind l gl
  let gr0 := risvLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    risvBirthGhost hpsi kind step site l.id
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
      risvLiveValue_some
        kind r z.value htok hvalid
  have hgr0 : gr0 = some z := by
    dsimp only [gr0]
    exact
      risvLiveShadow_some
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
      risvGhostMoveToken
          hpsi kind step site l r gl gr =
        risvGhostFinish
          hpsi kind l r lv2 rv0 gl2 gr0 := by
    unfold risvGhostMoveToken
    simp only [if_pos hgate]
    rfl
  have hghost :
      (risvGhostMoveToken
          hpsi kind step site l r gl gr).left =
            some
              { value := risvNegTurnNext hpsi l.id z.value
                lmeta := ghostStepLineageAdvance z.lmeta } ∧
        (risvGhostMoveToken
          hpsi kind step site l r gl gr).right =
            none := by
    rw [hMoveEq, hlv2, hrv0, hgr0]
    unfold risvGhostFinish
    simp only
      [if_pos hc, risvBumpTo, if_pos hnext, and_self]
  have hphys :
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (risvNegTurnNext hpsi l.id z.value) :=
    risvMoveToken_negTurn
      hpsi kind l r z.value
      hgate htok hvalid hc
  exact ⟨hghost.1, hghost.2, hphys⟩

private theorem risvNegStepShape
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
    (hvalid : risvLocalValid kind r z.value)
    (hnext :
      risvLocalValid kind l
        (risvNegStepNext hpsi z.value hc)) :
    (risvGhostMoveToken
        hpsi kind step site l r gl gr).left =
          some
            { value := risvNegStepNext hpsi z.value hc
              lmeta := ghostStepLineageAdvance z.lmeta } ∧
      (risvGhostMoveToken
        hpsi kind step site l r gl gr).right =
          none ∧
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (risvNegStepNext hpsi z.value hc) := by
  classical
  have hm1 :
      decodeOffset psi (tokenCode z.value) ≠ -1 := by
    omega
  let lv0 := risvLiveValue kind l
  let rv0 := risvLiveValue kind r
  let gl0 := risvLiveShadow kind l gl
  let gr0 := risvLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    risvBirthGhost hpsi kind step site l.id
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
      risvLiveValue_some
        kind r z.value htok hvalid
  have hgr0 : gr0 = some z := by
    dsimp only [gr0]
    exact
      risvLiveShadow_some
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
      risvGhostMoveToken
          hpsi kind step site l r gl gr =
        risvGhostFinish
          hpsi kind l r lv2 rv0 gl2 gr0 := by
    unfold risvGhostMoveToken
    simp only [if_pos hgate]
    rfl
  have hghost :
      (risvGhostMoveToken
          hpsi kind step site l r gl gr).left =
            some
              { value := risvNegStepNext hpsi z.value hc
                lmeta := ghostStepLineageAdvance z.lmeta } ∧
        (risvGhostMoveToken
          hpsi kind step site l r gl gr).right =
            none := by
    have hnext' := hnext
    unfold risvNegStepNext at hnext'
    rw [hMoveEq, hlv2, hrv0, hgr0]
    unfold risvGhostFinish
    simp only
      [if_neg hm1, dif_pos hc,
        risvBumpTo, if_pos hnext,
        risvNegStepNext, if_pos hnext', and_self]
  have hphys :
      tokenAt kind (moveToken hpsi kind l r).1 =
        some (risvNegStepNext hpsi z.value hc) :=
    risvMoveToken_negStep
      hpsi kind l r z.value hc
      hgate htok hvalid
  exact ⟨hghost.1, hghost.2, hphys⟩

private theorem risvRightmostPositive
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
          risvShiftRightInjectiveLt
            ring k y.val x.val
            (by omega) (by omega) hs
        omega
      rw [ghostTokenAt_ghostStep_frame
        hpsi ring step G e j kind hje hjr]
      exact hpreNone

private theorem risvRightmostMovedLeft
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
        risvShiftRightInjectiveLt
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


/-! ## Mirrored arrival arithmetic -/

private theorem risvALastDistPlusD
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

private theorem risvALastPositiveTargetBelow
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
    risvALastDistPlusD
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

private theorem risvAPositiveNotLast
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
      risvLocalValid kind q t)
    (hpos :
      0 < decodeOffset psi (tokenCode t)) :
    False := by
  have ht :=
    risvALastPositiveTargetBelow
      hpsi kind q t hdist hpos
  unfold risvLocalValid at hlocal
  dsimp only at hlocal
  rcases hlocal with hp | hn <;> omega

private def risvABounceNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) : TokenData psi :=
  risvMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2


private theorem risvAOldTarget
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

private theorem risvABounceTarget
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

private theorem risvAStage_eq
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

private theorem risvAProgress_eq
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

/-! ## Mirrored right-move arithmetic -/

private theorem risvRCanonicalSucc
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (x d a b : Nat)
    (ha :
      a = (x + d) % (2 * psi))
    (hb :
      b = (x + 1 + d) % (2 * psi)) :
    b = (a + 1) % (2 * psi) := by
  rw [ha, hb]
  have hone :
      1 % (2 * psi) = 1 :=
    Nat.mod_eq_of_lt (by omega)
  calc
    (x + 1 + d) % (2 * psi) =
        (x + d + 1) % (2 * psi) := by
          congr 1
          omega
    _ =
        (((x + d) % (2 * psi)) +
          (1 % (2 * psi))) %
            (2 * psi) := by
          rw [Nat.add_mod]
    _ =
        (((x + d) % (2 * psi)) + 1) %
            (2 * psi) := by
          rw [hone]

private theorem risvRRightMoveTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hdist :
      q'.dist.val =
        (q.dist.val + 1) % (2 * psi))
    (hc :
      2 ≤ decodeOffset psi (tokenCode t))
    (hnew :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) - 1) :
    tokenTargetCoordinate kind q' t' =
      tokenTargetCoordinate kind q t := by
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  cases hco :
      decodeOffset psi (tokenCode t) with
  | negSucc m =>
      rw [hco] at hc
      omega
  | ofNat m =>
      rw [hco] at hc hnew hv
      simp only [Int.ofNat_eq_natCast] at hc hnew hv
      have hm :
          2 ≤ m ∧ m ≤ psi := by
        rcases hv with hn | hp <;> omega
      have hm1 : 1 ≤ m := by
        omega
      have hcast :
          (((m - 1 : Nat)) : Int) =
            ((m : Int) - 1) := by
        omega
      have hnew' :
          decodeOffset psi (tokenCode t') =
            (((m - 1 : Nat)) : Int) := by
        exact hnew.trans hcast.symm
      unfold tokenTargetCoordinate
      rw [hco, hnew', hdist]
      simp only [Int.ofNat_eq_natCast]
      have hq : q.dist.val < 2 * psi :=
        q.dist.isLt
      by_cases hnowrap :
          q.dist.val + 1 < 2 * psi
      · rw [Nat.mod_eq_of_lt hnowrap]
        congr 1
        omega
      · have hwrap :
            q.dist.val + 1 = 2 * psi := by
          omega
        have hqeq :
            q.dist.val = 2 * psi - 1 := by
          omega
        rw [hwrap, Nat.mod_self, hqeq]
        cases kind with
        | black =>
            simp only [tokenD']
            have hsmall :
                m - 1 < 2 * psi := by
              omega
            have hsum :
                (((2 * psi - 1 : Nat)) : Int) +
                    ((m : Nat) : Int) =
                  (((m - 1 : Nat)) : Int) +
                    (((2 * psi : Nat)) : Int) := by
              omega
            simp only
              [Int.natCast_zero, Int.zero_add,
                Int.add_zero]
            rw [hsum, Int.add_emod_right]
        | white =>
            simp only [tokenD']
            have hsmall :
                m - 1 + psi < 2 * psi := by
              omega
            have hsum :
                (((2 * psi - 1 : Nat)) : Int) +
                    ((m : Nat) : Int) +
                    ((psi : Nat) : Int) =
                  (((m - 1 + psi : Nat)) : Int) +
                    (((2 * psi : Nat)) : Int) := by
              omega
            have hleft :
                (((m - 1 : Nat) : Int) +
                    ((psi : Nat) : Int)) =
                  (((m - 1 + psi : Nat)) : Int) := by
              omega
            simp only
              [Int.natCast_zero, Int.zero_add,
                Int.add_zero]
            rw [hleft, hsum, Int.add_emod_right]

private theorem risvRRightMoveProgress
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (hc :
      2 ≤ decodeOffset psi (tokenCode t))
    (hnew :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) - 1)
    (htarget :
      tokenTargetCoordinate kind q' t' =
        tokenTargetCoordinate kind q t) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  have holdPos :
      0 < decodeOffset psi (tokenCode t) := by
    omega
  have hnewPos :
      0 < decodeOffset psi (tokenCode t') := by
    omega
  have hstage :
      lemma4TokenStage kind q' t' =
        lemma4TokenStage kind q t := by
    unfold lemma4TokenStage
    dsimp only
    rw [if_pos hnewPos, if_pos holdPos, htarget]
  unfold lemma4TokenProgress
  dsimp only
  rw [if_pos hnewPos, if_pos holdPos, hstage]
  have hv :
      ValidOffset psi
        (decodeOffset psi (tokenCode t)) :=
    decodeOffset_valid
      psi (by have := (tokenCode t).isLt; omega) (tokenCode t)
  cases hco :
      decodeOffset psi (tokenCode t) with
  | negSucc m =>
      rw [hco] at hc
      omega
  | ofNat m =>
      rw [hco] at hc hnew hv
      simp only [Int.ofNat_eq_natCast] at hc hnew hv
      have hm :
          2 ≤ m ∧ m ≤ psi := by
        rcases hv with hn | hp <;> omega
      have hcast :
          (((m - 1 : Nat)) : Int) =
            ((m : Int) - 1) := by
        omega
      have hnew' :
          decodeOffset psi (tokenCode t') =
            (((m - 1 : Nat)) : Int) := by
        exact hnew.trans hcast.symm
      rw [hnew']
      have e1 : (Int.ofNat m).toNat = m := rfl
      have e2 : (((m - 1 : Nat)) : Int).toNat = m - 1 := rfl
      rw [e1, e2]
      omega

private def risvRRightNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (hc :
      2 ≤ decodeOffset psi (tokenCode t)) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hv : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  risvMkToken
    (encodeOffset psi (c - 1) (by
      rcases hv with hn | hp
      · exfalso
        omega
      · right
        omega))
    t.1.2 t.2


/-! ## New local facts for the rightmost initiator -/

private theorem risvLastNegativeTargetAbove
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) ≤
      tokenTargetCoordinate kind q t := by
  have hsum :=
    risvALastDistPlusD
      hpsi kind q hdist
  have hsumInt :
      (((q.dist.val + tokenD' psi kind :
        Nat)) : Int) =
        (((2 * psi - 1 : Nat)) : Int) :=
    congrArg (fun a : Nat => (a : Int)) hsum
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  have hb :
      1 - ((psi : Nat) : Int) ≤
          decodeOffset psi (tokenCode t) ∧
        decodeOffset psi (tokenCode t) ≤ -1 := by
    rcases hv with hn | hp
    · exact hn
    · exfalso
      omega
  have hnum :
      ((q.dist.val : Nat) : Int) +
            decodeOffset psi (tokenCode t) +
            ((tokenD' psi kind : Nat) : Int) =
        (((2 * psi - 1 : Nat)) : Int) +
          decodeOffset psi (tokenCode t) := by
    simp only [Int.natCast_add] at hsumInt
    omega
  unfold tokenTargetCoordinate
  rw [hnum]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

private theorem risvValidNotLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) %
          (2 * psi))
    (hlocal : risvLocalValid kind q t) :
    False := by
  have hl := hlocal
  unfold risvLocalValid at hl
  dsimp only at hl
  rcases hl with hp | hn
  · exact
      risvAPositiveNotLast
        hpsi kind q t hdist hlocal hp.1
  · have ht :=
      risvLastNegativeTargetAbove
        hpsi kind q t hdist hn.1
    omega

private theorem risvLocalValid_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t : TokenData psi)
    (hdist : q'.dist = q.dist)
    (h : risvLocalValid kind q t) :
    risvLocalValid kind q' t := by
  unfold risvLocalValid at h ⊢
  unfold tokenTargetCoordinate at h ⊢
  rw [hdist]
  exact h

private theorem risvLeftNeighbor_ne
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (i : Fin n) :
    ring.leftNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.leftNeighbor] at hv
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : n - 1 < n)] at hv
    omega
  · have hge : n ≤ i.val + n - 1 := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt
        (by omega : i.val + n - 1 - n < n)] at hv
    omega

private theorem risvBump_live_some
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (z z' : GhostToken n psi)
    (h :
      (risvBumpTo kind q v (some z)).live =
        some z') :
    z' =
        { value := v
          lmeta := ghostStepLineageAdvance z.lmeta } ∧
      risvLocalValid kind q v := by
  unfold risvBumpTo at h
  dsimp only at h
  by_cases hv : risvLocalValid kind q v
  · rw [if_pos hv] at h
    exact ⟨(Option.some.inj h).symm, hv⟩
  · rw [if_neg hv] at h
    cases h

/-! ### Physical selected-colour move of a live initiator with empty responder -/

private theorem risvMoveToken_initArrival
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate : l.last = false ∧ r.last = false)
    (hlv : risvLiveValue kind l = some t)
    (hrv : risvLiveValue kind r = none)
    (hc : decodeOffset psi (tokenCode t) = 1) :
    tokenAt kind (moveToken hpsi kind l r).2 =
      some (risvABounceNext hpsi t) := by
  rw [← risvMoveToken_eq hpsi kind l r]
  unfold risvMoveToken
  simp
    [risvSourceClear_token,
      risvSourceClear_last,
      risvSourceSet_token,
      risvABounceNext,
      hgate, hlv, hrv, hc]

private theorem risvMoveToken_initRight
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate : l.last = false ∧ r.last = false)
    (hlv : risvLiveValue kind l = some t)
    (hrv : risvLiveValue kind r = none)
    (hc : 2 ≤ decodeOffset psi (tokenCode t)) :
    tokenAt kind (moveToken hpsi kind l r).2 =
      some (risvRRightNext hpsi t hc) := by
  have h1 :
      decodeOffset psi (tokenCode t) ≠ 1 := by
    omega
  rw [← risvMoveToken_eq hpsi kind l r]
  unfold risvMoveToken
  simp
    [risvSourceClear_token,
      risvSourceClear_last,
      risvSourceSet_token,
      risvRRightNext,
      hgate, hlv, hrv, h1, hc]

private theorem risvMoveToken_initStay
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate : l.last = false ∧ r.last = false)
    (hlv : risvLiveValue kind l = some t)
    (hrv : risvLiveValue kind r = none)
    (hneg : decodeOffset psi (tokenCode t) < 0) :
    tokenAt kind (moveToken hpsi kind l r).1 =
      some t := by
  have h1 :
      decodeOffset psi (tokenCode t) ≠ 1 := by
    omega
  have h2 :
      ¬ 2 ≤ decodeOffset psi (tokenCode t) := by
    omega
  rw [← risvMoveToken_eq hpsi kind l r]
  unfold risvMoveToken
  simp
    [risvSourceClear_token,
      risvSourceClear_last,
      risvSourceSet_token,
      hgate, hlv, hrv, h1, h2]

/-! ### Ghost selected pair of a live initiator with empty responder -/

private theorem risvInitShape
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hgl : gl = some z)
    (hgr : gr = none)
    (hgate : l.last = false ∧ r.last = false)
    (htok : tokenAt kind l = some z.value)
    (hvalid : risvLocalValid kind l z.value)
    (hrv : risvLiveValue kind r = none) :
    risvGhostMoveToken
        hpsi kind step site l r gl gr =
      risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none := by
  classical
  let lv0 := risvLiveValue kind l
  let rv0 := risvLiveValue kind r
  let gl0 := risvLiveShadow kind l gl
  let gr0 := risvLiveShadow kind r gr
  let guard :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    risvBirthGhost hpsi kind step site l.id
  let lv1 :=
    if guard then some birth.value else lv0
  let gl1 :=
    if guard then some birth else gl0
  let collide := lv1 ≠ none ∧ rv0 ≠ none
  let lv2 := if collide then none else lv1
  let gl2 := if collide then none else gl1
  have hlv0 : lv0 = some z.value := by
    dsimp only [lv0]
    exact
      risvLiveValue_some
        kind l z.value htok hvalid
  have hgl0 : gl0 = some z := by
    dsimp only [gl0]
    exact
      risvLiveShadow_some
        kind l gl z hgl htok hvalid
  have hrv0 : rv0 = none := by
    dsimp only [rv0]
    exact hrv
  have hgr0 : gr0 = none := by
    dsimp only [gr0]
    rw [hgr]
    rfl
  have hguard : ¬ guard := by
    dsimp only [guard]
    intro hg
    have h2 := hg.2
    rw [hlv0] at h2
    cases h2
  have hlv1 : lv1 = some z.value := by
    simp [lv1, hguard, hlv0]
  have hgl1 : gl1 = some z := by
    simp [gl1, hguard, hgl0]
  have hcol : ¬ collide := by
    dsimp only [collide]
    intro hc
    exact hc.2 hrv0
  have hlv2 : lv2 = some z.value := by
    simp [lv2, hcol, hlv1]
  have hgl2 : gl2 = some z := by
    simp [gl2, hcol, hgl1]
  have hMoveEq :
      risvGhostMoveToken
          hpsi kind step site l r gl gr =
        risvGhostFinish
          hpsi kind l r lv2 rv0 gl2 gr0 := by
    unfold risvGhostMoveToken
    simp only [if_pos hgate]
    rfl
  rw [hMoveEq, hlv2, hrv0, hgl2, hgr0]

private theorem risvFinish_arrival
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (z : GhostToken n psi)
    (hc : decodeOffset psi (tokenCode z.value) = 1) :
    (risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none).left = none ∧
      (risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none).right =
        (risvBumpTo kind r
          (risvABounceNext hpsi z.value)
          (some z)).live := by
  unfold risvGhostFinish
  simp only [if_pos hc]
  first
    | (refine ⟨?_, ?_⟩ <;> first | rfl | trivial)
    | rfl
    | trivial

private theorem risvFinish_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (z : GhostToken n psi)
    (hc : 2 ≤ decodeOffset psi (tokenCode z.value)) :
    (risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none).left = none ∧
      (risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none).right =
        (risvBumpTo kind r
          (risvRRightNext hpsi z.value hc)
          (some z)).live := by
  have h1 :
      decodeOffset psi (tokenCode z.value) ≠ 1 := by
    omega
  unfold risvGhostFinish
  simp only [if_neg h1, dif_pos hc]
  first
    | (refine ⟨?_, ?_⟩ <;> first | rfl | trivial)
    | rfl
    | trivial

private theorem risvFinish_stay
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (z : GhostToken n psi)
    (hneg : decodeOffset psi (tokenCode z.value) < 0) :
    (risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none).left = some z ∧
      (risvGhostFinish
        hpsi kind l r (some z.value) none
        (some z) none).right = none := by
  have h1 :
      decodeOffset psi (tokenCode z.value) ≠ 1 := by
    omega
  have h2 :
      ¬ 2 ≤ decodeOffset psi (tokenCode z.value) := by
    omega
  unfold risvGhostFinish
  simp only [if_neg h1, dif_neg h2]
  first
    | (refine ⟨?_, ?_⟩ <;> first | rfl | trivial)
    | rfl
    | trivial

/-! ### Common setup -/

private theorem risvSetup
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (hright : Lemma4RightmostAt ring k kind G x z)
    (htrack : e = shiftRight ring k x.val) :
    let p :=
      risvSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    x.val + 1 < 2 * psi ∧
      2 * psi ≤ n ∧
      ring.rightNeighbor e ≠ e ∧
      ring.rightNeighbor e =
        shiftRight ring k (x.val + 1) ∧
      ghostTokenAt kind G e = some z ∧
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none ∧
      tokenAt kind (G.phys e) = some z.value ∧
      risvLocalValid kind (G.phys e) z.value ∧
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist ∧
      ghostStepSelectedPair
          hpsi ring step G e kind =
        risvGhostFinish
          hpsi kind p.1 p.2 (some z.value) none
          (some z) none ∧
      p.1.last = false ∧
      p.2.last = false ∧
      risvLiveValue kind p.1 = some z.value ∧
      risvLiveValue kind p.2 = none := by
  intro p
  have hfit :
      2 * psi ≤ n :=
    risvCd_fit
      hpsi ring k kind G.phys hCd
  have hn2 : 2 ≤ n := by
    omega
  have hne :
      ring.rightNeighbor e ≠ e :=
    risvRightNeighbor_ne ring hn2 e
  have hr0 := hright
  unfold Lemma4RightmostAt at hr0
  dsimp only at hr0
  have howner :
      ghostTokenAt kind G e = some z := by
    rw [htrack]
    exact hr0.1
  have htokPre :
      tokenAt kind (G.phys e) = some z.value :=
    risvGhostSound_token
      kind G e z hsound howner
  have hvalidPre :
      ValidToken kind G.phys e :=
    risvOwner_valid
      kind G e z hsound howner
  have hlocalPre :
      risvLocalValid kind (G.phys e) z.value := by
    unfold ValidToken at hvalidPre
    rw [htokPre] at hvalidPre
    exact hvalidPre
  have hnext :
      x.val + 1 < 2 * psi := by
    by_cases hlt : x.val + 1 < 2 * psi
    · exact hlt
    · exfalso
      have hxlast :
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
        rw [htrack, hrow.1, hxlast]
      exact
        risvValidNotLast
          hpsi kind (G.phys e) z.value
          hdistLast hlocalPre
  have hr :
      ring.rightNeighbor e =
        shiftRight ring k (x.val + 1) := by
    rw [htrack]
    exact
      risvRightNeighborShiftRight
        ring k x.val
  let y : Fin (2 * psi) :=
    ⟨x.val + 1, hnext⟩
  have hgr :
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none := by
    rw [hr]
    exact
      hr0.2.2 y
        (by
          show x.val < x.val + 1
          omega)
  have hwinE :
      Lemma4InWindow ring k psi e :=
    ⟨x, htrack⟩
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hr⟩
  have htokFrame :=
    risvSelectedInputTokenFrame
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
  have hdistL :
      p.1.dist = (G.phys e).dist :=
    risvSelectedInputDistLeft
      hpsi ring k kind step G e hne
      hCd hCd' hwinE
  have hdistR :
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist :=
    risvSelectedInputDistRight
      hpsi ring k kind step G e hne
      hCd hCd' hwinR
  have htokL :
      tokenAt kind p.1 = some z.value :=
    htokFrame.1.trans htokPre
  have hlocalL :
      risvLocalValid kind p.1 z.value :=
    risvLocalValid_dist
      kind (G.phys e) p.1 z.value
      hdistL hlocalPre
  have hlvL :
      risvLiveValue kind p.1 = some z.value :=
    risvLiveValue_some
      kind p.1 z.value htokL hlocalL
  have hlvR :
      risvLiveValue kind p.2 = none := by
    cases ht : tokenAt kind p.2 with
    | none =>
        unfold risvLiveValue
        rw [ht]
    | some t =>
        by_cases hv : risvLocalValid kind p.2 t
        · exfalso
          have hvPre :
              risvLocalValid kind
                (G.phys (ring.rightNeighbor e)) t :=
            risvLocalValid_dist
              kind p.2
              (G.phys (ring.rightNeighbor e)) t
              hdistR.symm hv
          have htokR :
              tokenAt kind
                  (G.phys (ring.rightNeighbor e)) =
                some t :=
            htokFrame.2.symm.trans ht
          have hvalidR :
              ValidToken kind G.phys
                (ring.rightNeighbor e) := by
            unfold ValidToken
            rw [htokR]
            exact hvPre
          rcases
              hcovered (ring.rightNeighbor e)
                hwinR hvalidR with
            ⟨zr, hzr⟩
          rw [hgr] at hzr
          cases hzr
        · unfold risvLiveValue
          rw [ht]
          simp only [if_neg hv]
  have hlastPair :=
    risvGhostStepLastPair
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
    risvCd_last_false
      ring k kind
      (ghostStep hpsi ring step G e).phys
      hCd' e hwinE
  have hlastR :
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).last =
        false :=
    risvCd_last_false
      ring k kind
      (ghostStep hpsi ring step G e).phys
      hCd' (ring.rightNeighbor e) hwinR
  have hgate :
      p.1.last = false ∧ p.2.last = false :=
    And.intro
      (hlastPair.1.symm.trans hlastE)
      (hlastPair.2.symm.trans hlastR)
  have hshape :=
    risvInitShape
      hpsi kind step e p.1 p.2
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G
        (ring.rightNeighbor e))
      z howner hgr hgate htokL hlocalL hlvR
  have hpair :
      ghostStepSelectedPair
          hpsi ring step G e kind =
        risvGhostFinish
          hpsi kind p.1 p.2 (some z.value) none
          (some z) none := by
    rw [← risvSelectedPair_eq_export
      hpsi ring step G e kind]
    exact hshape
  exact
    ⟨hnext, hfit, hne, hr, howner, hgr,
      htokPre, hlocalPre, hdistR, hpair,
      hgate.1, hgate.2, hlvL, hlvR⟩

/-! ### Rightmost bookkeeping -/

private theorem risvRightmostMovedRight
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (z z' : GhostToken n psi)
    (hfit : 2 * psi ≤ n)
    (hne : ring.rightNeighbor e ≠ e)
    (hright : Lemma4RightmostAt ring k kind G x z)
    (htrack : e = shiftRight ring k x.val)
    (hyx : y.val = x.val + 1)
    (hr : ring.rightNeighbor e = shiftRight ring k y.val)
    (hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right =
        some z')
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)) :
    Lemma4RightmostAt ring k kind
      (ghostStep hpsi ring step G e) y z' := by
  have hright0 := hright
  unfold Lemma4RightmostAt at hright0
  dsimp only at hright0
  unfold Lemma4RightmostAt
  dsimp only
  refine And.intro ?_ (And.intro ?_ ?_)
  · rw [← hr]
    exact
      (ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e kind hne).trans
        hpairRight
  · rw [← hr]
    exact hvalid
  · intro q hq
    let j := shiftRight ring k q.val
    have hje : j ≠ e := by
      intro hj
      have hs :
          shiftRight ring k q.val =
            shiftRight ring k x.val :=
        hj.trans htrack
      have hv :=
        risvShiftRightInjectiveLt
          ring k q.val x.val
          (by omega) (by omega) hs
      omega
    have hjr : j ≠ ring.rightNeighbor e := by
      intro hj
      have hs :
          shiftRight ring k q.val =
            shiftRight ring k y.val :=
        hj.trans hr
      have hv :=
        risvShiftRightInjectiveLt
          ring k q.val y.val
          (by omega) (by omega) hs
      omega
    have hpreNone :
        ghostTokenAt kind G j = none :=
      hright0.2.2 q (by omega)
    rw [ghostTokenAt_ghostStep_frame
      hpsi ring step G e j kind hje hjr]
    exact hpreNone

private theorem risvRightmostStay
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi)
    (hfit : 2 * psi ≤ n)
    (hne : ring.rightNeighbor e ≠ e)
    (hright : Lemma4RightmostAt ring k kind G x z)
    (htrack : e = shiftRight ring k x.val)
    (hpairLeft :
      (ghostStepSelectedPair
        hpsi ring step G e kind).left =
        some z)
    (hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right =
        none)
    (hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e) :
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
      (ghostTokenAt_ghostStep_initiator
        hpsi ring step G e kind).trans
        hpairLeft
  · rw [← htrack]
    exact hvalid
  · intro q hq
    let j := shiftRight ring k q.val
    have hje : j ≠ e := by
      intro hj
      have hs :
          shiftRight ring k q.val =
            shiftRight ring k x.val :=
        hj.trans htrack
      have hv :=
        risvShiftRightInjectiveLt
          ring k q.val x.val
          (by omega) (by omega) hs
      omega
    by_cases hjr : j = ring.rightNeighbor e
    · change
        ghostTokenAt kind
          (ghostStep hpsi ring step G e) j = none
      rw [hjr,
        ghostTokenAt_ghostStep_responder_of_ne
          hpsi ring step G e kind hne]
      exact hpairRight
    · rw [ghostTokenAt_ghostStep_frame
        hpsi ring step G e j kind hje hjr]
      exact hright0.2.2 q hq

/-! ## The three offset-local rows -/

theorem lemma4RightmostInitiatorSurvivalArrivalLocalRow_proved :
    Lemma4RightmostInitiatorSurvivalArrivalLocalRow := by
  unfold Lemma4RightmostInitiatorSurvivalArrivalLocalRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound hright htrack hsame hc
  have hsetup :=
    risvSetup
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound hright htrack
  let p :=
    risvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  change
    x.val + 1 < 2 * psi ∧
      2 * psi ≤ n ∧
      ring.rightNeighbor e ≠ e ∧
      ring.rightNeighbor e =
        shiftRight ring k (x.val + 1) ∧
      ghostTokenAt kind G e = some z ∧
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none ∧
      tokenAt kind (G.phys e) = some z.value ∧
      risvLocalValid kind (G.phys e) z.value ∧
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist ∧
      ghostStepSelectedPair
          hpsi ring step G e kind =
        risvGhostFinish
          hpsi kind p.1 p.2 (some z.value) none
          (some z) none ∧
      p.1.last = false ∧
      p.2.last = false ∧
      risvLiveValue kind p.1 = some z.value ∧
      risvLiveValue kind p.2 = none
    at hsetup
  rcases hsetup with
    ⟨hnext, hfit, hne, hr, _howner, _hgr,
      _htokPre, hlocalPre, hdistR, hpair,
      hgateL, hgateR, hlvL, hlvR⟩
  let next := risvABounceNext hpsi z.value
  have hfin :=
    risvFinish_arrival
      hpsi kind p.1 p.2 z hc
  have hpairLeft :
      (ghostStepSelectedPair
        hpsi ring step G e kind).left = none := by
    rw [hpair]
    exact hfin.1
  have hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right =
        (risvBumpTo kind p.2 next (some z)).live := by
    rw [hpair]
    exact hfin.2
  have hexR :
      ∃ z' : GhostToken n psi,
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
    rcases hsame with ⟨zL, hL, _⟩ | ⟨zR, hR, _⟩
    · rw [hpairLeft] at hL
      cases hL
    · exact ⟨zR, hR⟩
  rcases hexR with ⟨z', hR⟩
  rcases
      risvBump_live_some
        kind p.2 next z z'
        (hpairRight.symm.trans hR) with
    ⟨hz', hlocalNext⟩
  have hphysTok :=
    risvMoveToken_initArrival
      hpsi kind p.1 p.2 z.value
      ⟨hgateL, hgateR⟩ hlvL hlvR hc
  have hstepTok :=
    risvGhostStepTokenPairAt
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
    at hstepTok
  have htokPost :
      tokenAt kind
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)) =
        some z'.value := by
    rw [hstepTok.2, hphysTok, hz'] <;> rfl
  let y : Fin (2 * psi) := ⟨x.val + 1, hnext⟩
  have hry :
      ring.rightNeighbor e =
        shiftRight ring k y.val := hr
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hry⟩
  have hdistPostR :=
    risvCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' (ring.rightNeighbor e) hwinR
  have hdistP2Post :
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        p.2.dist :=
    hdistPostR.trans hdistR.symm
  have hlocalPost :
      risvLocalValid kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        next :=
    risvLocalValid_dist
      kind p.2 _ next hdistP2Post hlocalNext
  have hvalidPost :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e) := by
    unfold ValidToken
    rw [htokPost, hz']
    exact hlocalPost
  have hdecode :
      decodeOffset psi (tokenCode next) =
        1 - ((psi : Nat) : Int) := by
    show
      decodeOffset psi
          (tokenCode (risvABounceNext hpsi z.value)) =
        1 - ((psi : Nat) : Int)
    unfold risvABounceNext
    dsimp [risvMkToken, tokenCode]
    exact decodeOffset_negPsiPlusOne psi hpsi
  have hpreDist :
      (G.phys e).dist.val =
        (x.val + tokenD' psi kind) %
          (2 * psi) := by
    have h := hCd x
    dsimp only at h
    rw [htrack]
    exact h.1
  have hpostDist :
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val =
        (x.val + 1 + tokenD' psi kind) %
          (2 * psi) := by
    have h := hCd' y
    dsimp only at h
    rw [hr]
    exact h.1
  have holdTarget :
      tokenTargetCoordinate kind
          (G.phys e) z.value =
        (((x.val + 1 : Nat)) : Int) :=
    risvAOldTarget
      hpsi kind (G.phys e) z.value
      x.val x.isLt hnext hpreDist hc
  have hlowTarget :
      ((psi : Nat) : Int) ≤
        tokenTargetCoordinate kind
          (G.phys e) z.value := by
    have hl := hlocalPre
    unfold risvLocalValid at hl
    dsimp only at hl
    rw [hc] at hl
    rcases hl with hp | hn
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
          next =
        (((x.val + 2 - psi : Nat)) : Int) :=
    risvABounceTarget
      hpsi kind
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e))
      next x.val hnext hlow
      hpostDist hdecode
  have hstage :
      lemma4TokenStage kind
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e))
          next =
        lemma4TokenStage kind
            (G.phys e) z.value :=
    risvAStage_eq
      hpsi kind
      (G.phys e)
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e))
      z.value next x.val hlow
      hc hdecode holdTarget hnewTarget
  have hprogress :
      lemma4TokenProgress kind
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e))
          next =
        lemma4TokenProgress kind
            (G.phys e) z.value + 1 :=
    risvAProgress_eq
      hpsi kind
      (G.phys e)
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e))
      z.value next
      hc hdecode hstage
  have hprog' :
      lemma4TokenProgress kind
          ((ghostStep hpsi ring step G e).phys
            (shiftRight ring k y.val))
          z'.value =
        lemma4TokenProgress kind
            (G.phys e) z.value + 1 := by
    rw [← hry, hz']
    exact hprogress
  have hRm :
      Lemma4RightmostAt ring k kind
        (ghostStep hpsi ring step G e) y z' :=
    risvRightmostMovedRight
      hpsi ring k kind step G e x y z z'
      hfit hne hright htrack rfl hry hR
      hvalidPost
  have hid : z'.lmeta.id = z.lmeta.id := by
    rw [hz'] <;> rfl
  have hfresh :
      FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta :=
    risvFresh_advance kind k z z'
      (by rw [hz'] <;> rfl)
  unfold Lemma4RightmostInitiatorSurvivalStateLocalConclusion
  dsimp only
  rw [← htrack]
  exact
    ⟨y, z', hRm, hid, hfresh,
      by omega,
      fun _ => hprog'⟩

theorem lemma4RightmostInitiatorSurvivalRightMoveLocalRow_proved :
    Lemma4RightmostInitiatorSurvivalRightMoveLocalRow := by
  unfold Lemma4RightmostInitiatorSurvivalRightMoveLocalRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound hright htrack hsame hc
  have hsetup :=
    risvSetup
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound hright htrack
  let p :=
    risvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  change
    x.val + 1 < 2 * psi ∧
      2 * psi ≤ n ∧
      ring.rightNeighbor e ≠ e ∧
      ring.rightNeighbor e =
        shiftRight ring k (x.val + 1) ∧
      ghostTokenAt kind G e = some z ∧
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none ∧
      tokenAt kind (G.phys e) = some z.value ∧
      risvLocalValid kind (G.phys e) z.value ∧
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist ∧
      ghostStepSelectedPair
          hpsi ring step G e kind =
        risvGhostFinish
          hpsi kind p.1 p.2 (some z.value) none
          (some z) none ∧
      p.1.last = false ∧
      p.2.last = false ∧
      risvLiveValue kind p.1 = some z.value ∧
      risvLiveValue kind p.2 = none
    at hsetup
  rcases hsetup with
    ⟨hnext, hfit, hne, hr, _howner, _hgr,
      _htokPre, _hlocalPre, hdistR, hpair,
      hgateL, hgateR, hlvL, hlvR⟩
  let next := risvRRightNext hpsi z.value hc
  have hfin :=
    risvFinish_right
      hpsi kind p.1 p.2 z hc
  have hpairLeft :
      (ghostStepSelectedPair
        hpsi ring step G e kind).left = none := by
    rw [hpair]
    exact hfin.1
  have hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right =
        (risvBumpTo kind p.2 next (some z)).live := by
    rw [hpair]
    exact hfin.2
  have hexR :
      ∃ z' : GhostToken n psi,
        (ghostStepSelectedPair
          hpsi ring step G e kind).right =
          some z' := by
    rcases hsame with ⟨zL, hL, _⟩ | ⟨zR, hR, _⟩
    · rw [hpairLeft] at hL
      cases hL
    · exact ⟨zR, hR⟩
  rcases hexR with ⟨z', hR⟩
  rcases
      risvBump_live_some
        kind p.2 next z z'
        (hpairRight.symm.trans hR) with
    ⟨hz', hlocalNext⟩
  have hphysTok :=
    risvMoveToken_initRight
      hpsi kind p.1 p.2 z.value
      ⟨hgateL, hgateR⟩ hlvL hlvR hc
  have hstepTok :=
    risvGhostStepTokenPairAt
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
    at hstepTok
  have htokPost :
      tokenAt kind
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)) =
        some z'.value := by
    rw [hstepTok.2, hphysTok, hz'] <;> rfl
  let y : Fin (2 * psi) := ⟨x.val + 1, hnext⟩
  have hry :
      ring.rightNeighbor e =
        shiftRight ring k y.val := hr
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hry⟩
  have hdistPostR :=
    risvCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' (ring.rightNeighbor e) hwinR
  have hdistP2Post :
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist =
        p.2.dist :=
    hdistPostR.trans hdistR.symm
  have hlocalPost :
      risvLocalValid kind
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        next :=
    risvLocalValid_dist
      kind p.2 _ next hdistP2Post hlocalNext
  have hvalidPost :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e) := by
    unfold ValidToken
    rw [htokPost, hz']
    exact hlocalPost
  have hdecode :
      decodeOffset psi (tokenCode next) =
        decodeOffset psi (tokenCode z.value) - 1 := by
    show
      decodeOffset psi
          (tokenCode (risvRRightNext hpsi z.value hc)) =
        decodeOffset psi (tokenCode z.value) - 1
    unfold risvRRightNext
    dsimp [risvMkToken, tokenCode]
    exact decode_encode _ _ _
  have hpreDist :
      (G.phys e).dist.val =
        (x.val + tokenD' psi kind) %
          (2 * psi) := by
    have h := hCd x
    dsimp only at h
    rw [htrack]
    exact h.1
  have hpostDist :
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val =
        (x.val + 1 + tokenD' psi kind) %
          (2 * psi) := by
    have h := hCd' y
    dsimp only at h
    rw [hr]
    exact h.1
  have hsucc :
      ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e)).dist.val =
        ((G.phys e).dist.val + 1) %
          (2 * psi) :=
    risvRCanonicalSucc
      hpsi x.val (tokenD' psi kind)
      (G.phys e).dist.val
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)).dist.val
      hpreDist hpostDist
  have htarget :=
    risvRRightMoveTarget
      hpsi kind
      (G.phys e)
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e))
      z.value next
      hsucc hc hdecode
  have hprogress :
      lemma4TokenProgress kind
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e))
          next =
        lemma4TokenProgress kind
            (G.phys e) z.value + 1 :=
    risvRRightMoveProgress
      kind
      (G.phys e)
      ((ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e))
      z.value next
      hc hdecode htarget
  have hprog' :
      lemma4TokenProgress kind
          ((ghostStep hpsi ring step G e).phys
            (shiftRight ring k y.val))
          z'.value =
        lemma4TokenProgress kind
            (G.phys e) z.value + 1 := by
    rw [← hry, hz']
    exact hprogress
  have hRm :
      Lemma4RightmostAt ring k kind
        (ghostStep hpsi ring step G e) y z' :=
    risvRightmostMovedRight
      hpsi ring k kind step G e x y z z'
      hfit hne hright htrack rfl hry hR
      hvalidPost
  have hid : z'.lmeta.id = z.lmeta.id := by
    rw [hz'] <;> rfl
  have hfresh :
      FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta :=
    risvFresh_advance kind k z z'
      (by rw [hz'] <;> rfl)
  unfold Lemma4RightmostInitiatorSurvivalStateLocalConclusion
  dsimp only
  rw [← htrack]
  exact
    ⟨y, z', hRm, hid, hfresh,
      by omega,
      fun _ => hprog'⟩

theorem lemma4RightmostInitiatorSurvivalTurnLocalRow_proved :
    Lemma4RightmostInitiatorSurvivalTurnLocalRow := by
  unfold Lemma4RightmostInitiatorSurvivalTurnLocalRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound hright htrack _hsame hneg
  have hsetup :=
    risvSetup
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound hright htrack
  let p :=
    risvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  change
    x.val + 1 < 2 * psi ∧
      2 * psi ≤ n ∧
      ring.rightNeighbor e ≠ e ∧
      ring.rightNeighbor e =
        shiftRight ring k (x.val + 1) ∧
      ghostTokenAt kind G e = some z ∧
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none ∧
      tokenAt kind (G.phys e) = some z.value ∧
      risvLocalValid kind (G.phys e) z.value ∧
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist ∧
      ghostStepSelectedPair
          hpsi ring step G e kind =
        risvGhostFinish
          hpsi kind p.1 p.2 (some z.value) none
          (some z) none ∧
      p.1.last = false ∧
      p.2.last = false ∧
      risvLiveValue kind p.1 = some z.value ∧
      risvLiveValue kind p.2 = none
    at hsetup
  rcases hsetup with
    ⟨_hnext, hfit, hne, _hr, howner, _hgr,
      htokPre, _hlocalPre, _hdistR, hpair,
      hgateL, hgateR, hlvL, hlvR⟩
  have hfin :=
    risvFinish_stay
      hpsi kind p.1 p.2 z hneg
  have hpairLeft :
      (ghostStepSelectedPair
        hpsi ring step G e kind).left = some z := by
    rw [hpair]
    exact hfin.1
  have hpairRight :
      (ghostStepSelectedPair
        hpsi ring step G e kind).right = none := by
    rw [hpair]
    exact hfin.2
  have hphysTok :=
    risvMoveToken_initStay
      hpsi kind p.1 p.2 z.value
      ⟨hgateL, hgateR⟩ hlvL hlvR hneg
  have hstepTok :=
    risvGhostStepTokenPairAt
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
    at hstepTok
  have htokPost :
      tokenAt kind
          ((ghostStep hpsi ring step G e).phys e) =
        some z.value :=
    hstepTok.1.trans hphysTok
  have hwinE :
      Lemma4InWindow ring k psi e :=
    ⟨x, htrack⟩
  have hdistE :
      ((ghostStep hpsi ring step G e).phys e).dist =
        (G.phys e).dist :=
    risvCd_dist_same
      ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' e hwinE
  have hvalidPre :
      ValidToken kind G.phys e :=
    risvOwner_valid
      kind G e z hsound howner
  have hvalidPost :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e :=
    risvValid_same_dist
      kind G.phys
      (ghostStep hpsi ring step G e).phys
      e z.value
      htokPre htokPost hdistE hvalidPre
  have hprogress :
      lemma4TokenProgress kind
          ((ghostStep hpsi ring step G e).phys e)
          z.value =
        lemma4TokenProgress kind
          (G.phys e) z.value :=
    risvProgress_dist_eq
      kind (G.phys e)
      ((ghostStep hpsi ring step G e).phys e)
      z.value hdistE
  have hprog' :
      lemma4TokenProgress kind
          ((ghostStep hpsi ring step G e).phys
            (shiftRight ring k x.val))
          z.value =
        lemma4TokenProgress kind
          (G.phys e) z.value := by
    rw [← htrack]
    exact hprogress
  have hRm :
      Lemma4RightmostAt ring k kind
        (ghostStep hpsi ring step G e) x z :=
    risvRightmostStay
      hpsi ring k kind step G e x z
      hfit hne hright htrack
      hpairLeft hpairRight hvalidPost
  have hn2 : 2 ≤ n := by
    omega
  have hservice :
      e = lemma4ServiceEdge ring kind G e z →
        False := by
    intro hs
    have hnp :
        ¬ 0 < decodeOffset psi (tokenCode z.value) := by
      omega
    unfold lemma4ServiceEdge at hs
    rw [if_neg hnp] at hs
    exact risvLeftNeighbor_ne ring hn2 e hs.symm
  unfold Lemma4RightmostInitiatorSurvivalStateLocalConclusion
  dsimp only
  rw [← htrack]
  exact
    ⟨x, z, hRm, rfl, (fun hf => hf),
      by omega,
      fun hs => False.elim (hservice hs)⟩

theorem lemma4RightmostInitiatorSurvivalStateLocalResidual_proved :
    Lemma4RightmostInitiatorSurvivalStateLocalResidual :=
  lemma4RightmostInitiatorSurvivalStateLocalResidual_of_localRows
    lemma4RightmostInitiatorSurvivalArrivalLocalRow_proved
    lemma4RightmostInitiatorSurvivalRightMoveLocalRow_proved
    lemma4RightmostInitiatorSurvivalTurnLocalRow_proved

end PPL

#print axioms PPL.lemma4RightmostInitiatorSurvivalArrivalLocalRow_proved
#print axioms PPL.lemma4RightmostInitiatorSurvivalRightMoveLocalRow_proved
#print axioms PPL.lemma4RightmostInitiatorSurvivalTurnLocalRow_proved
#print axioms PPL.lemma4RightmostInitiatorSurvivalStateLocalResidual_proved
