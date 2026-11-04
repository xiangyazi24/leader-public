import Leader.PPL.TokenCompletion.SweepResponder
import Leader.PPL.TransitionFacts
import Leader.PPL.TokenCompletion.SweepResponderNegTurn


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-
Only the exceptional responder return is left as a residual.


All hypotheses below are already available after the finite selected-pair
classification.  The row contains only the c = -1 geometry/rank calculation:
the tracked responder moves to e, its metadata is bumped once, and the new
offset is +psi.
-/
def Lemma4SweepResponderNegTurnProgressRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z z' : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    GhostSound G →
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) →
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z →
    (ghostStepSelectedPair
        hpsi ring step G e kind).left =
      some z' →
    z'.lmeta.id = z.lmeta.id →
    z'.lmeta = ghostStepLineageAdvance z.lmeta →
    decodeOffset psi (tokenCode z.value) = -1 →
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys e) =
      some z'.value →
    decodeOffset psi (tokenCode z'.value) =
      ((psi : Nat) : Int) →
    Lemma4InWindow ring k psi e ∧
      (FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta) ∧
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e ∧
      lemma4TokenProgress
          kind
          (G.phys (ring.rightNeighbor e))
          z.value ≤
        lemma4TokenProgress
          kind
          ((ghostStep hpsi ring step G e).phys e)
          z'.value ∧
      (e =
          lemma4ServiceEdge
            ring kind G (ring.rightNeighbor e) z →
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys e)
            z'.value =
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value +
            1)


/-! -----------------------------------------------------------------------
    Literal selected-colour mirrors
------------------------------------------------------------------------ -/


private def sweepRespBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def sweepRespMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def sweepRespLocalValid
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
    Decidable (sweepRespLocalValid kind q t) := by
  unfold sweepRespLocalValid
  infer_instance


private def sweepRespSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def sweepRespClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if sweepRespLocalValid kind q t then
        q
      else
        sweepRespSetToken kind q none


private def sweepRespLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


private theorem sweepRespSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      sweepRespSetToken kind q t := by
  cases kind <;> rfl


private theorem sweepRespSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      sweepRespClearInvalid kind q := by
  cases kind <;> rfl


private theorem sweepRespSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = sweepRespLeaderBirth q := by
  rfl


private def sweepRespNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    sweepRespMkToken
      (offsetPsiCode psi hpsi)
      (sweepRespBitToFin (!sourceBit))
      (sweepRespBitToFin sourceBit)
  else
    sweepRespMkToken
      (offsetPsiCode psi hpsi)
      (sweepRespBitToFin sourceBit)
      (0 : Fin 2)


private def sweepRespLiveShadow
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
              sweepRespLocalValid kind q t then
            some z
          else
            none


private def sweepRespLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if sweepRespLocalValid kind q t then
        some t
      else
        none


private def sweepRespBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      sweepRespMkToken
        (offsetPsiCode psi hpsi)
        (sweepRespBitToFin (!idBit))
        (sweepRespBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def sweepRespBumpTo
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
        if sweepRespLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def sweepRespGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := sweepRespLiveValue kind l
  let rv0 := sweepRespLiveValue kind r
  let gl0 := sweepRespLiveShadow kind l gl
  let gr0 := sweepRespLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (sweepRespBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (sweepRespBirthGhost
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
            sweepRespMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            sweepRespBumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            sweepRespMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            sweepRespBumpTo kind r next gl2
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
                  sweepRespNegTurnNext
                    hpsi l.id t
                let b :=
                  sweepRespBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c ≤ -2 then
                have hbranch : c ≤ -2 := hm2
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  sweepRespMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  sweepRespBumpTo
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
                sweepRespNegTurnNext
                  hpsi l.id t
              let b :=
                sweepRespBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                sweepRespMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                sweepRespBumpTo
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
private def sweepRespMoveToken
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
            (sweepRespMkToken
              (offsetPsiCode psi hpsi)
              (sweepRespBitToFin (!l.id))
              (sweepRespBitToFin l.id)))
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
                sweepRespNegTurnNext hpsi l.id t
              (sourceSet kind l (some next),
                sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hbranch : c ≤ -2 := hm2
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                sweepRespMkToken
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
                (sweepRespMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2)))
        else if h2 : 2 ≤ c then
          have hbranch : 2 ≤ c := h2
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            sweepRespMkToken
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


private theorem sweepRespMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    sweepRespMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl


private def sweepRespPrelude
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


private def sweepRespSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := sweepRespPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2


private def sweepRespSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    sweepRespSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  sweepRespGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))


private theorem sweepRespSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    sweepRespSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl


/-! -----------------------------------------------------------------------
    Finite ghost-row facts
------------------------------------------------------------------------ -/


/-
Every live ghost output of the local mirror has exactly the value carried by
the corresponding literal Algorithm-3 output.  No lineage assumption is
needed here.
-/
private def SweepRespOptionSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) : Prop :=
  forall z : GhostToken n psi,
    g = some z ->
    And
      (tokenAt kind q = some z.value)
      (sweepRespLocalValid kind q z.value)




private def SweepRespAlignedSound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi))
    (g : Option (GhostToken n psi)) : Prop :=
  And
    (tokenAt kind q = v)
    (SweepRespOptionSound kind q g)




private theorem sweepRespLocalValid_of_dist_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t : TokenData psi)
    (hdist : q'.dist = q.dist)
    (hvalid : sweepRespLocalValid kind q t) :
    sweepRespLocalValid kind q' t := by
  unfold sweepRespLocalValid at hvalid ⊢
  unfold tokenTargetCoordinate at hvalid ⊢
  rw [hdist]
  exact hvalid




private theorem sweepRespSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q t) = t := by
  rw [sweepRespSourceSet_eq]
  cases kind <;> rfl




private theorem sweepRespSourceSet_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).dist = q.dist := by
  rw [sweepRespSourceSet_eq]
  cases kind <;> rfl




private theorem sweepRespSourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).id = q.id := by
  rw [sweepRespSourceSet_eq]
  cases kind <;> rfl




private theorem sweepRespSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      sweepRespLiveValue kind q := by
  rw [sweepRespSourceClear_eq]
  unfold sweepRespClearInvalid
    sweepRespLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv :
          sweepRespLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold sweepRespSetToken
        cases kind <;> rfl




private theorem sweepRespSourceClear_fields
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
  rw [sweepRespSourceClear_eq]
  unfold sweepRespClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      exact ⟨rfl, rfl, rfl⟩
  | some t =>
      by_cases hv :
          sweepRespLocalValid kind q t
      · simp only [if_pos hv]
        refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial
      · simp only [if_neg hv]
        unfold sweepRespSetToken
        cases kind <;>
          exact ⟨rfl, rfl, rfl⟩




private theorem sweepRespLiveShadow_aligned
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    SweepRespAlignedSound
      kind
      (sourceClear kind q)
      (sweepRespLiveValue kind q)
      (sweepRespLiveShadow kind q g) := by
  constructor
  · exact sweepRespSourceClear_token kind q
  · unfold SweepRespOptionSound
    intro z hz
    unfold sweepRespLiveShadow at hz
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
                  (sweepRespLocalValid kind q t)
            · simp only [if_pos hkeep] at hz
              cases hz
              constructor
              · rw [
                  sweepRespSourceClear_token,
                  sweepRespLiveValue,
                  ht]
                simp only [if_pos hkeep.2, hkeep.1]
              · rw [hkeep.1]
                exact
                  sweepRespLocalValid_of_dist_eq
                    kind q (sourceClear kind q) t
                    (sweepRespSourceClear_fields
                      kind q).1
                    hkeep.2
            · simp only [if_neg hkeep] at hz
              cases hz




/-- The liveShadow stay branch, with both endpoint soundness conjuncts. -/
private theorem sweepRespGhostMoveToken_liveShadow_stay
    {n psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    And
      (SweepRespOptionSound
        kind (sourceClear kind l)
        (sweepRespLiveShadow kind l gl))
      (SweepRespOptionSound
        kind (sourceClear kind r)
        (sweepRespLiveShadow kind r gr)) := by
  exact
    And.intro
      (sweepRespLiveShadow_aligned
        kind l gl).2
      (sweepRespLiveShadow_aligned
        kind r gr).2




private theorem sweepRespBirth_localValid
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (q : State psi kappa)
    (hdist :
      q.dist.val = tokenD' psi kind) :
    sweepRespLocalValid kind q
      (sweepRespBirthGhost
        hpsi kind step site idBit).value := by
  let birth :=
    sweepRespBirthGhost
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
  unfold sweepRespLocalValid
  rw [hcode, htarget]
  exact
    Or.inl
      ⟨by omega, by omega, by omega⟩




private theorem sweepRespBirthGhost_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (q : State psi kappa)
    (hdist :
      q.dist.val = tokenD' psi kind) :
    SweepRespOptionSound kind
      (sourceSet kind q
        (some
          (sweepRespBirthGhost
            hpsi kind step site idBit).value))
      (some
        (sweepRespBirthGhost
          hpsi kind step site idBit)) := by
  let birth :=
    sweepRespBirthGhost
      hpsi kind step site idBit
  unfold SweepRespOptionSound
  intro z hz
  cases hz
  constructor
  · exact
      sweepRespSourceSet_token
        kind q (some birth.value)
  · apply
      sweepRespBirth_localValid
        hpsi kind step site idBit
        (q :=
          sourceSet kind q (some birth.value))
    have hframe :=
      sweepRespSourceSet_dist
        kind q (some birth.value)
    have hval :=
      congrArg Fin.val hframe
    exact hval.trans hdist




/-- The birthGhost branch, with the fresh left owner and right live shadow. -/
private theorem sweepRespGhostMoveToken_birthGhost
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
      (SweepRespOptionSound kind
        (sourceSet kind l
          (some
            (sweepRespBirthGhost
              hpsi kind step site idBit).value))
        (some
          (sweepRespBirthGhost
            hpsi kind step site idBit)))
      (SweepRespOptionSound kind
        (sourceClear kind r)
        (sweepRespLiveShadow kind r gr)) := by
  exact
    And.intro
      (sweepRespBirthGhost_sound
        hpsi kind step site idBit l hdist)
      (sweepRespLiveShadow_aligned
        kind r gr).2




private theorem sweepRespOptionSound_none
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    SweepRespOptionSound
      (n := n) kind q none := by
  unfold SweepRespOptionSound
  intro z hz
  cases hz




/--
The bumpTo movement branch.  The first pair is the right-moving orientation
(gone, destination), and the second pair is the left-moving orientation
(destination, gone).
-/
private theorem sweepRespGhostMoveToken_bumpTo_move
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
        (SweepRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qGone
          (none : Option (GhostToken n psi)))
        (SweepRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qDest
          (sweepRespBumpTo
            (n := n) (psi := psi) (kappa := kappa)
            kind base next g).live))
      (And
        (SweepRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qDest
          (sweepRespBumpTo
            (n := n) (psi := psi) (kappa := kappa)
            kind base next g).live)
        (SweepRespOptionSound
          (n := n) (psi := psi) (kappa := kappa)
          kind qGone
          (none : Option (GhostToken n psi)))) := by
  have hnone :
      SweepRespOptionSound
        (n := n) (psi := psi) (kappa := kappa)
        kind qGone
        (none : Option (GhostToken n psi)) :=
    sweepRespOptionSound_none
      (n := n) (psi := psi) (kappa := kappa)
      kind qGone
  have hlive :
      SweepRespOptionSound
        (n := n) (psi := psi) (kappa := kappa)
        kind qDest
        (sweepRespBumpTo
          (n := n) (psi := psi) (kappa := kappa)
          kind base next g).live := by
    unfold SweepRespOptionSound
    intro z' hz'
    cases hg : g with
    | none =>
        simp only
          [sweepRespBumpTo, hg] at hz'
        cases hz'
    | some z =>
        by_cases hv :
            sweepRespLocalValid kind base next
        · simp only
            [sweepRespBumpTo,
              hg, if_pos hv] at hz'
          cases hz'
          constructor
          · exact htok
          · exact
              sweepRespLocalValid_of_dist_eq
                kind base qDest next hdist hv
        · simp only
            [sweepRespBumpTo,
              hg, if_neg hv] at hz'
          cases hz'
  exact
    And.intro
      (And.intro hnone hlive)
      (And.intro hlive hnone)




private def sweepRespOneResponder
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) : State psi kappa :=
  if r.mode = true ∧ bit ≠ r.id then
    sourceBirth r
  else if r.mode = false then
    { r with id := bit }
  else
    r




private theorem sweepRespOneResponder_dist
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) :
    (sweepRespOneResponder r bit).dist =
      r.dist := by
  unfold sweepRespOneResponder
  by_cases hbirth :
      r.mode = true ∧ bit ≠ r.id
  · rw [if_pos hbirth, sweepRespSourceBirth_eq] <;> rfl
  · rw [if_neg hbirth]
    by_cases hmode : r.mode = false
    · rw [if_pos hmode]
    · rw [if_neg hmode]




private def sweepRespPhysicalFinish
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
          if c = -1 then
            let next :=
              sweepRespNegTurnNext
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
                  (sweepRespMkToken
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
      if c = 1 then
        let bit := tokenBitBool t
        let r :=
          sweepRespOneResponder r bit
        let r :=
          sourceSet kind r
            (some
              (sweepRespMkToken
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
              (sweepRespMkToken
                nextOffset t.1.2 t.2))
        let l := sourceSet kind l none
        (l, r)
      else
        moveLeft l r




private def sweepRespGhostFinish
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
      if c = 1 then
        let next :=
          sweepRespMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          sweepRespBumpTo kind baseR next gl
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          sweepRespMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          sweepRespBumpTo kind baseR next gl
        ⟨none, b.live, b.done⟩
      else
        match rv with
        | none =>
            ⟨gl, gr, []⟩
        | some tr =>
            let cr :=
              decodeOffset psi (tokenCode tr)
            if cr = -1 then
              let next :=
                sweepRespNegTurnNext
                  hpsi baseL.id tr
              let b :=
                sweepRespBumpTo
                  kind baseL next gr
              ⟨b.live, none, b.done⟩
            else if hm2 : cr <= -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                sweepRespMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b :=
                sweepRespBumpTo
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
          if cr = -1 then
            let next :=
              sweepRespNegTurnNext
                hpsi baseL.id tr
            let b :=
              sweepRespBumpTo
                kind baseL next gr
            ⟨b.live, none, b.done⟩
          else if hm2 : cr <= -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid
                psi (by omega) (tokenCode tr)
            let next :=
              sweepRespMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b :=
              sweepRespBumpTo
                kind baseL next gr
            ⟨b.live, none, b.done⟩
          else
            ⟨gl, gr, []⟩




private theorem sweepRespGhostMoveToken_finish_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (hleft :
      SweepRespAlignedSound
        kind l lv gl)
    (hright :
      SweepRespAlignedSound
        kind r rv gr)
    (hLdist : l.dist = baseL.dist)
    (hRdist : r.dist = baseR.dist)
    (hLid : l.id = baseL.id) :
    let q :=
      sweepRespPhysicalFinish
        hpsi kind l r
    let g :=
      sweepRespGhostFinish
        hpsi kind baseL baseR lv rv gl gr
    And
      (SweepRespOptionSound
        kind q.1 g.left)
      (SweepRespOptionSound
        kind q.2 g.right) := by
  cases lv with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [sweepRespPhysicalFinish,
            sweepRespGhostFinish,
            hleft.1, if_pos h1]
        let next :=
          sweepRespMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let bit := tokenBitBool t
        let r1 := sweepRespOneResponder r bit
        have hb :=
          sweepRespGhostMoveToken_bumpTo_move
            (n := n) (psi := psi) (kappa := kappa)
            kind baseR
            (sourceSet kind l none)
            (sourceSet kind r1 (some next))
            next gl
            (sweepRespSourceSet_token
              kind r1 (some next))
            ((sweepRespSourceSet_dist
                kind r1 (some next)).trans
              ((sweepRespOneResponder_dist
                  r bit).trans hRdist))
        simpa only [next, bit, r1] using hb.1
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [sweepRespPhysicalFinish,
              sweepRespGhostFinish,
              hleft.1,
              if_neg h1, dif_pos h2]
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            sweepRespMkToken
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
            sweepRespGhostMoveToken_bumpTo_move
              (n := n) (psi := psi) (kappa := kappa)
              kind baseR
              (sourceSet kind l none)
              (sourceSet kind r (some next))
              next gl
              (sweepRespSourceSet_token
                kind r (some next))
              ((sweepRespSourceSet_dist
                  kind r (some next)).trans hRdist)
          simpa only [next] using hb.1
        · cases rv with
          | none =>
              simp only
                [sweepRespPhysicalFinish,
                  sweepRespGhostFinish,
                  hleft.1, hright.1,
                  if_neg h1, dif_neg h2]
              exact ⟨hleft.2, hright.2⟩
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi
                      (tokenCode tr) = -1
              · simp only
                  [sweepRespPhysicalFinish,
                    sweepRespGhostFinish,
                    hleft.1, hright.1,
                    if_neg h1, dif_neg h2,
                    if_pos hm1]
                rw [hLid]
                let next :=
                  sweepRespNegTurnNext
                    hpsi baseL.id tr
                have hb :=
                  sweepRespGhostMoveToken_bumpTo_move
                    (n := n) (psi := psi) (kappa := kappa)
                    kind baseL
                    (sourceSet kind r none)
                    (sourceSet kind l (some next))
                    next gr
                    (sweepRespSourceSet_token
                      kind l (some next))
                    ((sweepRespSourceSet_dist
                        kind l (some next)).trans hLdist)
                simpa only [next] using hb.2
              · by_cases hm2 :
                  decodeOffset psi
                      (tokenCode tr) <= -2
                · simp only
                    [sweepRespPhysicalFinish,
                      sweepRespGhostFinish,
                      hleft.1, hright.1,
                      if_neg h1, dif_neg h2,
                      if_neg hm1, dif_pos hm2]
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    sweepRespMkToken
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
                    sweepRespGhostMoveToken_bumpTo_move
                      (n := n) (psi := psi) (kappa := kappa)
                      kind baseL
                      (sourceSet kind r none)
                      (sourceSet kind l (some next))
                      next gr
                      (sweepRespSourceSet_token
                        kind l (some next))
                      ((sweepRespSourceSet_dist
                          kind l (some next)).trans hLdist)
                  simpa only [next] using hb.2
                · simp only
                    [sweepRespPhysicalFinish,
                      sweepRespGhostFinish,
                      hleft.1, hright.1,
                      if_neg h1, dif_neg h2,
                      if_neg hm1, dif_neg hm2]
                  exact ⟨hleft.2, hright.2⟩
  | none =>
      cases rv with
      | none =>
          simp only
            [sweepRespPhysicalFinish,
              sweepRespGhostFinish,
              hleft.1, hright.1]
          exact ⟨hleft.2, hright.2⟩
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [sweepRespPhysicalFinish,
                sweepRespGhostFinish,
                hleft.1, hright.1,
                if_pos hm1]
            rw [hLid]
            let next :=
              sweepRespNegTurnNext
                hpsi baseL.id tr
            have hb :=
              sweepRespGhostMoveToken_bumpTo_move
                (n := n) (psi := psi) (kappa := kappa)
                kind baseL
                (sourceSet kind r none)
                (sourceSet kind l (some next))
                next gr
                (sweepRespSourceSet_token
                  kind l (some next))
                ((sweepRespSourceSet_dist
                    kind l (some next)).trans hLdist)
            simpa only [next] using hb.2
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [sweepRespPhysicalFinish,
                  sweepRespGhostFinish,
                  hleft.1, hright.1,
                  if_neg hm1, dif_pos hm2]
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                sweepRespMkToken
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
                sweepRespGhostMoveToken_bumpTo_move
                  (n := n) (psi := psi) (kappa := kappa)
                  kind baseL
                  (sourceSet kind r none)
                  (sourceSet kind l (some next))
                  next gr
                  (sweepRespSourceSet_token
                    kind l (some next))
                  ((sweepRespSourceSet_dist
                      kind l (some next)).trans hLdist)
              simpa only [next] using hb.2
            · simp only
                [sweepRespPhysicalFinish,
                  sweepRespGhostFinish,
                  hleft.1, hright.1,
                  if_neg hm1, dif_neg hm2]
              exact ⟨hleft.2, hright.2⟩




private theorem sweepRespGhostMoveToken_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    let q := moveToken hpsi kind l r
    let g :=
      sweepRespGhostMoveToken
        hpsi kind step site l r gl gr
    And
      (SweepRespOptionSound kind q.1 g.left)
      (SweepRespOptionSound kind q.2 g.right) := by
  classical
  dsimp only
  rw [← sweepRespMoveToken_eq hpsi kind l r]


  let l0 := sourceClear kind l
  let r0 := sourceClear kind r
  let lv0 := sweepRespLiveValue kind l
  let rv0 := sweepRespLiveValue kind r
  let gl0 := sweepRespLiveShadow kind l gl
  let gr0 := sweepRespLiveShadow kind r gr


  have hL0 :
      SweepRespAlignedSound
        kind l0 lv0 gl0 := by
    simpa only [l0, lv0, gl0] using
      sweepRespLiveShadow_aligned
        kind l gl
  have hR0 :
      SweepRespAlignedSound
        kind r0 rv0 gr0 := by
    simpa only [r0, rv0, gr0] using
      sweepRespLiveShadow_aligned
        kind r gr
  have hL0fields :=
    sweepRespSourceClear_fields kind l
  have hR0fields :=
    sweepRespSourceClear_fields kind r
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
      sweepRespBirthGhost
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
        SweepRespAlignedSound
          kind l1 lv1 gl1 := by
      by_cases hbirth : hb
      · have hdist0 :
            l0.dist.val = tokenD' psi kind := by
          have hval :=
            congrArg Fin.val hL0dist
          exact hval.trans hbirth.1
        have hpair :=
          sweepRespGhostMoveToken_birthGhost
            hpsi kind step site l.id
            l0 r gr hdist0
        simp only
          [l1, lv1, gl1, if_pos hbirth]
        exact
          And.intro
            (sweepRespSourceSet_token
              kind l0 (some birth.value))
            hpair.1
      · simpa only
          [l1, lv1, gl1, if_neg hbirth]
          using hL0


    have hL1dist : l1.dist = l.dist := by
      by_cases hbirth : hb
      · simp only [l1, if_pos hbirth]
        exact
          (sweepRespSourceSet_dist
            kind l0 (some birth.value)).trans
            hL0dist
      · simpa only [l1, if_neg hbirth]
          using hL0dist


    have hL1id : l1.id = l.id := by
      by_cases hbirth : hb
      · simp only [l1, if_pos hbirth]
        exact
          (sweepRespSourceSet_id
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
        SweepRespAlignedSound
          kind l2 lv2 gl2 := by
      by_cases hcol : collide
      · simp only
          [l2, lv2, gl2, if_pos hcol]
        exact
          And.intro
            (sweepRespSourceSet_token
              kind l1 none)
            (sweepRespOptionSound_none
              kind (sourceSet kind l1 none))
      · simpa only
          [l2, lv2, gl2, if_neg hcol]
          using hL1


    have hL2dist : l2.dist = l.dist := by
      by_cases hcol : collide
      · simp only [l2, if_pos hcol]
        exact
          (sweepRespSourceSet_dist
            kind l1 none).trans hL1dist
      · simpa only [l2, if_neg hcol]
          using hL1dist


    have hL2id : l2.id = l.id := by
      by_cases hcol : collide
      · simp only [l2, if_pos hcol]
        exact
          (sweepRespSourceSet_id
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
        sweepRespMoveToken hpsi kind l r =
          sweepRespPhysicalFinish
            hpsi kind l2 r0 := by
      by_cases hbirth : hb
      · have hbirth0 :=
          hBirthPhysIff.mpr hbirth
        by_cases hcol : collide
        · have hcol0 :=
            hCollPhysIff.mpr hcol
          simp only
            [l1, l0, r0, birth,
              sweepRespBirthGhost,
              if_pos hbirth] at hcol0
          unfold sweepRespMoveToken
            sweepRespPhysicalFinish
            sweepRespOneResponder
          rw [if_pos hlast0, if_pos hbirth0]
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
              sweepRespBirthGhost,
              if_pos hbirth] at hcol0
          unfold sweepRespMoveToken
            sweepRespPhysicalFinish
            sweepRespOneResponder
          rw [if_pos hlast0, if_pos hbirth0]
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
          unfold sweepRespMoveToken
            sweepRespPhysicalFinish
            sweepRespOneResponder
          rw [if_pos hlast0, if_neg hbirth0]
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
          unfold sweepRespMoveToken
            sweepRespPhysicalFinish
            sweepRespOneResponder
          rw [if_pos hlast0, if_neg hbirth0]
          simp only [if_neg hcol0]
          try simp only
            [l2, l1, if_neg hcol,
              if_neg hbirth] <;> rfl


    have hghost :
        sweepRespGhostMoveToken
            hpsi kind step site l r gl gr =
          sweepRespGhostFinish
            hpsi kind l r lv2 rv0 gl2 gr0 := by
      unfold sweepRespGhostMoveToken
        sweepRespGhostFinish
      rw [if_pos hlast] <;> rfl


    have hfinish :=
      sweepRespGhostMoveToken_finish_sound
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
        sweepRespMoveToken hpsi kind l r =
          (l0, r0) := by
      unfold sweepRespMoveToken
      rw [if_neg hlast0] <;> rfl
    have hghost :
        sweepRespGhostMoveToken
            hpsi kind step site l r gl gr =
          ⟨gl0, gr0, []⟩ := by
      unfold sweepRespGhostMoveToken
      rw [if_neg hlast] <;> rfl
    have hstay :=
      sweepRespGhostMoveToken_liveShadow_stay
        kind l r gl gr
    rw [hphys, hghost]
    simpa only [l0, r0, gl0, gr0]
      using hstay


private theorem sweepRespGhostMove_valueSound
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    (∀ z' : GhostToken n psi,
      (sweepRespGhostMoveToken
          hpsi kind step site l r gl gr).left =
        some z' →
      tokenAt kind
          (moveToken hpsi kind l r).1 =
        some z'.value) ∧
    (∀ z' : GhostToken n psi,
      (sweepRespGhostMoveToken
          hpsi kind step site l r gl gr).right =
        some z' →
      tokenAt kind
          (moveToken hpsi kind l r).2 =
        some z'.value) := by
  have hs :=
    sweepRespGhostMoveToken_sound
      hpsi kind step site l r gl gr
  dsimp only at hs
  constructor
  · intro z' hpost
    exact (hs.1 z' hpost).1
  · intro z' hpost
    exact (hs.2 z' hpost).1
private theorem sweepRespSameId_liveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      sweepRespLiveShadow kind q g = some z') :
    ∃ z0 : GhostToken n psi,
      g = some z0 ∧ z' = z0 := by
  cases hg : g with
  | none =>
      have hbad :
          (none : Option (GhostToken n psi)) =
            some z' := by
        simpa [sweepRespLiveShadow, hg] using hpost
      cases hbad
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          have hbad :
              (none : Option (GhostToken n psi)) =
                some z' := by
            simpa [sweepRespLiveShadow, hg, ht] using hpost
          cases hbad
      | some t =>
          by_cases hkeep :
              z0.value = t ∧
                sweepRespLocalValid kind q t
          · have hsome :
                some z0 = some z' := by
              simpa
                [sweepRespLiveShadow, hg, ht,
                  if_pos hkeep]
                using hpost
            have hz : z0 = z' :=
              Option.some.inj hsome
            exact ⟨z0, rfl, hz.symm⟩
          · have hbad :
                (none : Option (GhostToken n psi)) =
                  some z' := by
              simpa
                [sweepRespLiveShadow, hg, ht,
                  if_neg hkeep]
                using hpost
            cases hbad


private theorem sweepRespSameId_liveShadow_oldResponder
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (z z' : GhostToken n psi)
    (hpost :
      sweepRespLiveShadow kind q (some z) =
        some z') :
    z' = z ∧
      sweepRespLiveValue kind q = some z.value ∧
      sweepRespLocalValid kind q z.value := by
  cases ht : tokenAt kind q with
  | none =>
      have hbad :
          (none : Option (GhostToken n psi)) =
            some z' := by
        simpa
          [sweepRespLiveShadow, ht]
          using hpost
      cases hbad
  | some t =>
      by_cases hkeep :
          z.value = t ∧
            sweepRespLocalValid kind q t
      · have hsome :
            some z = some z' := by
          simpa
            [sweepRespLiveShadow, ht,
              if_pos hkeep]
            using hpost
        have hz : z = z' :=
          Option.some.inj hsome
        have hlive :
            sweepRespLiveValue kind q =
              some z.value := by
          unfold sweepRespLiveValue
          rw [ht]
          dsimp only
          rw [if_pos hkeep.2]
          exact congrArg some hkeep.1.symm
        have hvalid :
            sweepRespLocalValid kind q z.value := by
          rw [hkeep.1]
          exact hkeep.2
        exact ⟨hz.symm, hlive, hvalid⟩
      · have hbad :
            (none : Option (GhostToken n psi)) =
              some z' := by
          simpa
            [sweepRespLiveShadow, ht,
              if_neg hkeep]
            using hpost
        cases hbad


private theorem sweepRespSameId_bump_live_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (next : TokenData psi)
    (g : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hpost :
      (sweepRespBumpTo kind qDest next g).live =
        some z') :
    ∃ z0 : GhostToken n psi,
      g = some z0 ∧
      z'.lmeta = ghostStepLineageAdvance z0.lmeta ∧
      z'.value = next := by
  cases hg : g with
  | none =>
      have hbad :
          (none : Option (GhostToken n psi)) =
            some z' := by
        simpa [sweepRespBumpTo, hg] using hpost
      cases hbad
  | some z0 =>
      by_cases hv :
          sweepRespLocalValid kind qDest next
      · have hsome :
            some
                ({ value := next
                   lmeta :=
                     ghostStepLineageAdvance z0.lmeta } :
                  GhostToken n psi) =
              some z' := by
          simpa
            [sweepRespBumpTo, hg, if_pos hv]
            using hpost
        have hz :
            ({ value := next
               lmeta :=
                 ghostStepLineageAdvance z0.lmeta } :
              GhostToken n psi) = z' :=
          Option.some.inj hsome
        subst z'
        exact ⟨z0, rfl, rfl, rfl⟩
      · have hbad :
            (none : Option (GhostToken n psi)) =
              some z' := by
          simpa
            [sweepRespBumpTo, hg, if_neg hv]
            using hpost
        cases hbad


private theorem sweepRespSameId_advance_id
    {n : Nat}
    (m : LineageMeta n) :
    (ghostStepLineageAdvance m).id = m.id := by
  rfl


private theorem sweepRespSameId_negTurn_decode
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (sweepRespNegTurnNext hpsi sourceBit t)) =
      ((psi : Nat) : Int) := by
  unfold sweepRespNegTurnNext
  by_cases hc : t.2 = (1 : Fin 2)
  · rw [if_pos hc]
    simpa [sweepRespMkToken, tokenCode]
      using decodeOffset_psi psi hpsi
  · rw [if_neg hc]
    simpa [sweepRespMkToken, tokenCode]
      using decodeOffset_psi psi hpsi


private structure SweepRespSameIdPrep
    (n psi : Nat) where
  lv : Option (TokenData psi)
  rv : Option (TokenData psi)
  gl : Option (GhostToken n psi)
  gr : Option (GhostToken n psi)


private def sweepRespSameIdPrep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    SweepRespSameIdPrep n psi :=
  let lv0 := sweepRespLiveValue kind l
  let rv0 := sweepRespLiveValue kind r
  let gl0 := sweepRespLiveShadow kind l gl
  let gr0 := sweepRespLiveShadow kind r gr
  let hb :=
    l.dist.val = tokenD' psi kind ∧ lv0 = none
  let birth :=
    sweepRespBirthGhost hpsi kind step site l.id
  let lv1 :=
    if hb then some birth.value else lv0
  let gl1 :=
    if hb then some birth else gl0
  let collide := lv1 ≠ none ∧ rv0 ≠ none
  { lv := if collide then none else lv1
    rv := rv0
    gl := if collide then none else gl1
    gr := gr0 }


private theorem sweepRespSameIdPrep_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    (sweepRespSameIdPrep
        hpsi kind step site l r gl gr).rv =
        sweepRespLiveValue kind r ∧
      (sweepRespSameIdPrep
        hpsi kind step site l r gl gr).gr =
        sweepRespLiveShadow kind r gr := by
  exact ⟨rfl, rfl⟩


private theorem sweepRespSameIdPrep_left_id_ne
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step) :
    ∀ u : GhostToken n psi,
      (sweepRespSameIdPrep
          hpsi kind step site l r gl (some z)).gl =
        some u →
      u.lmeta.id ≠ z.lmeta.id := by
  intro u hu
  cases hlv : sweepRespLiveValue kind l with
  | none =>
      by_cases hdist :
          l.dist.val = tokenD' psi kind
      · cases hrv : sweepRespLiveValue kind r with
        | none =>
            have hsome :
                some
                    (sweepRespBirthGhost
                      hpsi kind step site l.id) =
                  some u := by
              simpa
                [sweepRespSameIdPrep, hlv, hdist, hrv]
                using hu
            have hub :
                sweepRespBirthGhost
                    hpsi kind step site l.id =
                  u :=
              Option.some.inj hsome
            subst u
            intro huid
            apply hNotFresh
            have hrev :
                z.lmeta.id =
                  (sweepRespBirthGhost
                    hpsi kind step site l.id).lmeta.id :=
              huid.symm
            simpa [sweepRespBirthGhost] using hrev
        | some tr =>
            have hbad : False := by
              simpa
                [sweepRespSameIdPrep, hlv, hdist, hrv]
                using hu
            exact False.elim hbad
      · have hshadow :
            sweepRespLiveShadow kind l gl =
              some u := by
          simpa
            [sweepRespSameIdPrep, hlv, hdist]
            using hu
        obtain ⟨u0, hgl, hu0⟩ :=
          sweepRespSameId_liveShadow_source
            kind l gl u hshadow
        rw [hu0]
        exact hNoLeft u0 hgl
  | some tl =>
      cases hrv : sweepRespLiveValue kind r with
      | none =>
          have hshadow :
              sweepRespLiveShadow kind l gl =
                some u := by
            simpa
              [sweepRespSameIdPrep, hlv, hrv]
              using hu
          obtain ⟨u0, hgl, hu0⟩ :=
            sweepRespSameId_liveShadow_source
              kind l gl u hshadow
          rw [hu0]
          exact hNoLeft u0 hgl
      | some tr =>
          have hbad : False := by
            simpa
              [sweepRespSameIdPrep, hlv, hrv]
              using hu
          exact False.elim hbad


private theorem sweepRespSameId_gate_eq_finish
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgate :
      l.last = false ∧ r.last = false) :
    sweepRespGhostMoveToken
        hpsi kind step site l r gl gr =
      sweepRespGhostFinish
        hpsi kind l r
        (sweepRespSameIdPrep
          hpsi kind step site l r gl gr).lv
        (sweepRespSameIdPrep
          hpsi kind step site l r gl gr).rv
        (sweepRespSameIdPrep
          hpsi kind step site l r gl gr).gl
        (sweepRespSameIdPrep
          hpsi kind step site l r gl gr).gr := by
  unfold sweepRespGhostMoveToken
    sweepRespSameIdPrep
  rw [if_pos hgate]
  rfl


private theorem sweepRespSameId_gate_closed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgate :
      ¬ (l.last = false ∧ r.last = false)) :
    sweepRespGhostMoveToken
        hpsi kind step site l r gl gr =
      ⟨sweepRespLiveShadow kind l gl,
        sweepRespLiveShadow kind r gr, []⟩ := by
  unfold sweepRespGhostMoveToken
  rw [if_neg hgate]


private def sweepRespSameIdMoveLeft
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match rv with
  | none =>
      ⟨gl, gr, []⟩
  | some tr =>
      let cr := decodeOffset psi (tokenCode tr)
      if cr = -1 then
        let next :=
          sweepRespNegTurnNext hpsi baseL.id tr
        let b :=
          sweepRespBumpTo kind baseL next gr
        ⟨b.live, none, b.done⟩
      else if hm2 : cr ≤ -2 then
        have hc : ValidOffset psi cr :=
          decodeOffset_valid
            psi (by omega) (tokenCode tr)
        let next :=
          sweepRespMkToken
            (encodeOffset psi (cr + 1) (by
              rcases hc with hn | hp
              · left
                omega
              · exfalso
                omega))
            tr.1.2 tr.2
        let b :=
          sweepRespBumpTo kind baseL next gr
        ⟨b.live, none, b.done⟩
      else
        ⟨gl, gr, []⟩


private theorem sweepRespSameIdMoveLeft_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    sweepRespSameIdMoveLeft
        hpsi kind baseL none gl gr =
      ⟨gl, gr, []⟩ := by
  rfl


private theorem sweepRespSameIdMoveLeft_negTurn_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hneg :
      decodeOffset psi (tokenCode tr) = -1) :
    (sweepRespSameIdMoveLeft
        hpsi kind baseL (some tr) gl gr).right =
      none := by
  unfold sweepRespSameIdMoveLeft
  dsimp only
  rw [if_pos hneg]


private theorem sweepRespSameIdMoveLeft_negTurn_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hneg :
      decodeOffset psi (tokenCode tr) = -1)
    (hpost :
      (sweepRespSameIdMoveLeft
          hpsi kind baseL (some tr) gl gr).left =
        some z') :
    ∃ u : GhostToken n psi,
      gr = some u ∧
      z'.lmeta = ghostStepLineageAdvance u.lmeta ∧
      decodeOffset psi (tokenCode z'.value) =
        ((psi : Nat) : Int) := by
  unfold sweepRespSameIdMoveLeft at hpost
  dsimp only at hpost
  rw [if_pos hneg] at hpost
  dsimp only at hpost
  obtain ⟨u, hgr, hmeta, hvalue⟩ :=
    sweepRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseL)
      (g := gr)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgr, hmeta, ?_⟩
  rw [hvalue]
  exact
    sweepRespSameId_negTurn_decode
      hpsi baseL.id tr


private theorem sweepRespSameIdMoveLeft_negative_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hnot :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hneg :
      decodeOffset psi (tokenCode tr) ≤ -2) :
    (sweepRespSameIdMoveLeft
        hpsi kind baseL (some tr) gl gr).right =
      none := by
  unfold sweepRespSameIdMoveLeft
  dsimp only
  rw [if_neg hnot, dif_pos hneg]


private theorem sweepRespSameIdMoveLeft_negative_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hnot :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hneg :
      decodeOffset psi (tokenCode tr) ≤ -2)
    (hpost :
      (sweepRespSameIdMoveLeft
          hpsi kind baseL (some tr) gl gr).left =
        some z') :
    ∃ u : GhostToken n psi,
      gr = some u ∧
      z'.lmeta = ghostStepLineageAdvance u.lmeta ∧
      decodeOffset psi (tokenCode z'.value) =
        decodeOffset psi (tokenCode tr) + 1 := by
  unfold sweepRespSameIdMoveLeft at hpost
  dsimp only at hpost
  rw [if_neg hnot, dif_pos hneg] at hpost
  dsimp only at hpost
  obtain ⟨u, hgr, hmeta, hvalue⟩ :=
    sweepRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseL)
      (g := gr)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgr, hmeta, ?_⟩
  rw [hvalue]
  simp only
    [sweepRespMkToken, tokenCode, decode_encode]


private theorem sweepRespSameIdMoveLeft_stay
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hnot :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hnotNeg :
      ¬ decodeOffset psi (tokenCode tr) ≤ -2) :
    sweepRespSameIdMoveLeft
        hpsi kind baseL (some tr) gl gr =
      ⟨gl, gr, []⟩ := by
  unfold sweepRespSameIdMoveLeft
  dsimp only
  rw [if_neg hnot, dif_neg hnotNeg]


private theorem sweepRespSameIdFinish_none
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) :
    sweepRespGhostFinish
        hpsi kind baseL baseR none rv gl gr =
      sweepRespSameIdMoveLeft
        hpsi kind baseL rv gl gr := by
  rfl


private theorem sweepRespSameIdFinish_posOne_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 :
      decodeOffset psi (tokenCode t) = 1) :
    (sweepRespGhostFinish
        hpsi kind baseL baseR
        (some t) rv gl gr).left = none := by
  unfold sweepRespGhostFinish
  dsimp only
  rw [if_pos h1]


private theorem sweepRespSameIdFinish_posOne_right_source
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (h1 :
      decodeOffset psi (tokenCode t) = 1)
    (hpost :
      (sweepRespGhostFinish
          hpsi kind baseL baseR
          (some t) rv gl gr).right =
        some z') :
    ∃ u : GhostToken n psi,
      gl = some u ∧ z'.lmeta.id = u.lmeta.id := by
  unfold sweepRespGhostFinish at hpost
  dsimp only at hpost
  rw [if_pos h1] at hpost
  dsimp only at hpost
  obtain ⟨u, hgl, hmeta, _hvalue⟩ :=
    sweepRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseR)
      (g := gl)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgl, ?_⟩
  have hm :=
    congrArg (fun m : LineageMeta n => m.id) hmeta
  simpa [ghostStepLineageAdvance] using hm


private theorem sweepRespSameIdFinish_positive_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      2 ≤ decodeOffset psi (tokenCode t)) :
    (sweepRespGhostFinish
        hpsi kind baseL baseR
        (some t) rv gl gr).left = none := by
  unfold sweepRespGhostFinish
  dsimp only
  rw [if_neg h1, dif_pos h2]


private theorem sweepRespSameIdFinish_positive_right_source
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      2 ≤ decodeOffset psi (tokenCode t))
    (hpost :
      (sweepRespGhostFinish
          hpsi kind baseL baseR
          (some t) rv gl gr).right =
        some z') :
    ∃ u : GhostToken n psi,
      gl = some u ∧ z'.lmeta.id = u.lmeta.id := by
  unfold sweepRespGhostFinish at hpost
  dsimp only at hpost
  rw [if_neg h1, dif_pos h2] at hpost
  dsimp only at hpost
  obtain ⟨u, hgl, hmeta, _hvalue⟩ :=
    sweepRespSameId_bump_live_source
      (kind := kind)
      (qDest := baseR)
      (g := gl)
      (z' := z')
      (next := _) hpost
  refine ⟨u, hgl, ?_⟩
  have hm :=
    congrArg (fun m : LineageMeta n => m.id) hmeta
  simpa [ghostStepLineageAdvance] using hm


private theorem sweepRespSameIdFinish_neutral
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 ≤ decodeOffset psi (tokenCode t)) :
    sweepRespGhostFinish
        hpsi kind baseL baseR
        (some t) rv gl gr =
      sweepRespSameIdMoveLeft
        hpsi kind baseL rv gl gr := by
  unfold sweepRespGhostFinish
  dsimp only
  rw [if_neg h1, dif_neg h2]
  rfl


private theorem sweepRespSameIdMoveLeft_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (rv : Option (TokenData psi))
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hrv :
      rv = sweepRespLiveValue kind baseR)
    (hpost :
      (sweepRespSameIdMoveLeft
          hpsi kind baseL rv gl
          (sweepRespLiveShadow kind baseR (some z))).right =
        some z') :
    z' = z ∧
      0 < decodeOffset psi (tokenCode z.value) := by
  cases hrvCase : rv with
  | none =>
      rw [hrvCase] at hpost
      rw [sweepRespSameIdMoveLeft_none] at hpost
      have hs :=
        sweepRespSameId_liveShadow_oldResponder
          kind baseR z z' hpost
      have hnone :
          (none : Option (TokenData psi)) =
            some z.value :=
        hrvCase.symm.trans (hrv.trans hs.2.1)
      cases hnone
  | some tr =>
      rw [hrvCase] at hpost
      by_cases hm1 :
          decodeOffset psi (tokenCode tr) = -1
      · have hnone :=
          sweepRespSameIdMoveLeft_negTurn_right
            hpsi kind baseL tr gl
            (sweepRespLiveShadow kind baseR (some z))
            hm1
        rw [hnone] at hpost
        cases hpost
      · by_cases hm2 :
          decodeOffset psi (tokenCode tr) ≤ -2
        · have hnone :=
            sweepRespSameIdMoveLeft_negative_right
              hpsi kind baseL tr gl
              (sweepRespLiveShadow kind baseR (some z))
              hm1 hm2
          rw [hnone] at hpost
          cases hpost
        · have hstay :=
            sweepRespSameIdMoveLeft_stay
              hpsi kind baseL tr gl
              (sweepRespLiveShadow kind baseR (some z))
              hm1 hm2
          rw [hstay] at hpost
          have hs :=
            sweepRespSameId_liveShadow_oldResponder
              kind baseR z z' hpost
          have htr :
              tr = z.value := by
            have hsome :
                some tr = some z.value :=
              hrvCase.symm.trans (hrv.trans hs.2.1)
            exact Option.some.inj hsome
          have hvalid := hs.2.2
          unfold sweepRespLocalValid at hvalid
          dsimp only at hvalid
          rcases hvalid with hp | hn
          · exact ⟨hs.1, hp.1⟩
          · rw [htr] at hm1 hm2
            omega


private theorem sweepRespSameIdMoveLeft_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (rv : Option (TokenData psi))
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hLeftNoId :
      ∀ u : GhostToken n psi,
        gl = some u →
        u.lmeta.id ≠ z.lmeta.id)
    (hrv :
      rv = sweepRespLiveValue kind baseR)
    (hpost :
      (sweepRespSameIdMoveLeft
          hpsi kind baseL rv gl
          (sweepRespLiveShadow kind baseR (some z))).left =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z'.lmeta = ghostStepLineageAdvance z.lmeta ∧
      ((decodeOffset psi (tokenCode z.value) = -1 ∧
          decodeOffset psi (tokenCode z'.value) =
            ((psi : Nat) : Int)) ∨
        (decodeOffset psi (tokenCode z.value) ≤ -2 ∧
          decodeOffset psi (tokenCode z'.value) =
            decodeOffset psi (tokenCode z.value) + 1)) := by
  cases hrvCase : rv with
  | none =>
      rw [hrvCase] at hpost
      rw [sweepRespSameIdMoveLeft_none] at hpost
      exact False.elim ((hLeftNoId z' hpost) hid)
  | some tr =>
      rw [hrvCase] at hpost
      by_cases hm1 :
          decodeOffset psi (tokenCode tr) = -1
      · obtain ⟨u, hshadow, hmeta, hnew⟩ :=
          sweepRespSameIdMoveLeft_negTurn_left
            hpsi kind baseL tr gl
            (sweepRespLiveShadow kind baseR (some z))
            z' hm1
            (by simpa [hrvCase] using hpost)
        have hs :=
          sweepRespSameId_liveShadow_oldResponder
            kind baseR z u hshadow
        rw [hs.1] at hmeta
        have htr :
            tr = z.value := by
          have hsome :
              some tr = some z.value :=
            hrvCase.symm.trans (hrv.trans hs.2.1)
          exact Option.some.inj hsome
        have hold :
            decodeOffset psi (tokenCode z.value) = -1 := by
          simpa [htr] using hm1
        exact ⟨hmeta, Or.inl ⟨hold, hnew⟩⟩
      · by_cases hm2 :
          decodeOffset psi (tokenCode tr) ≤ -2
        · obtain ⟨u, hshadow, hmeta, hnew⟩ :=
            sweepRespSameIdMoveLeft_negative_left
              hpsi kind baseL tr gl
              (sweepRespLiveShadow kind baseR (some z))
              z' hm1 hm2
              (by simpa [hrvCase] using hpost)
          have hs :=
            sweepRespSameId_liveShadow_oldResponder
              kind baseR z u hshadow
          rw [hs.1] at hmeta
          have htr :
              tr = z.value := by
            have hsome :
                some tr = some z.value :=
              hrvCase.symm.trans (hrv.trans hs.2.1)
            exact Option.some.inj hsome
          have hold :
              decodeOffset psi (tokenCode z.value) ≤ -2 := by
            simpa [htr] using hm2
          have hnew' :
              decodeOffset psi (tokenCode z'.value) =
                decodeOffset psi (tokenCode z.value) + 1 := by
            simpa [htr] using hnew
          exact ⟨hmeta, Or.inr ⟨hold, hnew'⟩⟩
        · have hstay :=
            sweepRespSameIdMoveLeft_stay
              hpsi kind baseL tr gl
              (sweepRespLiveShadow kind baseR (some z))
              hm1 hm2
          have hgl :
              gl = some z' := by
            simpa [hrvCase, hstay] using hpost
          exact False.elim ((hLeftNoId z' hgl) hid)


private theorem sweepRespSameIdFinish_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hLeftNoId :
      ∀ u : GhostToken n psi,
        gl = some u →
        u.lmeta.id ≠ z.lmeta.id)
    (hrv :
      rv = sweepRespLiveValue kind baseR)
    (hgr :
      gr = sweepRespLiveShadow kind baseR (some z))
    (hpost :
      (sweepRespGhostFinish
          hpsi kind baseL baseR lv rv gl gr).right =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z' = z ∧
      0 < decodeOffset psi (tokenCode z.value) := by
  rw [hgr] at hpost
  cases hlv : lv with
  | none =>
      rw [hlv] at hpost
      rw [sweepRespSameIdFinish_none] at hpost
      exact
        sweepRespSameIdMoveLeft_right
          hpsi kind baseL baseR rv gl
          z z' hrv hpost
  | some t =>
      rw [hlv] at hpost
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · obtain ⟨u, hgu, huid⟩ :=
          sweepRespSameIdFinish_posOne_right_source
            hpsi kind baseL baseR t rv gl
            (sweepRespLiveShadow kind baseR (some z))
            z' h1
            (by simpa [hlv] using hpost)
        have huz :
            u.lmeta.id = z.lmeta.id :=
          huid.symm.trans hid
        exact False.elim ((hLeftNoId u hgu) huz)
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · obtain ⟨u, hgu, huid⟩ :=
            sweepRespSameIdFinish_positive_right_source
              hpsi kind baseL baseR t rv gl
              (sweepRespLiveShadow kind baseR (some z))
              z' h1 h2
              (by simpa [hlv] using hpost)
          have huz :
              u.lmeta.id = z.lmeta.id :=
            huid.symm.trans hid
          exact False.elim ((hLeftNoId u hgu) huz)
        · have hneutral :=
            sweepRespSameIdFinish_neutral
              hpsi kind baseL baseR t rv gl
              (sweepRespLiveShadow kind baseR (some z))
              h1 h2
          have hm :
              (sweepRespSameIdMoveLeft
                  hpsi kind baseL rv gl
                  (sweepRespLiveShadow kind baseR (some z))).right =
                some z' := by
            simpa [hlv, hneutral] using hpost
          exact
            sweepRespSameIdMoveLeft_right
              hpsi kind baseL baseR rv gl
              z z' hrv hm


private theorem sweepRespSameIdFinish_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hLeftNoId :
      ∀ u : GhostToken n psi,
        gl = some u →
        u.lmeta.id ≠ z.lmeta.id)
    (hrv :
      rv = sweepRespLiveValue kind baseR)
    (hgr :
      gr = sweepRespLiveShadow kind baseR (some z))
    (hpost :
      (sweepRespGhostFinish
          hpsi kind baseL baseR lv rv gl gr).left =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z'.lmeta = ghostStepLineageAdvance z.lmeta ∧
      ((decodeOffset psi (tokenCode z.value) = -1 ∧
          decodeOffset psi (tokenCode z'.value) =
            ((psi : Nat) : Int)) ∨
        (decodeOffset psi (tokenCode z.value) ≤ -2 ∧
          decodeOffset psi (tokenCode z'.value) =
            decodeOffset psi (tokenCode z.value) + 1)) := by
  rw [hgr] at hpost
  cases hlv : lv with
  | none =>
      rw [hlv] at hpost
      rw [sweepRespSameIdFinish_none] at hpost
      exact
        sweepRespSameIdMoveLeft_left
          hpsi kind baseL baseR rv gl
          z z' hLeftNoId hrv hpost hid
  | some t =>
      rw [hlv] at hpost
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · have hnone :=
          sweepRespSameIdFinish_posOne_left
            hpsi kind baseL baseR t rv gl
            (sweepRespLiveShadow kind baseR (some z))
            h1
        rw [hnone] at hpost
        cases hpost
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · have hnone :=
            sweepRespSameIdFinish_positive_left
              hpsi kind baseL baseR t rv gl
              (sweepRespLiveShadow kind baseR (some z))
              h1 h2
          rw [hnone] at hpost
          cases hpost
        · have hneutral :=
            sweepRespSameIdFinish_neutral
              hpsi kind baseL baseR t rv gl
              (sweepRespLiveShadow kind baseR (some z))
              h1 h2
          have hm :
              (sweepRespSameIdMoveLeft
                  hpsi kind baseL rv gl
                  (sweepRespLiveShadow kind baseR (some z))).left =
                some z' := by
            simpa [hlv, hneutral] using hpost
          exact
            sweepRespSameIdMoveLeft_left
              hpsi kind baseL baseR rv gl
              z z' hLeftNoId hrv hm hid


private theorem sweepRespRightSameId
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hpost :
      (sweepRespGhostMoveToken
          hpsi kind step site l r gl (some z)).right =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z' = z := by
  classical
  by_cases hgate :
      l.last = false ∧ r.last = false
  · have hnorm :=
      sweepRespSameId_gate_eq_finish
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    let P :=
      sweepRespSameIdPrep
        hpsi kind step site l r gl (some z)
    have hleft :
        ∀ u : GhostToken n psi,
          P.gl = some u →
          u.lmeta.id ≠ z.lmeta.id := by
      simpa [P] using
        sweepRespSameIdPrep_left_id_ne
          hpsi kind step site l r gl z
          hNoLeft hNotFresh
    have hright :=
      sweepRespSameIdPrep_right
        hpsi kind step site l r gl (some z)
    have hs :=
      sweepRespSameIdFinish_right
        hpsi kind l r
        P.lv P.rv P.gl P.gr z z'
        hleft
        (by simpa [P] using hright.1)
        (by simpa [P] using hright.2)
        (by simpa [P] using hpost)
        hid
    exact hs.1
  · have hnorm :=
      sweepRespSameId_gate_closed
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    exact
      (sweepRespSameId_liveShadow_oldResponder
        kind r z z' hpost).1


private theorem sweepRespRightSameId_positive_of_gate
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hgate :
      l.last = false ∧ r.last = false)
    (hpost :
      (sweepRespGhostMoveToken
          hpsi kind step site l r gl (some z)).right =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    0 < decodeOffset psi (tokenCode z.value) := by
  classical
  have hnorm :=
    sweepRespSameId_gate_eq_finish
      hpsi kind step site l r gl (some z) hgate
  rw [hnorm] at hpost
  let P :=
    sweepRespSameIdPrep
      hpsi kind step site l r gl (some z)
  have hleft :
      ∀ u : GhostToken n psi,
        P.gl = some u →
        u.lmeta.id ≠ z.lmeta.id := by
    simpa [P] using
      sweepRespSameIdPrep_left_id_ne
        hpsi kind step site l r gl z
        hNoLeft hNotFresh
  have hright :=
    sweepRespSameIdPrep_right
      hpsi kind step site l r gl (some z)
  exact
    (sweepRespSameIdFinish_right
      hpsi kind l r
      P.lv P.rv P.gl P.gr z z'
      hleft
      (by simpa [P] using hright.1)
      (by simpa [P] using hright.2)
      (by simpa [P] using hpost)
      hid).2


private theorem sweepRespLeftSameId
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z z' : GhostToken n psi)
    (hNoLeft :
      ∀ zl : GhostToken n psi,
        gl = some zl →
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hpost :
      (sweepRespGhostMoveToken
          hpsi kind step site l r gl (some z)).left =
        some z')
    (hid :
      z'.lmeta.id = z.lmeta.id) :
    z'.lmeta = ghostStepLineageAdvance z.lmeta ∧
      ((decodeOffset psi (tokenCode z.value) = -1 ∧
          decodeOffset psi (tokenCode z'.value) =
            ((psi : Nat) : Int)) ∨
        (decodeOffset psi (tokenCode z.value) ≤ -2 ∧
          decodeOffset psi (tokenCode z'.value) =
            decodeOffset psi (tokenCode z.value) + 1)) := by
  classical
  by_cases hgate :
      l.last = false ∧ r.last = false
  · have hnorm :=
      sweepRespSameId_gate_eq_finish
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    let P :=
      sweepRespSameIdPrep
        hpsi kind step site l r gl (some z)
    have hleft :
        ∀ u : GhostToken n psi,
          P.gl = some u →
          u.lmeta.id ≠ z.lmeta.id := by
      simpa [P] using
        sweepRespSameIdPrep_left_id_ne
          hpsi kind step site l r gl z
          hNoLeft hNotFresh
    have hright :=
      sweepRespSameIdPrep_right
        hpsi kind step site l r gl (some z)
    exact
      sweepRespSameIdFinish_left
        hpsi kind l r
        P.lv P.rv P.gl P.gr z z'
        hleft
        (by simpa [P] using hright.1)
        (by simpa [P] using hright.2)
        (by simpa [P] using hpost)
        hid
  · have hnorm :=
      sweepRespSameId_gate_closed
        hpsi kind step site l r gl (some z) hgate
    rw [hnorm] at hpost
    obtain ⟨u, hgl, hu⟩ :=
      sweepRespSameId_liveShadow_source
        kind l gl z' hpost
    rw [hu] at hid
    exact False.elim ((hNoLeft u hgl) hid)




/-! -----------------------------------------------------------------------
    Physical selected-token and last-field projections
------------------------------------------------------------------------ -/


private theorem sweepRespElimTokenLeft
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


private theorem sweepRespElimTokenRight
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


private theorem sweepRespWhitePreservesBlack
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


private theorem sweepRespPplTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := sweepRespSelectedInput hpsi kind l r
    tokenAt kind (ppl hpsi l r).1 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind (ppl hpsi l r).2 =
        tokenAt kind (moveToken hpsi kind p.1 p.2).2 := by
  cases kind with
  | black =>
      let p := sweepRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw :=
        sweepRespWhitePreservesBlack
          hpsi b.1 b.2
      have hel :=
        sweepRespElimTokenLeft .black w.1 w.2
      have her :=
        sweepRespElimTokenRight .black w.1 w.2
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
      let p := sweepRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hel :=
        sweepRespElimTokenLeft .white w.1 w.2
      have her :=
        sweepRespElimTokenRight .white w.1 w.2
      change
        tokenAt .white
            (eliminateLeaders w.1 w.2).1 =
              tokenAt .white w.1 ∧
          tokenAt .white
            (eliminateLeaders w.1 w.2).2 =
              tokenAt .white w.2
      exact ⟨hel, her⟩


private theorem sweepRespMoveTokenLast
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


private theorem sweepRespElimLast
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


private theorem sweepRespPplLastPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := sweepRespSelectedInput hpsi kind l r
    (ppl hpsi l r).1.last = p.1.last ∧
      (ppl hpsi l r).2.last = p.2.last := by
  cases kind with
  | black =>
      let p := sweepRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hb := sweepRespMoveTokenLast hpsi .black p.1 p.2
      have hw := sweepRespMoveTokenLast hpsi .white b.1 b.2
      have he := sweepRespElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            p.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            p.2.last
      exact
        ⟨he.1.trans (hw.1.trans hb.1),
          he.2.trans (hw.2.trans hb.2)⟩
  | white =>
      let p := sweepRespPrelude hpsi l r
      let b :=
        moveToken hpsi .black p.1 p.2
      let w :=
        moveToken hpsi .white b.1 b.2
      have hw := sweepRespMoveTokenLast hpsi .white b.1 b.2
      have he := sweepRespElimLast w.1 w.2
      change
        (eliminateLeaders w.1 w.2).1.last =
            b.1.last ∧
          (eliminateLeaders w.1 w.2).2.last =
            b.2.last
      exact
        ⟨he.1.trans hw.1,
          he.2.trans hw.2⟩


private theorem sweepRespGhostStepTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      sweepRespSelectedInput hpsi kind
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
    sweepRespPplTokenPair
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


private theorem sweepRespGhostStepTokenPairAt
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      sweepRespSelectedInput hpsi kind
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
    sweepRespGhostStepTokenPair
      hpsi ring G e kind hne


private theorem sweepRespGhostStepLastPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    let p :=
      sweepRespSelectedInput hpsi kind
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
    sweepRespPplLastPair
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


private theorem sweepRespCd_fit
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


private theorem sweepRespRightNeighbor_ne
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


private theorem sweepRespLeftNeighborRightNeighbor
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


private theorem sweepRespRightNeighborShiftRight
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


private theorem sweepRespGhostSound_token
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


private theorem sweepRespOwner_valid
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


private theorem sweepRespFirstNegativeTarget
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


private theorem sweepRespNegative_not_first
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
    sweepRespGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hvalid :=
    sweepRespOwner_valid
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
          rw [hx0, Nat.zero_add] at hrow
          first
          | exact hrow.trans (Nat.zero_mod _)
          | simpa using hrow
          | omega
      | white =>
          simp only [tokenD'] at hrow ⊢
          rw [hx0, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega)] at hrow
          exact hrow
    have ht :=
      sweepRespFirstNegativeTarget
        hpsi kind
        (G.phys (ring.rightNeighbor e))
        z.value hdist hneg
    omega


private theorem sweepRespPredecessorData
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
    sweepRespNegative_not_first
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
        sweepRespRightNeighborShiftRight
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
  rw [sweepRespLeftNeighborRightNeighbor,
    sweepRespLeftNeighborRightNeighbor] at he
  exact
    ⟨x, y, hx, he,
      by dsimp [y]; omega⟩


private theorem sweepRespCd_last_false
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


private theorem sweepRespCd_dist_same
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


private theorem sweepRespProgress_dist_eq
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


private theorem sweepRespValid_same_dist
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


private theorem sweepRespFresh_advance
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


private theorem sweepRespNegativeAbs
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
            first
            | exact Int.ofNat_zero_le m
            | exact Int.natCast_nonneg m
            | omega
          exfalso
          omega
      | negSucc m =>
          simp at hn ⊢
          omega
    · omega


private theorem sweepRespNegativeStep_target
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
          first
          | rfl
          | simp
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


private theorem sweepRespNegativeStep_valid
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


private theorem sweepRespNegativeStep_progress
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
    sweepRespNegativeAbs
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


private theorem sweepRespServiceEdge_negative
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
    (sweepRespLeftNeighborRightNeighbor
      ring e).symm


/-! -----------------------------------------------------------------------
    Main reduction
------------------------------------------------------------------------ -/


theorem lemma4SweepResponderSameIdBranch_of_negTurnRow
    (hturn : Lemma4SweepResponderNegTurnProgressRow) :
    Lemma4SweepResponderSameIdBranch := by
  unfold Lemma4SweepResponderSameIdBranch
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' _hcovered hsound huniq _hkin
  intro hwin howner hsame


  have hfit :
      2 * psi ≤ n :=
    sweepRespCd_fit
      hpsi ring k kind G.phys hCd
  have hn2 : 2 ≤ n := by
    omega
  have hne :
      ring.rightNeighbor e ≠ e :=
    sweepRespRightNeighbor_ne ring hn2 e


  let p :=
    sweepRespSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))


  have hpair :
      sweepRespSelectedPair
          hpsi ring step G e kind =
        ghostStepSelectedPair
          hpsi ring step G e kind :=
    sweepRespSelectedPair_eq_export
      hpsi ring step G e kind


  have htokStep :=
    sweepRespGhostStepTokenPairAt
      hpsi ring step G e kind hne


  have hlastStep :=
    sweepRespGhostStepLastPair
      hpsi ring step G e kind hne


  have hNoLeft :
      ∀ zl : GhostToken n psi,
        ghostTokenAt kind G e = some zl →
        zl.lmeta.id ≠ z.lmeta.id := by
    intro zl hl hid
    have heq :=
      huniq.1
        kind e (ring.rightNeighbor e)
        zl z hl howner hid
    exact hne heq.symm


  have hNotFresh :
      z.lmeta.id ≠ .born kind step := by
    intro hz
    have hs :=
      huniq.2
        kind (ring.rightNeighbor e) z
        kind step howner hz
    exact (Nat.lt_irrefl step) hs


  have htok0 :
      tokenAt kind
          (G.phys (ring.rightNeighbor e)) =
        some z.value :=
    sweepRespGhostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner


  have hvalid0 :
      ValidToken kind G.phys
        (ring.rightNeighbor e) :=
    sweepRespOwner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner


  rcases hsame with hleft | hright
  · rcases hleft with ⟨zL, hL, hidL⟩
    have hLmirror :
        (sweepRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (some z)).left =
        some zL := by
      have hL' :
          (sweepRespSelectedPair
            hpsi ring step G e kind).left =
          some zL := by
        rw [hpair]
        exact hL
      change
        (sweepRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).left =
          some zL at hL'
      rw [howner] at hL'
      exact hL'


    have hshape :=
      sweepRespLeftSameId
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        z zL hNoLeft hNotFresh
        hLmirror hidL


    have htokSelected :=
      (sweepRespGhostMove_valueSound
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        (some z)).1 zL hLmirror


    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys e) =
          some zL.value := by
      exact htokStep.1.trans htokSelected


    rcases hshape with ⟨hmeta, hturnClass | hord⟩
    · have hrow :=
        hturn
          hpsi ring k kind step G e z zL
          hCd hCd' hsound hwin howner
          hL hidL hmeta
          hturnClass.1 htokPost hturnClass.2
      rcases hrow with
        ⟨hwinE, hfresh, hvalid,
          hmono, hservice⟩
      exact
        Or.inr
          ⟨e, zL, hwinE,
            Or.inl ⟨rfl, hL⟩,
            hidL, hfresh, hvalid,
            hmono, hservice⟩


    · rcases hord with ⟨hc, hc'⟩
      have hneg :
          decodeOffset psi (tokenCode z.value) < 0 := by
        omega
      rcases
        sweepRespPredecessorData
          hpsi ring k kind G e z
          hCd hsound hwin howner hneg
        with ⟨x, y, hxr, hye, hyx⟩


      have hwinE :
          Lemma4InWindow ring k psi e :=
        ⟨y, hye⟩


      have htarget :=
        sweepRespNegativeStep_target
          hpsi ring k kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          e x y z.value zL.value
          hCd hCd'
          hxr hye hyx hc hc'


      have hvalid :
          ValidToken kind
            (ghostStep hpsi ring step G e).phys e :=
        sweepRespNegativeStep_valid
          kind
          G.phys
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) e
          z.value zL.value
          htok0 htokPost hvalid0 hc hc' htarget


      have hprog :
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              zL.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1 :=
        sweepRespNegativeStep_progress
          kind
          (G.phys (ring.rightNeighbor e))
          ((ghostStep hpsi ring step G e).phys e)
          z.value zL.value hc hc' htarget


      have hfresh :
          FreshAt kind k z.lmeta →
            FreshAt kind k zL.lmeta :=
        sweepRespFresh_advance
          kind k z zL hmeta


      have hmono :
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value ≤
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys e)
              zL.value := by
        rw [hprog]
        omega


      exact
        Or.inr
          ⟨e, zL, hwinE,
            Or.inl ⟨rfl, hL⟩,
            hidL, hfresh, hvalid,
            hmono,
            fun _ => hprog⟩


  · rcases hright with ⟨zR, hR, hidR⟩
    have hRmirror :
        (sweepRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (some z)).right =
        some zR := by
      have hR' :
          (sweepRespSelectedPair
            hpsi ring step G e kind).right =
          some zR := by
        rw [hpair]
        exact hR
      change
        (sweepRespGhostMoveToken
          hpsi kind step e
          p.1 p.2
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e))).right =
          some zR at hR'
      rw [howner] at hR'
      exact hR'


    have hzz :
        zR = z :=
      sweepRespRightSameId
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        z zR hNoLeft hNotFresh
        hRmirror hidR
    subst zR


    have htokSelected :=
      (sweepRespGhostMove_valueSound
        hpsi kind step e p.1 p.2
        (ghostTokenAt kind G e)
        (some z)).2 z hRmirror


    have htokPost :
        tokenAt kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)) =
          some z.value := by
      exact htokStep.2.trans htokSelected


    have hdist :
        ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist =
          (G.phys (ring.rightNeighbor e)).dist :=
      sweepRespCd_dist_same
        ring k kind
        G.phys
        (ghostStep hpsi ring step G e).phys
        hCd hCd'
        (ring.rightNeighbor e) hwin


    have hvalid :
        ValidToken kind
          (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) :=
      sweepRespValid_same_dist
        kind
        G.phys
        (ghostStep hpsi ring step G e).phys
        (ring.rightNeighbor e)
        z.value htok0 htokPost hdist hvalid0


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
      sweepRespProgress_dist_eq
        kind
        (G.phys (ring.rightNeighbor e))
        ((ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e))
        z.value hdist


    have hservice :
        e =
            lemma4ServiceEdge
              ring kind G (ring.rightNeighbor e) z →
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys
                (ring.rightNeighbor e))
              z.value =
            lemma4TokenProgress
                kind
                (G.phys (ring.rightNeighbor e))
                z.value +
              1 := by
      intro hs
      by_cases hpos :
          0 < decodeOffset psi (tokenCode z.value)
      · unfold lemma4ServiceEdge at hs
        rw [if_pos hpos] at hs
        exact False.elim (hne hs.symm)
      · have hv :=
          decodeOffset_valid
            psi (by omega) (tokenCode z.value)
        have hneg :
            decodeOffset psi (tokenCode z.value) < 0 := by
          rcases hv with hn | hp
          · omega
          · omega


        have hwinE :
            Lemma4InWindow ring k psi e := by
          rcases
            sweepRespPredecessorData
              hpsi ring k kind G e z
              hCd hsound hwin howner hneg
            with ⟨_x, y, _hxr, hye, _hyx⟩
          exact ⟨y, hye⟩


        have hlastE :
            ((ghostStep hpsi ring step G e).phys e).last =
              false :=
          sweepRespCd_last_false
            ring k kind
            (ghostStep hpsi ring step G e).phys
            hCd' e hwinE
        have hlastR :
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e)).last =
              false :=
          sweepRespCd_last_false
            ring k kind
            (ghostStep hpsi ring step G e).phys
            hCd' (ring.rightNeighbor e) hwin


        have hpLast :
            p.1.last = false ∧ p.2.last = false := by
          constructor
          · rw [← hlastStep.1]
            exact hlastE
          · rw [← hlastStep.2]
            exact hlastR


        have hpositive :=
          sweepRespRightSameId_positive_of_gate
            hpsi kind step e p.1 p.2
            (ghostTokenAt kind G e)
            z z
            hNoLeft hNotFresh
            hpLast hRmirror rfl
        exact False.elim (hpos hpositive)


    have hmono :
        lemma4TokenProgress
            kind
            (G.phys (ring.rightNeighbor e))
            z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys
              (ring.rightNeighbor e))
            z.value := by
      exact Nat.le_of_eq hprogEq.symm


    exact
      Or.inr
        ⟨ring.rightNeighbor e, z,
          hwin,
          Or.inr ⟨rfl, hR⟩,
          rfl,
          (fun hfresh => hfresh),
          hvalid, hmono, hservice⟩



theorem lemma4SweepResponderSameIdBranch_proved :
    Lemma4SweepResponderSameIdBranch :=
  lemma4SweepResponderSameIdBranch_of_negTurnRow
    (by
      unfold Lemma4SweepResponderNegTurnProgressRow
      exact lemma4SweepResponderNegTurnProgressRow_proved)

theorem lemma4SweepResponderLiteralCases_closed :
    Lemma4SweepResponderLiteralCases :=
  lemma4SweepResponderLiteralCases_of_sameIdBranch
    lemma4SweepResponderSameIdBranch_proved

end PPL


#print axioms PPL.lemma4SweepResponderSameIdBranch_of_negTurnRow
#print axioms PPL.lemma4SweepResponderSameIdBranch_proved
#print axioms PPL.lemma4SweepResponderLiteralCases_closed
