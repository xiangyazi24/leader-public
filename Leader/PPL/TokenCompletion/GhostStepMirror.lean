import Leader.PPL.TokenCompletion.RightmostResponder
import Lean


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Lemma 4 ghost-step export


The selected-colour mirror below is copied definition-for-definition from the
already compiled mirror in TokenCorrectnessLemma4RunFacts.  Only the public
surface changes: it reads the old owners through ghostTokenAt and exposes the
lineage increment explicitly.
-/


/-- Public metadata update for one actual token move. -/
def ghostStepLineageAdvance
    {n : Nat} (m : LineageMeta n) : LineageMeta n :=
  { m with moves := m.moves + 1 }


/-
Build implementation-private names only inside the elaborator, following the
ClockSuffixBridge pattern.  No implementation-private declaration appears in
a theorem or definition type.
-/
private def ghostStepCorePrivateName (stem : String) : Lean.Name :=
  let base :=
    Lean.Name.str Lean.Name.anonymous ("_" ++ "private")
  ((((((base.str "Leader").str "PPL").str
      "TokenCorrectness").str "Ghost").num 0).str "PPL").str stem


elab "unfoldGhostStepCore" : tactic => do
  let stems := [
    "setTwo", "ghostMoveToken", "bumpTo", "birthGhost",
    "liveValue", "liveShadow", "tokenPrelude",
    "tcLocalValid", "tcMkToken", "tcBitToFin"
  ]
  for stem in stems do
    let nm := Lean.mkIdent (ghostStepCorePrivateName stem)
    let tac ← `(tactic| try (unfold $nm:ident at *))
    Lean.Elab.Tactic.evalTactic tac


/-! ## Public selected-colour result -/


private def ghostStepExportBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def ghostStepExportMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def ghostStepExportLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) <= target ∧
        target <= (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 <= target ∧
        target <= (((psi - 1 : Nat)) : Int))


private instance instDecidableGhostStepExportLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (ghostStepExportLocalValid kind q t) := by
  unfold ghostStepExportLocalValid
  infer_instance


private def ghostStepExportTokenPrelude
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


private def ghostStepExportLiveShadow
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
              ghostStepExportLocalValid kind q t then
            some z
          else
            none


private def ghostStepExportLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if ghostStepExportLocalValid kind q t then
        some t
      else
        none


private def ghostStepExportBirthGhost
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      ghostStepExportMkToken
        (offsetPsiCode psi hpsi)
        (ghostStepExportBitToFin (!idBit))
        (ghostStepExportBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def ghostStepExportBumpTo
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
        ghostStepLineageAdvance z.lmeta
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if ghostStepExportLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def ghostStepExportNegTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    ghostStepExportMkToken
      (offsetPsiCode psi hpsi)
      (ghostStepExportBitToFin (!sourceBit))
      (ghostStepExportBitToFin sourceBit)
  else
    ghostStepExportMkToken
      (offsetPsiCode psi hpsi)
      (ghostStepExportBitToFin sourceBit)
      (0 : Fin 2)


private def ghostStepExportFinishMove
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
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
          ghostStepExportMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          ghostStepExportBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          ghostStepExportMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          ghostStepExportBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                ghostStepExportNegTurnNext hpsi l.id t
              let b :=
                ghostStepExportBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                ghostStepExportMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                ghostStepExportBumpTo kind l next gr0
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
              ghostStepExportNegTurnNext hpsi l.id t
            let b :=
              ghostStepExportBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c <= -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              ghostStepExportMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              ghostStepExportBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩


private def ghostStepExportGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := ghostStepExportLiveValue kind l
  let rv0 := ghostStepExportLiveValue kind r
  let gl0 := ghostStepExportLiveShadow kind l gl
  let gr0 := ghostStepExportLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ghostStepExportBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (ghostStepExportBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    ghostStepExportFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩


private def ghostStepExportSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k


def ghostStepSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let pre :=
    ghostStepExportTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      ghostStepExportGhostMoveToken
        hpsi .black step e
        pre.1 pre.2
        (ghostTokenAt .black G e) (ghostTokenAt .black G rsite)
  | .white =>
      let qb :=
        moveToken hpsi .black pre.1 pre.2
      ghostStepExportGhostMoveToken
        hpsi .white step e
        qb.1 qb.2
        (ghostTokenAt .white G e) (ghostTokenAt .white G rsite)


private theorem ghostStepExportBridge
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      ghostStepExportSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (ghostStepSelectedPair
          hpsi ring step G e kind).left
        (ghostStepSelectedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> try unfold ghostStep
  all_goals
    unfoldGhostStepCore
    rfl




/-! ## Public site equations -/


/-- The physical component is exactly the public protocol step. -/
theorem ghostStep_phys_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (ghostStep hpsi ring step G e).phys =
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e := by
  rfl


/--
Frame equation, proved first.  A site outside the interaction pair keeps its
selected-colour owner literally.
-/
theorem ghostTokenAt_ghostStep_frame
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e j : Fin n)
    (kind : TokenKind)
    (hje : j ≠ e)
    (hjr : j ≠ ring.rightNeighbor e) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
      ghostTokenAt kind G j := by
  rw [ghostStepExportBridge
    hpsi ring step G e kind j]
  simp [ghostStepExportSetTwo, hje, hjr]


/-- Initiator equation: setTwo gives priority to the first endpoint. -/
theorem ghostTokenAt_ghostStep_initiator
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) e =
      (ghostStepSelectedPair
        hpsi ring step G e kind).left := by
  rw [ghostStepExportBridge
    hpsi ring step G e kind e]
  simp [ghostStepExportSetTwo]


/--
Responder equation, including the singleton-ring alias case.  Thus the
statement is exact without an extra n ≥ 2 premise.
-/
theorem ghostTokenAt_ghostStep_responder
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) =
      if ring.rightNeighbor e = e then
        (ghostStepSelectedPair
          hpsi ring step G e kind).left
      else
        (ghostStepSelectedPair
          hpsi ring step G e kind).right := by
  rw [ghostStepExportBridge
    hpsi ring step G e kind
      (ring.rightNeighbor e)]
  by_cases hne : ring.rightNeighbor e = e
  · simp [ghostStepExportSetTwo, hne]
  · simp [ghostStepExportSetTwo, hne]


/-- Convenient non-singleton responder specialization used by Lemma 4. -/
theorem ghostTokenAt_ghostStep_responder_of_ne
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) =
      (ghostStepSelectedPair
        hpsi ring step G e kind).right := by
  simpa [hne] using
    ghostTokenAt_ghostStep_responder
      hpsi ring step G e kind


end PPL


#print axioms PPL.ghostStep_phys_export
#print axioms PPL.ghostTokenAt_ghostStep_frame
#print axioms PPL.ghostTokenAt_ghostStep_initiator
#print axioms PPL.ghostTokenAt_ghostStep_responder
#print axioms PPL.ghostTokenAt_ghostStep_responder_of_ne
