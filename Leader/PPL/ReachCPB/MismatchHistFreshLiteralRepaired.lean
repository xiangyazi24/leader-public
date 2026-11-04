import Leader.PPL.ReachCPB.MismatchHistFreshLiteralRows
import Leader.PPL.ReachCPB.MismatchHistFreshLiteralTransport
import Leader.PPL.ReachCPB.MismatchHistFreshTerminalSelectedPass
import Leader.PPL.TokenCompletion.GhostStepMirror
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
# Repaired c=+1 owner row and the live literal aged row

`Lemma16AgedC1OwnerRow` is false as stated
(`lemma16AgedC1OwnerRow_false`): `Lemma16AgedC1Data` ties the post owner only
to its ghost source and records no link between the ghost value and the
physical token that the literal step serves.  This file

1. adds that link (`Lemma16AgedC1PhysData`): the selected-colour Algorithm-3
   input pair at the interaction satisfies the literal c=1 service
   preconditions with the physical token equal to `source.value`;
2. reproves the owner-provenance row with the repaired c=1 case
   (`Lemma16AgedSelectedOwnerCaseRowPhys`), since the ghost step only takes
   the c=1 branch when those preconditions hold;
3. proves the repaired c=1 transport row (`Lemma16AgedC1OwnerRowPhys`):
   either the physical bit matches the responder ID, which is exactly the
   new negative latch, or Algorithm 3 line 20 creates a shielded leader and
   the post state is CPB;
4. assembles `Lemma16PostEpochFreshSelectedLiveLiteralAgedRow`.

The ghost-move mirror is copied from
`ReachCPBMismatchHistFreshLiteralOwnerCase` (prefix `rp`); the Algorithm-3
line-20 mirror and the birth-to-CPB closure are copied from
`ReachCPBMismatchHistFreshTerminalSelectedPass` and
`ReachCPBMismatchHistFreshTerminalDetectBirth`.
-/

/-! ## Proof-local mirror of the selected-colour ghost move -/

private def rpBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def rpMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

/-- Literal local validity of a selected-colour token (public copy of the
ghost-step `tcLocalValid`). -/
def Lemma16AgedLocalValid
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

private instance instDecidableRpLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (Lemma16AgedLocalValid kind q t) := by
  unfold Lemma16AgedLocalValid
  infer_instance

private def rpTokenPrelude
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
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def rpLiveShadow
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
          if z.value = t ∧ Lemma16AgedLocalValid kind q t then
            some z
          else
            none

/-- The selected-colour token of a state when it is locally valid (public
copy of the ghost-step `liveValue`). -/
def lemma16AgedLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if Lemma16AgedLocalValid kind q t then
        some t
      else
        none

private def rpBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      rpMkToken
        (offsetPsiCode psi hpsi)
        (rpBitToFin (!idBit))
        (rpBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def rpBumpTo
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
        if Lemma16AgedLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def rpNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    rpMkToken
      (offsetPsiCode psi hpsi)
      (rpBitToFin (!sourceBit))
      (rpBitToFin sourceBit)
  else
    rpMkToken
      (offsetPsiCode psi hpsi)
      (rpBitToFin sourceBit)
      (0 : Fin 2)

private def rpFinishMove
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
          rpMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := rpBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          rpMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := rpBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                rpNegTurnNext hpsi l.id tr
              let b := rpBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid psi (by omega) (tokenCode tr)
              let next :=
                rpMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := rpBumpTo kind l next gr0
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
              rpNegTurnNext hpsi l.id tr
            let b := rpBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid psi (by omega) (tokenCode tr)
            let next :=
              rpMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := rpBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def rpGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := lemma16AgedLiveValue kind l
  let rv0 := lemma16AgedLiveValue kind r
  let gl0 := rpLiveShadow kind l gl
  let gr0 := rpLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (rpBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (rpBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

/-- The Algorithm-3 input pair of the selected colour: the Algorithm-2
prelude output for black, and the black `moveToken` output for white. -/
def lemma16AgedSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := rpTokenPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2

private def rpSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    lemma16AgedSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  rpGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem rpSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    rpSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

/-! ## The initiator ID is untouched before the selected move -/

private theorem rpDetermineModeLeftId
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (determineMode l r).1.id = l.id := by
  simp only [determineMode]
  repeat' (first
    | split <;> try dsimp only
    | rfl)
  all_goals rfl

private theorem rpPreludeLeftId
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    (rpTokenPrelude hpsi l r).1.id = l.id := by
  let s := createLeaderThroughLine6 hpsi l r
  have hs : s.left.id = l.id := by
    dsimp only [s, createLeaderThroughLine6]
    have hd :=
      rpDetermineModeLeftId l r
    first
      | exact hd
      | (split <;> simpa using hd)
  dsimp only [rpTokenPrelude]
  repeat' (first
    | split <;> try dsimp only
    | rfl)
  all_goals simpa [s] using hs

private theorem rpMoveTokenLeftId
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.id = l.id := by
  have h :=
    congrArg (fun q : State psi kappa => q.id)
      (moveToken_initiator_fields hpsi kind l r)
  cases kind <;>
    simpa [eraseKindToken] using h

private theorem lemma16AgedSelectedInputLeftId
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (lemma16AgedSelectedInput hpsi kind l r).1.id = l.id := by
  cases kind with
  | black =>
      exact rpPreludeLeftId hpsi l r
  | white =>
      exact
        (rpMoveTokenLeftId hpsi TokenKind.black
          (rpTokenPrelude hpsi l r).1
          (rpTokenPrelude hpsi l r).2).trans
          (rpPreludeLeftId hpsi l r)

/-! ## Elementary facts about the mirrored pieces -/

private theorem rpLiveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      rpLiveShadow kind q g = some z) :
    g = some z := by
  cases hg : g with
  | none =>
      simp [rpLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [rpLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                Lemma16AgedLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [rpLiveShadow, hg, ht, hv]
                using hz
            subst z
            rfl
          · simp
              [rpLiveShadow, hg, ht, hv]
              at hz

private theorem rpLiveShadow_value
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      rpLiveShadow kind q g = some z) :
    lemma16AgedLiveValue kind q = some z.value := by
  cases hg : g with
  | none =>
      simp [rpLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [rpLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                Lemma16AgedLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [rpLiveShadow, hg, ht, hv]
                using hz
            subst z
            simp [lemma16AgedLiveValue, ht, hv.2, hv.1]
          · simp
              [rpLiveShadow, hg, ht, hv]
              at hz

private theorem rpBump_live
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      (rpBumpTo kind qDest newValue g).live = some z) :
    ∃ z0 : GhostToken n psi,
      g = some z0 ∧
      z =
        { value := newValue
          lmeta := ghostStepLineageAdvance z0.lmeta } := by
  cases hg : g with
  | none =>
      rw [hg] at hz
      simp [rpBumpTo] at hz
  | some z0 =>
      rw [hg] at hz
      by_cases hv : Lemma16AgedLocalValid kind qDest newValue
      · have hzz :
            ({ value := newValue
               lmeta := ghostStepLineageAdvance z0.lmeta } :
              GhostToken n psi) = z := by
          simpa [rpBumpTo, hv] using hz
        exact ⟨z0, rfl, hzz.symm⟩
      · simp [rpBumpTo, hv] at hz

private theorem rpBitToFin_bit
    {psi : Nat}
    (off : Fin (2 * psi - 1))
    (b : Bool) (c : Fin 2) :
    tokenBitBool (rpMkToken off (rpBitToFin b) c) = b := by
  cases b <;> rfl

private theorem rpBitToFin_carry
    {psi : Nat}
    (off : Fin (2 * psi - 1))
    (b : Bool) (c : Fin 2) :
    tokenCarryBool (rpMkToken off c (rpBitToFin b)) = b := by
  cases b <;> rfl

private theorem rpNegTurnNext_offset
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (b : Bool)
    (t : TokenData psi) :
    decodeOffset psi (tokenCode (rpNegTurnNext hpsi b t)) =
      ((psi : Nat) : Int) := by
  unfold rpNegTurnNext
  split
  · exact decodeOffset_psi psi hpsi
  · exact decodeOffset_psi psi hpsi

private theorem rpNegTurnNext_payload
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (b : Bool)
    (t : TokenData psi) :
    if tokenCarryBool t = true then
      And
        (tokenBitBool (rpNegTurnNext hpsi b t) = !b)
        (tokenCarryBool (rpNegTurnNext hpsi b t) = b)
    else
      And
        (tokenBitBool (rpNegTurnNext hpsi b t) = b)
        (tokenCarryBool (rpNegTurnNext hpsi b t) = false) := by
  by_cases hc : t.2 = (1 : Fin 2)
  · have hcb : tokenCarryBool t = true := by
      unfold tokenCarryBool
      rw [hc]
      rfl
    rw [if_pos hcb]
    unfold rpNegTurnNext
    rw [if_pos hc]
    exact ⟨rpBitToFin_bit _ _ _, rpBitToFin_carry _ _ _⟩
  · have hv : t.2.val ≠ 1 := fun h => hc (Fin.ext h)
    have hcb : tokenCarryBool t = false := by
      unfold tokenCarryBool
      first
        | exact beq_false_of_ne hv
        | simp [hv]
    rw [if_neg (by rw [hcb]; decide)]
    unfold rpNegTurnNext
    rw [if_neg hc]
    exact ⟨rpBitToFin_bit _ _ _, rfl⟩

private theorem rpNegTurnNext_payload_eq
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (b b' : Bool)
    (hb : b = b')
    (t : TokenData psi) :
    if tokenCarryBool t = true then
      And
        (tokenBitBool (rpNegTurnNext hpsi b t) = !b')
        (tokenCarryBool (rpNegTurnNext hpsi b t) = b')
    else
      And
        (tokenBitBool (rpNegTurnNext hpsi b t) = b')
        (tokenCarryBool (rpNegTurnNext hpsi b t) = false) := by
  subst hb
  exact rpNegTurnNext_payload hpsi b t

private theorem rpBirth_bit
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (b : Bool) :
    tokenBitBool
        (rpBirthGhost (n := n) hpsi kind step site b).value =
      !b := by
  cases b <;> rfl

private theorem rpBirth_carry
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (b : Bool) :
    tokenCarryBool
        (rpBirthGhost (n := n) hpsi kind step site b).value =
      b := by
  cases b <;> rfl

/-! ## Named successor values of the two ordinary moves -/

private def rpDecNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (h2 : 2 ≤ decodeOffset psi (tokenCode t)) :
    TokenData psi :=
  have hc : ValidOffset psi (decodeOffset psi (tokenCode t)) :=
    decodeOffset_valid psi (by omega) (tokenCode t)
  rpMkToken
    (encodeOffset psi (decodeOffset psi (tokenCode t) - 1) (by
      rcases hc with hn | hp
      · exfalso
        omega
      · right
        omega))
    t.1.2 t.2

private def rpIncNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (h2 : decodeOffset psi (tokenCode t) ≤ -2) :
    TokenData psi :=
  have hc : ValidOffset psi (decodeOffset psi (tokenCode t)) :=
    decodeOffset_valid psi (by omega) (tokenCode t)
  rpMkToken
    (encodeOffset psi (decodeOffset psi (tokenCode t) + 1) (by
      rcases hc with hn | hp
      · left
        omega
      · exfalso
        omega))
    t.1.2 t.2

private theorem rpDecNext_offset
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (h2 : 2 ≤ decodeOffset psi (tokenCode t)) :
    decodeOffset psi (tokenCode (rpDecNext hpsi t h2)) =
      decodeOffset psi (tokenCode t) - 1 := by
  unfold rpDecNext
  exact decode_encode _ _ _

private theorem rpIncNext_offset
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (h2 : decodeOffset psi (tokenCode t) ≤ -2) :
    decodeOffset psi (tokenCode (rpIncNext hpsi t h2)) =
      decodeOffset psi (tokenCode t) + 1 := by
  unfold rpIncNext
  exact decode_encode _ _ _

private theorem rpDecNext_bit
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (h2 : 2 ≤ decodeOffset psi (tokenCode t)) :
    tokenBitBool (rpDecNext hpsi t h2) = tokenBitBool t :=
  rfl

private theorem rpDecNext_carry
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi)
    (h2 : 2 ≤ decodeOffset psi (tokenCode t)) :
    tokenCarryBool (rpDecNext hpsi t h2) = tokenCarryBool t :=
  rfl

/-! ## The five shapes of the finishing move -/

private theorem rpFinish_cases
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) :
    (∃ t : TokenData psi,
      lv2 = some t ∧
      decodeOffset psi (tokenCode t) = 1 ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left = none ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right =
        (rpBumpTo kind r
          (rpMkToken (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2) gl2).live) ∨
    (∃ t : TokenData psi,
      ∃ h2 : 2 ≤ decodeOffset psi (tokenCode t),
      lv2 = some t ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left = none ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right =
        (rpBumpTo kind r (rpDecNext hpsi t h2) gl2).live) ∨
    (∃ tr : TokenData psi,
      rv0 = some tr ∧
      decodeOffset psi (tokenCode tr) = -1 ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left =
        (rpBumpTo kind l (rpNegTurnNext hpsi l.id tr) gr0).live ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right = none) ∨
    (∃ tr : TokenData psi,
      ∃ h2 : decodeOffset psi (tokenCode tr) ≤ -2,
      rv0 = some tr ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left =
        (rpBumpTo kind l (rpIncNext hpsi tr h2) gr0).live ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right = none) ∨
    ((rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left = gl2 ∧
      (rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right = gr0 ∧
      ∀ t : TokenData psi, lv2 = some t →
        ¬ (2 ≤ decodeOffset psi (tokenCode t))) := by
  cases hlv : lv2 with
  | none =>
      cases hrv : rv0 with
      | none =>
          right; right; right; right
          refine ⟨?_, ?_, ?_⟩
          · simp only [rpFinishMove] <;> rfl
          · simp only [rpFinishMove] <;> rfl
          · intro t ht
            exact absurd ht (by simp)
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · right; right; left
            refine ⟨tr, rfl, hm1, ?_, ?_⟩
            · simp only [rpFinishMove, dif_pos hm1]
            · simp only [rpFinishMove, dif_pos hm1]
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · right; right; right; left
              refine ⟨tr, hm2, rfl, ?_, ?_⟩
              · simp only [rpFinishMove, dif_neg hm1, dif_pos hm2]
                  <;> rfl
              · simp only [rpFinishMove, dif_neg hm1, dif_pos hm2]
            · right; right; right; right
              refine ⟨?_, ?_, ?_⟩
              · simp only [rpFinishMove, dif_neg hm1, dif_neg hm2]
              · simp only [rpFinishMove, dif_neg hm1, dif_neg hm2]
              · intro t ht
                exact absurd ht (by simp)
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · left
        refine ⟨t, rfl, h1, ?_, ?_⟩
        · simp only [rpFinishMove, dif_pos h1]
        · simp only [rpFinishMove, dif_pos h1]
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · right; left
          refine ⟨t, h2, rfl, ?_, ?_⟩
          · simp only [rpFinishMove, dif_neg h1, dif_pos h2]
          · simp only [rpFinishMove, dif_neg h1, dif_pos h2]
              <;> rfl
        · have hsmall :
              ∀ t' : TokenData psi, some t = some t' →
                ¬ (2 ≤ decodeOffset psi (tokenCode t')) := by
            intro t' ht'
            have htt : t = t' := Option.some.inj ht'
            subst htt
            exact h2
          cases hrv : rv0 with
          | none =>
              right; right; right; right
              refine ⟨?_, ?_, hsmall⟩
              · simp only [rpFinishMove, dif_neg h1, dif_neg h2]
              · simp only [rpFinishMove, dif_neg h1, dif_neg h2]
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · right; right; left
                refine ⟨tr, rfl, hm1, ?_, ?_⟩
                · simp only
                    [rpFinishMove, dif_neg h1, dif_neg h2,
                      dif_pos hm1]
                · simp only
                    [rpFinishMove, dif_neg h1, dif_neg h2,
                      dif_pos hm1]
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · right; right; right; left
                  refine ⟨tr, hm2, rfl, ?_, ?_⟩
                  · simp only
                      [rpFinishMove, dif_neg h1, dif_neg h2,
                        dif_neg hm1, dif_pos hm2]
                      <;> rfl
                  · simp only
                      [rpFinishMove, dif_neg h1, dif_neg h2,
                        dif_neg hm1, dif_pos hm2]
                · right; right; right; right
                  refine ⟨?_, ?_, hsmall⟩
                  · simp only
                      [rpFinishMove, dif_neg h1, dif_neg h2,
                        dif_neg hm1, dif_neg hm2]
                  · simp only
                      [rpFinishMove, dif_neg h1, dif_neg h2,
                        dif_neg hm1, dif_neg hm2]

/-! ## Pre-finish structure of one selected-colour move -/

/--
One selected-colour move is either the inactive-last stay, or (both last
bits false) a finishing move whose left candidate is the current birth or a
live old initiator owner, whose value is the left live value, in which case
the right live value is empty (no collision); the right candidate is a live
old responder owner with its own value as the right live value.
-/
private theorem rpGhostMove_structure
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    (∃ gl0 gr0 : Option (GhostToken n psi),
      (∀ s, gl0 = some s → gl = some s) ∧
      (∀ s, gr0 = some s → gr = some s) ∧
      rpGhostMoveToken hpsi kind step site l r gl gr =
        ⟨gl0, gr0, []⟩) ∨
    (∃ (lv2 rv0 : Option (TokenData psi))
        (gl2 gr0 : Option (GhostToken n psi)),
      l.last = false ∧ r.last = false ∧
      (∀ s, gl2 = some s →
        lv2 = some s.value ∧
        lemma16AgedLiveValue kind r = none ∧
        (s = rpBirthGhost hpsi kind step site l.id ∨
          (gl = some s ∧
            lemma16AgedLiveValue kind l = some s.value))) ∧
      (∀ s, gr0 = some s →
        rv0 = some s.value ∧ gr = some s) ∧
      rpGhostMoveToken hpsi kind step site l r gl gr =
        rpFinishMove hpsi kind l r lv2 rv0 gl2 gr0) := by
  let lv0 := lemma16AgedLiveValue kind l
  let rv0 := lemma16AgedLiveValue kind r
  let gl0 := rpLiveShadow kind l gl
  let gr0 := rpLiveShadow kind r gr
  have hgr0 :
      ∀ s, gr0 = some s → rv0 = some s.value ∧ gr = some s := by
    intro s hs
    exact ⟨rpLiveShadow_value kind r gr s hs,
      rpLiveShadow_source kind r gr s hs⟩
  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let lv1 : Option (TokenData psi) :=
      if hb then
        some (rpBirthGhost hpsi kind step site l.id).value
      else lv0
    let gl1 : Option (GhostToken n psi) :=
      if hb then
        some (rpBirthGhost hpsi kind step site l.id)
      else gl0
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 : Option (TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (GhostToken n psi) :=
      if collide then none else gl1
    have hres :
        rpGhostMoveToken hpsi kind step site l r gl gr =
          rpFinishMove
            hpsi kind l r
            lv2 rv0 gl2 gr0 := by
      simp only [rpGhostMoveToken, if_pos hlast]
      rfl
    have hgl2 :
        ∀ s, gl2 = some s →
          lv2 = some s.value ∧
          lemma16AgedLiveValue kind r = none ∧
          (s = rpBirthGhost hpsi kind step site l.id ∨
            (gl = some s ∧
              lemma16AgedLiveValue kind l = some s.value)) := by
      intro s hs
      by_cases hcol : collide
      · simp [gl2, hcol] at hs
      · have hgl1 : gl1 = some s := by
          simpa [gl2, hcol] using hs
        have hlv2 : lv2 = lv1 := by
          show (if collide then none else lv1) = lv1
          rw [if_neg hcol]
        have hlv1 : lv1 = some s.value := by
          by_cases hbirth : hb
          · have hsb :
                rpBirthGhost hpsi kind step site l.id = s := by
              simpa [gl1, hbirth] using hgl1
            show
              (if hb then
                some (rpBirthGhost hpsi kind step site l.id).value
              else lv0) = some s.value
            rw [if_pos hbirth, hsb]
          · have hgl0 : gl0 = some s := by
              simpa [gl1, hbirth] using hgl1
            show
              (if hb then
                some (rpBirthGhost hpsi kind step site l.id).value
              else lv0) = some s.value
            rw [if_neg hbirth]
            exact rpLiveShadow_value kind l gl s hgl0
        have hrv0 : rv0 = none := by
          refine Classical.byContradiction ?_
          intro hne
          apply hcol
          refine ⟨?_, hne⟩
          rw [hlv1]
          intro hh
          cases hh
        refine ⟨hlv2.trans hlv1, hrv0, ?_⟩
        by_cases hbirth : hb
        · have hsb :
              rpBirthGhost hpsi kind step site l.id = s := by
            simpa [gl1, hbirth] using hgl1
          exact .inl hsb.symm
        · have hgl0 : gl0 = some s := by
            simpa [gl1, hbirth] using hgl1
          exact .inr
            ⟨rpLiveShadow_source kind l gl s hgl0,
              rpLiveShadow_value kind l gl s hgl0⟩
    exact .inr ⟨lv2, rv0, gl2, gr0, hlast.1, hlast.2,
      hgl2, hgr0, hres⟩
  · have hres :
        rpGhostMoveToken hpsi kind step site l r gl gr =
          ⟨gl0, gr0, []⟩ := by
      simp only [rpGhostMoveToken, if_neg hlast]
      rfl
    exact .inl ⟨gl0, gr0,
      fun s hs => rpLiveShadow_source kind l gl s hs,
      fun s hs => (hgr0 s hs).2, hres⟩

/-! ## Repaired c=+1 data and owner-case type -/

/--
The c=+1 initiator branch together with its physical certificate.

The first eight fields are exactly `Lemma16AgedC1Data`.  The last four say
that the literal selected-colour Algorithm-3 input pair `(l, r)` at the
interaction (`lemma16AgedSelectedInput`) takes the c=1 service with the
physical token `source.value`: both last bits are false, the initiator's
selected token is `source.value` and locally valid, and the responder has no
locally valid selected token (so no collision).  The ghost step takes its
c=1 branch only under exactly these conditions, so these fields are
produced by the owner-case row; they are what lets Algorithm 3 line 20 be
applied to the physical state.
-/
structure Lemma16AgedC1PhysData
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  source : GhostToken n psi
  howner :
    ghostTokenAt kind G e = some source
  hsite :
    i = ring.rightNeighbor e
  hmeta :
    z.lmeta = ghostStepLineageAdvance source.lmeta
  hbit :
    tokenBitBool z.value =
      tokenBitBool source.value
  hcarry :
    tokenCarryBool z.value =
      tokenCarryBool source.value
  hsourceOffset :
    decodeOffset psi (tokenCode source.value) =
      (1 : Int)
  hpostOffset :
    decodeOffset psi (tokenCode z.value) =
      (1 : Int) - (((psi : Nat) : Int))
  hinitLast :
    (lemma16AgedSelectedInput hpsi kind
      (G.phys e) (G.phys (ring.rightNeighbor e))).1.last = false
  hrespLast :
    (lemma16AgedSelectedInput hpsi kind
      (G.phys e) (G.phys (ring.rightNeighbor e))).2.last = false
  hinitLive :
    lemma16AgedLiveValue kind
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).1 =
      some source.value
  hrespLive :
    lemma16AgedLiveValue kind
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).2 =
      none

/-- Owner cases with the repaired c=+1 constructor. -/
inductive Lemma16AgedSelectedOwnerCasePhys
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  | ordinary :
      Lemma16AgedOrdinaryData
        ring kind step G e i z ->
      Lemma16AgedSelectedOwnerCasePhys
        hpsi ring kind step G e i z
  | c1 :
      Lemma16AgedC1PhysData
        hpsi ring kind G e i z ->
      Lemma16AgedSelectedOwnerCasePhys
        hpsi ring kind step G e i z
  | negOne :
      Lemma16AgedNegOneData
        ring kind G e i z ->
      Lemma16AgedSelectedOwnerCasePhys
        hpsi ring kind step G e i z

/-- `Lemma16AgedSelectedOwnerCaseRow` with the repaired c=+1 case. -/
def Lemma16AgedSelectedOwnerCaseRowPhys : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    LastReadyCapped ring G.phys ->
    forall (i : Fin n)
      (z : GhostToken n psi),
      Or (i = e)
        (i = ring.rightNeighbor e) ->
      ghostTokenAt kind
          (ghostStep hpsi ring step G e) i =
        some z ->
      Nonempty
        (Lemma16AgedSelectedOwnerCasePhys
          hpsi ring kind step G e i z)

/-! ## Owner cases at the initiator and at the responder -/

private theorem rpBirth_offset
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (b : Bool) :
    decodeOffset psi
        (tokenCode (rpBirthGhost (n := n) hpsi kind step site b).value) =
      ((psi : Nat) : Int) :=
  decodeOffset_psi psi hpsi

private theorem rpMove_left
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (l r : State psi kappa)
    (hlid : l.id = (G.phys e).id)
    (z : GhostToken n psi)
    (hz :
      (rpGhostMoveToken hpsi kind step e l r
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G (ring.rightNeighbor e))).left =
        some z) :
    Nonempty
      (Lemma16AgedSelectedOwnerCasePhys
        hpsi ring kind step G e e z) := by
  rcases rpGhostMove_structure hpsi kind step e l r
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G (ring.rightNeighbor e)) with
    ⟨gl0, gr0, hgl0, _hgr0, hres⟩ |
    ⟨lv2, rv0, gl2, gr0, _hll, _hrl, hgl2, hgr0, hres⟩
  · rw [hres] at hz
    have howner : ghostTokenAt kind G e = some z := hgl0 z hz
    exact ⟨.ordinary (.stay
      { site := e
        source := z
        hpair := .inl rfl
        hsite := rfl
        howner := howner
        hsame := rfl })⟩
  · rw [hres] at hz
    rcases rpFinish_cases hpsi kind l r lv2 rv0 gl2 gr0 with
      ⟨t, _hlv, _h1, hL, _hR⟩ |
      ⟨t, _h2, _hlv, hL, _hR⟩ |
      ⟨tr, hrv, hm1, hL, _hR⟩ |
      ⟨tr, hm2, hrv, hL, _hR⟩ |
      ⟨hL, _hR, hsmall⟩
    · rw [hL] at hz
      exact absurd hz (by simp)
    · rw [hL] at hz
      exact absurd hz (by simp)
    · rw [hL] at hz
      rcases rpBump_live kind l _ gr0 z hz with ⟨s, hs, hzeq⟩
      rcases hgr0 s hs with ⟨hrvs, howner⟩
      have hts : tr = s.value :=
        Option.some.inj (hrv.symm.trans hrvs)
      subst hts
      subst hzeq
      have hpay :=
        rpNegTurnNext_payload_eq hpsi l.id (G.phys e).id hlid s.value
      exact ⟨.negOne
        { source := s
          howner := howner
          hsite := rfl
          hmeta := rfl
          hsourceOffset := hm1
          hpostOffset :=
            rpNegTurnNext_offset hpsi l.id s.value
          hpayload := hpay }⟩
    · rw [hL] at hz
      rcases rpBump_live kind l _ gr0 z hz with ⟨s, hs, hzeq⟩
      rcases hgr0 s hs with ⟨hrvs, howner⟩
      have hts : tr = s.value :=
        Option.some.inj (hrv.symm.trans hrvs)
      subst hts
      subst hzeq
      exact ⟨.ordinary (.left
        { source := s
          howner := howner
          hsite := rfl
          hmeta := rfl
          hbit := rfl
          hcarry := rfl
          hnegative := hm2
          hoffset := rpIncNext_offset hpsi s.value hm2 })⟩
    · rw [hL] at hz
      rcases hgl2 z hz with ⟨hlvz, _hrvnone, hbirth | ⟨howner, _hlive⟩⟩
      · exfalso
        have hn2 := hsmall z.value hlvz
        rw [hbirth, rpBirth_offset] at hn2
        exact hn2 (by omega)
      · exact ⟨.ordinary (.stay
          { site := e
            source := z
            hpair := .inl rfl
            hsite := rfl
            howner := howner
            hsame := rfl })⟩

private theorem rpMove_right
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (l r : State psi kappa)
    (hl :
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).1 = l)
    (hr :
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).2 = r)
    (hlid : l.id = (G.phys e).id)
    (z : GhostToken n psi)
    (hz :
      (rpGhostMoveToken hpsi kind step e l r
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G (ring.rightNeighbor e))).right =
        some z) :
    Nonempty
      (Lemma16AgedSelectedOwnerCasePhys
        hpsi ring kind step G e (ring.rightNeighbor e) z) := by
  rcases rpGhostMove_structure hpsi kind step e l r
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G (ring.rightNeighbor e)) with
    ⟨gl0, gr0, _hgl0, hgr0, hres⟩ |
    ⟨lv2, rv0, gl2, gr0, hll, hrl, hgl2, hgr0, hres⟩
  · rw [hres] at hz
    have howner :
        ghostTokenAt kind G (ring.rightNeighbor e) = some z :=
      hgr0 z hz
    exact ⟨.ordinary (.stay
      { site := ring.rightNeighbor e
        source := z
        hpair := .inr rfl
        hsite := rfl
        howner := howner
        hsame := rfl })⟩
  · rw [hres] at hz
    rcases rpFinish_cases hpsi kind l r lv2 rv0 gl2 gr0 with
      ⟨t, hlv, h1, _hL, hR⟩ |
      ⟨t, h2, hlv, _hL, hR⟩ |
      ⟨tr, _hrv, _hm1, _hL, hR⟩ |
      ⟨tr, _hm2, _hrv, _hL, hR⟩ |
      ⟨_hL, hR, _hsmall⟩
    · rw [hR] at hz
      rcases rpBump_live kind r _ gl2 z hz with ⟨s, hs, hzeq⟩
      rcases hgl2 s hs with
        ⟨hlvs, hrvnone, hbirth | ⟨howner, hlive⟩⟩
      · exfalso
        have hts : t = s.value :=
          Option.some.inj (hlv.symm.trans hlvs)
        subst hts
        rw [hbirth, rpBirth_offset] at h1
        omega
      · have hts : t = s.value :=
          Option.some.inj (hlv.symm.trans hlvs)
        subst hts
        subst hzeq
        exact ⟨.c1
          { source := s
            howner := howner
            hsite := rfl
            hmeta := rfl
            hbit := rfl
            hcarry := rfl
            hsourceOffset := h1
            hpostOffset :=
              decodeOffset_negPsiPlusOne psi hpsi
            hinitLast := by
              rw [hl]
              exact hll
            hrespLast := by
              rw [hr]
              exact hrl
            hinitLive := by
              rw [hl]
              exact hlive
            hrespLive := by
              rw [hr]
              exact hrvnone }⟩
    · rw [hR] at hz
      rcases rpBump_live kind r _ gl2 z hz with ⟨s, hs, hzeq⟩
      rcases hgl2 s hs with
        ⟨hlvs, _hrvnone, hbirth | ⟨howner, _hlive⟩⟩
      · have hts : t = s.value :=
          Option.some.inj (hlv.symm.trans hlvs)
        subst hts
        subst hbirth
        subst hzeq
        have hoff :=
          rpDecNext_offset hpsi
            (rpBirthGhost (n := n) hpsi kind step e l.id).value h2
        rw [rpBirth_offset] at hoff
        exact ⟨.ordinary (.birth
          { hsite := rfl
            hid := rfl
            hbirthSite := rfl
            hbirthStep := rfl
            hmoves := rfl
            hoffset := hoff.trans (by omega)
            hbit := by
              rw [← hlid]
              exact (rpDecNext_bit hpsi _ h2).trans
                (rpBirth_bit hpsi kind step e l.id)
            hcarry := by
              rw [← hlid]
              exact (rpDecNext_carry hpsi _ h2).trans
                (rpBirth_carry hpsi kind step e l.id) })⟩
      · have hts : t = s.value :=
          Option.some.inj (hlv.symm.trans hlvs)
        subst hts
        subst hzeq
        exact ⟨.ordinary (.right
          { source := s
            howner := howner
            hsite := rfl
            hmeta := rfl
            hbit := rfl
            hcarry := rfl
            hpositive := h2
            hoffset := rpDecNext_offset hpsi s.value h2 })⟩
    · rw [hR] at hz
      exact absurd hz (by simp)
    · rw [hR] at hz
      exact absurd hz (by simp)
    · rw [hR] at hz
      have howner :
          ghostTokenAt kind G (ring.rightNeighbor e) = some z :=
        (hgr0 z hz).2
      exact ⟨.ordinary (.stay
        { site := ring.rightNeighbor e
          source := z
          hpair := .inr rfl
          hsite := rfl
          howner := howner
          hsame := rfl })⟩

private theorem rpRightNeighborNe
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt
  rcases Nat.lt_or_ge (e.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    omega
  · have h2 : e.val + 1 = n := by omega
    rw [h2, Nat.mod_self] at hv
    omega

/--
Selected-pair owner provenance with the physical c=+1 certificate.

Same case tree as `lemma16AgedSelectedOwnerCaseRow_proved`; in the c=+1
branch the ghost step has both last bits false, the initiator live value
equal to the source value, and no live responder token (otherwise the
collision would have removed the initiator candidate), which are exactly
the extra fields of `Lemma16AgedC1PhysData`.
-/
theorem lemma16AgedSelectedOwnerCaseRowPhys_proved :
    Lemma16AgedSelectedOwnerCaseRowPhys := by
  intro n psi kappa hpsi hn3 ring kind step G e _hready i z hi hz
  have hne := rpRightNeighborNe hn3 ring e
  have hlid :
      (lemma16AgedSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1.id =
        (G.phys e).id :=
    lemma16AgedSelectedInputLeftId hpsi kind _ _
  rcases hi with hi | hi
  · rw [hi] at hz ⊢
    rw [ghostTokenAt_ghostStep_initiator,
      ← rpSelectedPair_eq_export] at hz
    exact rpMove_left hpsi ring kind step G e
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).1
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).2
      hlid z hz
  · rw [hi] at hz ⊢
    rw [ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e kind hne,
      ← rpSelectedPair_eq_export] at hz
    exact rpMove_right hpsi ring kind step G e
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).1
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).2
      rfl rfl hlid z hz


/-! ## Algorithm 3 line 20 (copied from TerminalSelectedPass) -/

private theorem rpaLiveValue_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (h : lemma16AgedLiveValue kind q = some v) :
    tokenAt kind q = some v ∧
      Lemma16AgedLocalValid kind q v := by
  cases ht : tokenAt kind q with
  | none =>
      simp [lemma16AgedLiveValue, ht] at h
  | some t =>
      by_cases hv : Lemma16AgedLocalValid kind q t
      · have htv : t = v := by
          simpa [lemma16AgedLiveValue, ht, hv] using h
        subst htv
        exact ⟨rfl, hv⟩
      · simp [lemma16AgedLiveValue, ht, hv] at h

/-! ## A definitional mirror of Algorithm 3 -/

private def rpaSet
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def rpaClear
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if Lemma16AgedLocalValid kind q t then q else rpaSet kind q none

private def rpaLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private def rpaMove
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let l := rpaClear kind l
  let r := rpaClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧ tokenAt kind l = none then
        rpaSet kind l
          (some (rpMkToken (offsetPsiCode psi hpsi)
            (rpBitToFin (!l.id)) (rpBitToFin l.id)))
      else l
    let l :=
      if tokenAt kind l ≠ none ∧ tokenAt kind r ≠ none then
        rpaSet kind l none
      else l
    let moveLeft := fun (l r : State psi kappa) =>
      match tokenAt kind r with
      | none => (l, r)
      | some t =>
          let c := decodeOffset psi t.1.1
          if hm1 : c = -1 then
            let next :=
              if t.2 = (1 : Fin 2) then
                rpMkToken (offsetPsiCode psi hpsi)
                  (rpBitToFin (!l.id)) (rpBitToFin l.id)
              else
                rpMkToken (offsetPsiCode psi hpsi)
                  (rpBitToFin l.id) (0 : Fin 2)
            let l := rpaSet kind l (some next)
            let r := rpaSet kind r none
            (l, r)
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid psi (by omega) t.1.1
            let nextOffset :=
              encodeOffset psi (c + 1) (by
                rcases hc with hn | hp
                · left
                  omega
                · exfalso
                  omega)
            let l := rpaSet kind l
              (some (rpMkToken nextOffset t.1.2 t.2))
            let r := rpaSet kind r none
            (l, r)
          else
            (l, r)
    match tokenAt kind l with
    | none => moveLeft l r
    | some t =>
        let c := decodeOffset psi t.1.1
        if hc1 : c = 1 then
          let bit := t.1.2.val == 1
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              rpaLeaderBirth r
            else if r.mode = false then
              { r with id := bit }
            else r
          let r := rpaSet kind r
            (some (rpMkToken (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2))
          let l := rpaSet kind l none
          (l, r)
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid psi (by omega) t.1.1
          let nextOffset :=
            encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega)
          let r := rpaSet kind r
            (some (rpMkToken nextOffset t.1.2 t.2))
          let l := rpaSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)

private theorem rpaMove_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    rpaMove hpsi kind l r = moveToken hpsi kind l r := by
  cases kind <;> rfl

private theorem rpaClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (rpaClear kind q).mode = q.mode ∧
      (rpaClear kind q).id = q.id ∧
      (rpaClear kind q).last = q.last := by
  unfold rpaClear
  cases tokenAt kind q with
  | none =>
      exact ⟨rfl, rfl, rfl⟩
  | some t =>
      dsimp only
      split
      · exact ⟨rfl, rfl, rfl⟩
      · cases kind <;> exact ⟨rfl, rfl, rfl⟩

private theorem rpaClear_self
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (ht : tokenAt kind q = some t)
    (hv : Lemma16AgedLocalValid kind q t) :
    rpaClear kind q = q := by
  unfold rpaClear
  rw [ht]
  dsimp only
  rw [if_pos hv]

private theorem rpaClear_none
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (h : lemma16AgedLiveValue kind q = none) :
    tokenAt kind (rpaClear kind q) = none := by
  unfold rpaClear
  cases ht : tokenAt kind q with
  | none =>
      exact ht
  | some t =>
      by_cases hv : Lemma16AgedLocalValid kind q t
      · simp [lemma16AgedLiveValue, ht, hv] at h
      · dsimp only
        rw [if_neg hv]
        cases kind <;> rfl

/-- Algorithm 3 line 20 on a Detect responder. -/
private theorem rpaMove_line20
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hll : l.last = false)
    (hrl : r.last = false)
    (ht : lemma16AgedLiveValue kind l = some t)
    (hc1 : decodeOffset psi (tokenCode t) = 1)
    (hrv : lemma16AgedLiveValue kind r = none)
    (hmode : r.mode = true)
    (hbit : tokenBitBool t ≠ r.id) :
    PPL.Elim.view4 (moveToken hpsi kind l r).2 =
      PPL.Safety.PeacefulProps.born4 := by
  rcases rpaLiveValue_some kind l t ht with ⟨htok, hval⟩
  have hcl : rpaClear kind l = l :=
    rpaClear_self kind l t htok hval
  have hcrTok : tokenAt kind (rpaClear kind r) = none :=
    rpaClear_none kind r hrv
  rcases rpaClear_fields kind r with ⟨hcrMode, hcrId, hcrLast⟩
  rw [← rpaMove_eq]
  unfold rpaMove
  simp only [hcl]
  generalize rpaClear kind r = r' at hcrTok hcrMode hcrId hcrLast ⊢
  have hr'mode : r'.mode = true := hcrMode.trans hmode
  have hr'last : r'.last = false := hcrLast.trans hrl
  have hbit' : (t.1.2.val == 1) ≠ r'.id := by
    rw [hcrId]
    exact hbit
  have hc1' : decodeOffset psi t.1.1 = 1 := hc1
  have hlast : l.last = false ∧ r'.last = false := ⟨hll, hr'last⟩
  rw [dif_pos hlast]
  have hnb :
      ¬ (l.dist.val = tokenD' psi kind ∧ tokenAt kind l = none) := by
    intro hh
    rw [htok] at hh
    cases hh.2
  rw [if_neg hnb]
  have hnc :
      ¬ (tokenAt kind l ≠ none ∧ tokenAt kind r' ≠ none) := by
    intro hh
    exact hh.2 hcrTok
  rw [if_neg hnc]
  try dsimp only
  rw [htok]
  try dsimp only
  rw [dif_pos hc1']
  have hcond : r'.mode = true ∧ (t.1.2.val == 1) ≠ r'.id :=
    ⟨hr'mode, hbit'⟩
  rw [if_pos hcond]
  cases kind <;> rfl

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 200000 in
/-- The responder keeps its ID through Algorithm 3 in Detect, unless it is
born. -/
private theorem rpaMove_detect_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hmode : r.mode = true) :
    (moveToken hpsi kind l r).2.mode = r.mode ∧
      ((moveToken hpsi kind l r).2.id = r.id ∨
        PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          PPL.Safety.PeacefulProps.born4) := by
  rcases rpaClear_fields kind r with ⟨hcrMode, hcrId, _hcrLast⟩
  rw [← rpaMove_eq]
  unfold rpaMove
  generalize rpaClear kind l = l' at *
  generalize rpaClear kind r = r' at hcrMode hcrId ⊢
  have hr'mode : r'.mode = true := hcrMode.trans hmode
  rw [← hcrMode, ← hcrId]
  cases kind <;>
    (try dsimp only) <;>
    repeat' split
  all_goals
    first
    | exact ⟨rfl, Or.inl rfl⟩
    | exact ⟨rfl, Or.inr rfl⟩
    | (exfalso; simp_all; done)
    | simp_all [rpaSet, rpaLeaderBirth, PPL.Elim.view4,
        PPL.Safety.PeacefulProps.born4]

/-! ## DetermineMode / line 6 prefix: responder mode and ID -/

private theorem rpaDetermineMode_right_id
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (determineMode l r).2.id = r.id := by
  simp only [determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals rfl

private theorem rpaPre_right_mode_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2.mode =
        (determineMode l r).2.mode ∧
      (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2.id =
        (determineMode l r).2.id := by
  dsimp only [PPL.Safety.PeacefulProps.preTokenPair,
    createLeaderThroughLine6]
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

private theorem rpaRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 <= n)
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
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem rpaSelectedInput_black
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    lemma16AgedSelectedInput hpsi .black l r =
      PPL.Safety.PeacefulProps.preTokenPair hpsi l r := by
  rfl

private theorem rpaSelectedInput_white
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    lemma16AgedSelectedInput hpsi .white l r =
      moveToken hpsi .black
        (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).1
        (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2 := by
  rfl

/-! ## Line-20 birth survives to a CPB post state (copied from DetectBirth) -/

private theorem rpFin3Cases
    (b : Fin 3) :
    b = (0 : Fin 3) \/
      b = (1 : Fin 3) \/
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

private theorem rpRowERightBorn
    (l : PPL.Elim.Cell4) :
    (PPL.Elim.rowE
      l PPL.Safety.PeacefulProps.born4).2 =
        PPL.Safety.PeacefulProps.born4 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases rpFin3Cases lb with
      h0 | h12
  · rw [h0]
    cases ll <;>
      cases lsh <;>
      cases lsb <;>
      simp
        [PPL.Safety.PeacefulProps.born4,
          PPL.Elim.rowE]
  · rcases h12 with h1 | h2
    · rw [h1]
      cases ll <;>
        cases lsh <;>
        cases lsb <;>
        simp
          [PPL.Safety.PeacefulProps.born4,
            PPL.Elim.rowE]
    · rw [h2]
      cases ll <;>
        cases lsh <;>
        cases lsb <;>
        simp
          [PPL.Safety.PeacefulProps.born4,
            PPL.Elim.rowE]

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 200000 in
/--
Physical c=+1 mismatch forces CPB after the step.

If the selected-colour Algorithm-3 input pair takes the c=1 service with a
token whose bit differs from the responder's pre-step ID, then Algorithm 3
line 20 (in Detect) gives the responder the shielded born view; the white
pass, if any, and Algorithm 5 keep it, and one-step AllLivePeaceful closure
plus the surviving leader give CPB.
-/
private theorem rpC1MismatchCPB
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hdist : DistReadyCapped ring G.phys)
    (t : TokenData psi)
    (hll :
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).1.last = false)
    (hrl :
      (lemma16AgedSelectedInput hpsi kind
        (G.phys e) (G.phys (ring.rightNeighbor e))).2.last = false)
    (hlv :
      lemma16AgedLiveValue kind
        (lemma16AgedSelectedInput hpsi kind
          (G.phys e) (G.phys (ring.rightNeighbor e))).1 =
        some t)
    (hrv :
      lemma16AgedLiveValue kind
        (lemma16AgedSelectedInput hpsi kind
          (G.phys e) (G.phys (ring.rightNeighbor e))).2 =
        none)
    (hc1 : decodeOffset psi (tokenCode t) = 1)
    (hmismatch :
      tokenBitBool t ≠ (G.phys (ring.rightNeighbor e)).id) :
    CPB ring (ghostStep hpsi ring step G e).phys := by
  let rsite := ring.rightNeighbor e
  let l : State psi kappa := G.phys e
  let r : State psi kappa := G.phys rsite
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  let b :=
    PPL.moveToken hpsi .black p.1 p.2
  let w :=
    PPL.moveToken hpsi .white b.1 b.2

  have hlead : l.leader = false :=
    hdist.1.1.2.1 e
  have hlsig : l.signalR.val = 0 :=
    detectStep_signalFree_at G.phys hdist.1.1.2.2.1 e
  have hrsig : r.signalR.val = 0 :=
    detectStep_signalFree_at G.phys hdist.1.1.2.2.1 rsite
  have hlclock : l.clock.val = kappa := hdist.1.2 e
  have hrclock : r.clock.val = kappa := hdist.1.2 rsite
  have hdm :=
    detectStep_determineMode_capped
      hpsi l r hlead hlsig hrsig hlclock hrclock
  dsimp only at hdm
  have hdmode : (determineMode l r).2.mode = true :=
    hdm.2.2.2.1
  rcases rpaPre_right_mode_id hpsi l r with ⟨hpmode0, hpid0⟩
  have hpmode : p.2.mode = true := hpmode0.trans hdmode
  have hpid : p.2.id = r.id :=
    hpid0.trans (rpaDetermineMode_right_id l r)

  have hwview :
      PPL.Elim.view4 w.2 =
        PPL.Safety.PeacefulProps.born4 := by
    cases kind with
    | black =>
        have hll : p.1.last = false := hll
        have hrl : p.2.last = false := hrl
        have hlv : lemma16AgedLiveValue .black p.1 = some t := hlv
        have hrv : lemma16AgedLiveValue .black p.2 = none := hrv
        have hbit : tokenBitBool t ≠ p.2.id := by
          rw [hpid]
          exact hmismatch
        have hbview :
            PPL.Elim.view4 b.2 =
              PPL.Safety.PeacefulProps.born4 :=
          rpaMove_line20 hpsi .black p.1 p.2 t
            hll hrl hlv hc1 hrv hpmode hbit
        have hwcases :=
          PPL.moveToken_view4_cases
            hpsi PPL.TokenKind.white b.1 b.2
        rcases hwcases.2 with hsame | hborn
        · exact hsame.trans hbview
        · simpa [PPL.Safety.PeacefulProps.born4]
            using hborn
    | white =>
        have hll : (moveToken hpsi .black p.1 p.2).1.last = false := hll
        have hrl : (moveToken hpsi .black p.1 p.2).2.last = false := hrl
        have hlv :
            lemma16AgedLiveValue .white
              (moveToken hpsi .black p.1 p.2).1 = some t := hlv
        have hrv :
            lemma16AgedLiveValue .white
              (moveToken hpsi .black p.1 p.2).2 = none := hrv
        rcases rpaMove_detect_id hpsi .black p.1 p.2 hpmode with
          ⟨hbmode, hbid | hbborn⟩
        · have hbit :
              tokenBitBool t ≠
                (moveToken hpsi .black p.1 p.2).2.id := by
            rw [hbid, hpid]
            exact hmismatch
          exact
            rpaMove_line20 hpsi .white
              (moveToken hpsi .black p.1 p.2).1
              (moveToken hpsi .black p.1 p.2).2
              t
              hll hrl hlv hc1 hrv
              (hbmode.trans hpmode) hbit
        · have hwcases :=
            PPL.moveToken_view4_cases
              hpsi PPL.TokenKind.white
              (moveToken hpsi .black p.1 p.2).1
              (moveToken hpsi .black p.1 p.2).2
          rcases hwcases.2 with hsame | hborn
          · exact hsame.trans hbborn
          · simpa [PPL.Safety.PeacefulProps.born4]
              using hborn

  have hcreate :
      PPL.createLeader hpsi l r = w := by
    rfl

  have hcreateView :
      PPL.Elim.view4
          (PPL.createLeader hpsi l r).2 =
        PPL.Safety.PeacefulProps.born4 := by
    rw [hcreate]
    exact hwview

  have hpplView :
      PPL.Elim.view4
          (PPL.ppl hpsi l r).2 =
        PPL.Safety.PeacefulProps.born4 := by
    change
      PPL.Elim.view4
          (PPL.eliminateLeaders
            (PPL.createLeader hpsi l r).1
            (PPL.createLeader hpsi l r).2).2 =
        PPL.Safety.PeacefulProps.born4
    calc
      PPL.Elim.view4
          (PPL.eliminateLeaders
            (PPL.createLeader hpsi l r).1
            (PPL.createLeader hpsi l r).2).2 =
          (PPL.Elim.rowE
            (PPL.Elim.view4
              (PPL.createLeader hpsi l r).1)
            (PPL.Elim.view4
              (PPL.createLeader hpsi l r).2)).2 := by
            exact
              PPL.Elim.view4_eliminateLeaders_right
                (PPL.createLeader hpsi l r).1
                (PPL.createLeader hpsi l r).2
      _ =
          (PPL.Elim.rowE
            (PPL.Elim.view4
              (PPL.createLeader hpsi l r).1)
            PPL.Safety.PeacefulProps.born4).2 := by
            rw [hcreateView]
      _ = PPL.Safety.PeacefulProps.born4 :=
        rpRowERightBorn
          (PPL.Elim.view4
            (PPL.createLeader hpsi l r).1)

  have hpplLeader :
      (PPL.ppl hpsi l r).2.leader = true := by
    have hv :=
      congrArg
        (fun q : PPL.Elim.Cell4 => q.leader)
        hpplView
    simpa
      [PPL.Elim.view4,
        PPL.Safety.PeacefulProps.born4]
      using hv

  have hne :
      rsite ≠ e := by
    exact rpRightNeighborNe hn3 ring e

  have htrans :
      PPL.transition psi kappa l r =
        PPL.ppl hpsi l r :=
    PPL.transition_eq_ppl hpsi l r

  have hpairLeader :
      (PPL.transition psi kappa l r).2.leader =
        true := by
    rw [htrans]
    exact hpplLeader

  have hstepLeader :
      (PopulationProtocol.step
        (PPL.protocol psi kappa)
        ring G.phys e rsite).leader = true := by
    simpa
      [l, r, rsite,
        PopulationProtocol.step,
        PPL.protocol, hne]
      using hpairLeader

  have hghostLeader :
      ((PPL.ghostStep
        hpsi ring step G e).phys rsite).leader =
        true := by
    rw [PPL.ghostStep_phys_export
      hpsi ring step G e]
    exact hstepLeader

  have hpeace0 :
      AllLivePeaceful ring G.phys :=
    hdist.1.1.1

  have hpeacePost :
      AllLivePeaceful ring
        (PPL.ghostStep
          hpsi ring step G e).phys := by
    rw [PPL.ghostStep_phys_export
      hpsi ring step G e]
    exact
      allLivePeaceful_step_closed
        hn3 hpsi ring G.phys e hpeace0

  exact
    cpb_of_allLivePeaceful_hasLeader
      ring
      (PPL.ghostStep
        hpsi ring step G e).phys
      hpeacePost
      ⟨rsite, hghostLeader⟩

/-! ## The repaired c=+1 transport row -/

private theorem rpShiftRight_succ
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (d : Nat) :
    shiftRight ring x (d + 1) =
      ring.rightNeighbor (shiftRight ring x d) := by
  apply Fin.ext
  change (x.val + (d + 1)) % n =
    ((x.val + d) % n + 1) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem rpStage_c1
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k e : Fin n)
    (source z : GhostToken n psi)
    (q : Nat)
    (hstage :
      Lemma16FreshMacroStageAt ring k e source q)
    (hsrc :
      decodeOffset psi (tokenCode source.value) = 1)
    (hoff :
      decodeOffset psi (tokenCode z.value) =
        (1 : Int) - (((psi : Nat) : Int)))
    (hmoves :
      z.lmeta.moves = source.lmeta.moves + 1) :
    Lemma16FreshMacroStageAt
      ring k (ring.rightNeighbor e) z q := by
  unfold Lemma16FreshMacroStageAt at hstage ⊢
  dsimp only at hstage ⊢
  rw [hoff, hmoves]
  rw [hsrc] at hstage
  rcases hstage with ⟨x, hx, hp | hn⟩
  · rcases hp with ⟨_h1, _h2, h3, h4⟩
    refine ⟨x + 1, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hx, rpShiftRight_succ]
    · omega
    · omega
    · omega
    · omega
  · exfalso
    omega

private theorem rpPayloadCorrect_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (s : Fin n)
    (x : Nat)
    (t t' : TokenData psi)
    (hb : tokenBitBool t' = tokenBitBool t)
    (hc : tokenCarryBool t' = tokenCarryBool t)
    (h : payloadCorrect ring C s x t) :
    payloadCorrect ring C s x t' := by
  unfold payloadCorrect at h ⊢
  dsimp only at h ⊢
  rw [hb, hc]
  exact h

private theorem rpNoPrior_pre
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (lid : LineageId n)
    (h :
      Lemma16NoPriorCompletionId
        (ghostStep hpsi ring step G e) lid) :
    Lemma16NoPriorCompletionId G lid := by
  intro m hm
  apply h m
  simp only [ghostStep, List.mem_append]
  exact .inl (.inl hm)

/--
`Lemma16AgedC1OwnerRow` with the physical certificate.

The old initiator owner satisfies the pre live invariant at some q<psi
(post no-prior gives pre no-prior).  The macro stage moves one edge right and
turns to c=1-psi; payload and prefix are unchanged.  For the new negative
latch: the border geometry identifies the responder with `b+q`, IDs are
frozen to Cepoch, and the payload gives `bit = expectedAddOneBit k q`.  If
the bit differed from the responder ID, `rpC1MismatchCPB` would make the
post state CPB, contradicting the premise.
-/
def Lemma16AgedC1OwnerRowPhys : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi ->
    LastReadyCapped ring G.phys ->
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    Not
      (CPB ring
        (ghostStep hpsi ring step G e).phys) ->
    forall (i : Fin n)
      (z : GhostToken n psi)
      (t : Nat),
      z.lmeta.id = .born kind t ->
      z.lmeta.birthSite = k ->
      epoch <= t ->
      Lemma16NoPriorCompletionId
        (ghostStep hpsi ring step G e)
        z.lmeta.id ->
      Lemma16AgedC1PhysData
        hpsi ring kind G e i z ->
      Lemma16AgedLiveGoal
        ring Cepoch b k i z

theorem lemma16AgedC1OwnerRowPhys_proved :
    Lemma16AgedC1OwnerRowPhys := by
  intro n psi kappa hpsi hn3 ring Cepoch epoch b k kind step G e
  intro hgeom hready hinv hnot i z t hid hbs hepoch hprior d
  have hidEq : z.lmeta.id = d.source.lmeta.id := by
    rw [d.hmeta]
    rfl
  have hbsEq : z.lmeta.birthSite = d.source.lmeta.birthSite := by
    rw [d.hmeta]
    rfl
  have hmoves : z.lmeta.moves = d.source.lmeta.moves + 1 := by
    rw [d.hmeta]
    rfl
  have hpre :
      Lemma16NoPriorCompletionId G d.source.lmeta.id := by
    rw [← hidEq]
    exact rpNoPrior_pre hpsi ring step G e z.lmeta.id hprior
  rcases
      hinv.2 e d.source t d.howner
        (hidEq.symm.trans hid) (hbsEq.symm.trans hbs) hepoch hpre with
    ⟨q, hq, hstage, hpay, hprefix, _hlatch⟩
  have hresp :
      ring.rightNeighbor e = shiftRight ring b q :=
    lemma16FreshMacroStage_c1_responder_of_borderGeometry
      hpsi ring b k e d.source q hgeom hstage d.hsourceOffset
  have hmatch :
      tokenBitBool d.source.value =
        (G.phys (ring.rightNeighbor e)).id := by
    refine Classical.byContradiction ?_
    intro hne
    exact hnot
      (rpC1MismatchCPB hpsi hn3 ring kind step G e hready.1
        d.source.value d.hinitLast d.hrespLast d.hinitLive
        d.hrespLive d.hsourceOffset hne)
  have hi : i = ring.rightNeighbor e := d.hsite
  subst hi
  refine ⟨q, hq, ?_, ?_, hprefix, ?_⟩
  · exact rpStage_c1 hpsi ring k e d.source z q hstage
      d.hsourceOffset d.hpostOffset hmoves
  · exact rpPayloadCorrect_congr ring Cepoch k q
      d.source.value z.value d.hbit d.hcarry hpay
  · intro _hneg
    rw [← hresp, ← hinv.1 (ring.rightNeighbor e), ← hmatch]
    unfold payloadCorrect at hpay
    exact hpay.1

/-! ## The live literal aged row -/

theorem lemma16PostEpochFreshSelectedLiveLiteralAgedRow_proved :
    Lemma16PostEpochFreshSelectedLiveLiteralAgedRow := by
  have hcases : Lemma16AgedSelectedOwnerCaseRowPhys :=
    lemma16AgedSelectedOwnerCaseRowPhys_proved
  have hordinary : Lemma16AgedOrdinaryOwnerRow :=
    lemma16AgedOrdinaryOwnerRow_proved
  have hc1 : Lemma16AgedC1OwnerRowPhys :=
    lemma16AgedC1OwnerRowPhys_proved
  have hnegOne : Lemma16AgedNegOneOwnerRow :=
    lemma16AgedNegOneOwnerRow_proved
  unfold Lemma16AgedSelectedOwnerCaseRowPhys at hcases
  unfold Lemma16AgedOrdinaryOwnerRow at hordinary
  unfold Lemma16AgedC1OwnerRowPhys at hc1
  unfold Lemma16AgedNegOneOwnerRow at hnegOne
  unfold Lemma16PostEpochFreshSelectedLiveLiteralAgedRow

  intro n psi kappa
  intro hpsi hn3 ring Cepoch epoch b k kind
  intro step G e
  intro hgeom hready hinv hage
  dsimp only
  intro hnot
  intro i z t
  intro hpair howner hid hsite hepoch hprior

  rcases
      hcases
        hpsi hn3 ring kind step G e
        hready i z hpair howner with
    ⟨hcase⟩

  cases hcase with
  | ordinary hord =>
      exact
        hordinary
          hpsi ring Cepoch epoch b k kind
          step G e
          hinv
          i z t
          hid hsite hepoch hprior
          hord
  | c1 hturn =>
      exact
        hc1
          hpsi hn3 ring Cepoch epoch b k kind
          step G e
          hgeom hready hinv hnot
          i z t
          hid hsite hepoch hprior
          hturn
  | negOne hturn =>
      exact
        hnegOne
          hpsi ring Cepoch epoch b k kind
          step G e
          hinv hage
          i z t
          hid hsite hepoch hprior
          hturn

/-! ## The refutation witness violates the new field

In the witness of `lemma16AgedC1OwnerRow_false` (n=4, psi=2, kappa=1, e=1,
black), no agent carries a physical token, so the initiator of the selected
input pair has no live black value, while `hinitLive` would require
`some source.value`.
-/

private def rpWState (i : Fin 4) : PPL.State 2 1 :=
  {
    leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB := none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }

theorem lemma16AgedC1PhysData_refuteWitness_initLive :
    lemma16AgedLiveValue .black
      (lemma16AgedSelectedInput (by decide : 2 ≤ 2) .black
        (rpWState ⟨1, by decide⟩) (rpWState ⟨2, by decide⟩)).1 =
      none := by
  decide

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16AgedSelectedOwnerCaseRowPhys_proved
#print axioms PPL.Convergence.ReachCPB.lemma16AgedC1OwnerRowPhys_proved
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSelectedLiveLiteralAgedRow_proved
#print axioms PPL.Convergence.ReachCPB.lemma16AgedC1PhysData_refuteWitness_initLive
