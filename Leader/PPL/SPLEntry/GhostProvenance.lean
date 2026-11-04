import Leader.PPL.SPLEntry.Ghost

/-!
# Prime ghost step: output provenance of the selected pair (part 3)

The prime ghost step `ghostStepPrime` updates the two interacting sites by a
private local function of `L18PrimeGhost`.  This file restates that function
publicly (`q3GMoveToken`, a verbatim copy; `q3_selected_eq` proves by `rfl`
that the prime ghost step uses exactly it) and proves the provenance of every
live ghost output (`q3_left_cases`, `q3_right_cases`): an output owner is
either the unchanged shadow of the pre-owner at the same site, or the bump of
the pre-owner at the other site (or of a fresh birth at the initiator) by one
explicit Algorithm-3 move, with lineage id, birth site and birth step kept and
the move count increased by one.

This replaces the physical/ghost old-image linking: the payload invariant of
fresh lineages can be carried on the ghost values directly, with no appeal to
the physical `SPLPostTokenOldImage` witness.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false

open PPL
open PPL.Probability


def q3GBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

def q3GMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

def q3GLocalValid
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

instance instDecidableQ3GLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (q3GLocalValid kind q t) := by
  unfold q3GLocalValid
  infer_instance

/--
The pre-Algorithm-3 pair for P_PL prime.

This is the prefix of pprimeCreateLeader through Algorithm-2 line 9:
DetermineMode is literal, line 6 is suppressed, the line-4 distance is always
written, then last is updated from that written responder.
-/
def q3GPrelude
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let q := determineMode l r
  let tmp : Fin (2 * psi) :=
    if q.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(q.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩
  let r1 : State psi kappa :=
    { q.2 with dist := tmp }
  let l1 : State psi kappa :=
    if r1.leader = true then
      { q.1 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { q.1 with last := false }
    else
      { q.1 with last := r1.last }
  (l1, r1)

def q3GLiveShadow
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
              q3GLocalValid kind q t then
            some z
          else
            none

def q3GLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if q3GLocalValid kind q t then
        some t
      else
        none

def q3GBirth
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      q3GMkToken
        (offsetPsiCode psi hpsi)
        (q3GBitToFin (!idBit))
        (q3GBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

def q3GBumpTo
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
        { z.lmeta with moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if q3GLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

def q3GNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    q3GMkToken
      (offsetPsiCode psi hpsi)
      (q3GBitToFin (!sourceBit))
      (q3GBitToFin sourceBit)
  else
    q3GMkToken
      (offsetPsiCode psi hpsi)
      (q3GBitToFin sourceBit)
      (0 : Fin 2)

def q3GFinishMove
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
          q3GMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          q3GBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          q3GMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          q3GBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                q3GNegTurnNext hpsi l.id t
              let b :=
                q3GBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                q3GMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                q3GBumpTo kind l next gr0
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
              q3GNegTurnNext hpsi l.id t
            let b :=
              q3GBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              q3GMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              q3GBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

def q3GMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := q3GLiveValue kind l
  let rv0 := q3GLiveValue kind r
  let gl0 := q3GLiveShadow kind l gl
  let gr0 := q3GLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (q3GBirth
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (q3GBirth
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
    q3GFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩


/-- The prime ghost step's selected-pair update is `q3GMoveToken`. -/
theorem q3_selected_eq {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (step : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    ghostStepSelectedPair_prime hpsi ring step G e kind =
      match kind with
      | .black =>
          q3GMoveToken hpsi .black step e
            (q3GPrelude hpsi (G.phys e) (G.phys (ring.rightNeighbor e))).1
            (q3GPrelude hpsi (G.phys e) (G.phys (ring.rightNeighbor e))).2
            (ghostTokenAt .black G e)
            (ghostTokenAt .black G (ring.rightNeighbor e))
      | .white =>
          q3GMoveToken hpsi .white step e
            (pprimeMoveToken hpsi .black
              (q3GPrelude hpsi (G.phys e) (G.phys (ring.rightNeighbor e))).1
              (q3GPrelude hpsi (G.phys e) (G.phys (ring.rightNeighbor e))).2).1
            (pprimeMoveToken hpsi .black
              (q3GPrelude hpsi (G.phys e) (G.phys (ring.rightNeighbor e))).1
              (q3GPrelude hpsi (G.phys e) (G.phys (ring.rightNeighbor e))).2).2
            (ghostTokenAt .white G e)
            (ghostTokenAt .white G (ring.rightNeighbor e)) := by
  cases kind <;> rfl

/-! ## Provenance of the outputs -/

/-- A bumped owner: new value, same lineage metadata, one more move. -/
def q3Bump {n psi : Nat} (z0 : GhostToken n psi) (v : TokenData psi) :
    GhostToken n psi :=
  { value := v, lmeta := { z0.lmeta with moves := z0.lmeta.moves + 1 } }

/-- The right-moving Algorithm-3 value updates (`c = 1` bounce, `c ≥ 2` step). -/
def q3MoveR {psi : Nat} (hpsi : 2 ≤ psi) (t v : TokenData psi) : Prop :=
  (decodeOffset psi (tokenCode t) = 1 ∧
      v = q3GMkToken (offsetNegPsiPlusOneCode psi hpsi) t.1.2 t.2) ∨
    (2 ≤ decodeOffset psi (tokenCode t) ∧
      decodeOffset psi (tokenCode v) = decodeOffset psi (tokenCode t) - 1 ∧
      v.1.2 = t.1.2 ∧ v.2 = t.2)

/-- The left-moving Algorithm-3 value updates (`c = -1` turn, `c ≤ -2` step). -/
def q3MoveL {psi kappa : Nat} (hpsi : 2 ≤ psi) (l : State psi kappa)
    (t v : TokenData psi) : Prop :=
  (decodeOffset psi (tokenCode t) = -1 ∧ v = q3GNegTurnNext hpsi l.id t) ∨
    (decodeOffset psi (tokenCode t) ≤ -2 ∧
      decodeOffset psi (tokenCode v) = decodeOffset psi (tokenCode t) + 1 ∧
      v.1.2 = t.1.2 ∧ v.2 = t.2)

theorem q3_bump_live {n psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (v : TokenData psi) (g : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : (q3GBumpTo kind q v g).live = some z) :
    ∃ z0, g = some z0 ∧ z = q3Bump z0 v ∧ q3GLocalValid kind q v := by
  unfold q3GBumpTo at h
  rcases g with _ | z0
  · simp at h
  · dsimp only at h
    split at h
    · exact ⟨z0, rfl, (Option.some.inj h).symm, by assumption⟩
    · simp at h

theorem q3_shadow {n psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : q3GLiveShadow kind q g = some z) :
    g = some z ∧ tokenAt kind q = some z.value := by
  unfold q3GLiveShadow at h
  rcases g with _ | z0
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · rename_i t ht
      split at h
      · rename_i hc
        have := Option.some.inj h
        subst this
        exact ⟨rfl, by rw [ht, hc.1]⟩
      · simp at h

theorem q3_liveValue {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) (h : q3GLiveValue kind q = some t) :
    tokenAt kind q = some t := by
  unfold q3GLiveValue at h
  split at h
  · simp at h
  · rename_i t0 ht
    split at h
    · rw [ht, h]
    · simp at h

theorem q3_finish_right {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : (q3GFinishMove hpsi kind l r lv2 rv0 gl2 gr0).right = some z) :
    gr0 = some z ∨
      ∃ t v, lv2 = some t ∧ q3MoveR hpsi t v ∧
        (q3GBumpTo kind r v gl2).live = some z := by
  unfold q3GFinishMove at h
  rcases lv2 with _ | t
  · dsimp only at h
    rcases rv0 with _ | t'
    · exact Or.inl h
    · dsimp only at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · exact Or.inl h
  · dsimp only at h
    split at h
    · rename_i h1
      exact Or.inr ⟨t, _, rfl, Or.inl ⟨h1, rfl⟩, h⟩
    · split at h
      · rename_i h1 h2
        dsimp only at h
        refine Or.inr ⟨t, _, rfl, ?_, h⟩
        refine Or.inr ⟨h2, ?_, rfl, rfl⟩
        simp only [tokenCode, q3GMkToken]
        rw [decode_encode]
      · rcases rv0 with _ | t'
        · exact Or.inl h
        · dsimp only at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · exact Or.inl h

theorem q3_finish_left {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : (q3GFinishMove hpsi kind l r lv2 rv0 gl2 gr0).left = some z) :
    (gl2 = some z ∧ ∀ t, lv2 = some t → decodeOffset psi (tokenCode t) ≤ 0) ∨
      ∃ t v, rv0 = some t ∧ q3MoveL hpsi l t v ∧
        (q3GBumpTo kind l v gr0).live = some z := by
  unfold q3GFinishMove at h
  rcases lv2 with _ | t
  · dsimp only at h
    rcases rv0 with _ | t'
    · exact Or.inl ⟨h, fun t ht => by simp at ht⟩
    · dsimp only at h
      split at h
      · rename_i hm1
        exact Or.inr ⟨t', _, rfl, Or.inl ⟨hm1, rfl⟩, h⟩
      · split at h
        · rename_i hm1 hm2
          dsimp only at h
          refine Or.inr ⟨t', _, rfl, ?_, h⟩
          refine Or.inr ⟨hm2, ?_, rfl, rfl⟩
          simp only [tokenCode, q3GMkToken]
          rw [decode_encode]
        · exact Or.inl ⟨h, fun t ht => by simp at ht⟩
  · dsimp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i h1 h2
        have hle : decodeOffset psi (tokenCode t) ≤ 0 := by
          have hv := decodeOffset_valid psi (by omega) (tokenCode t)
          unfold ValidOffset at hv
          omega
        rcases rv0 with _ | t'
        · exact Or.inl ⟨h, fun t0 ht0 => by
            rw [← Option.some.inj ht0]; exact hle⟩
        · dsimp only at h
          split at h
          · rename_i hm1
            exact Or.inr ⟨t', _, rfl, Or.inl ⟨hm1, rfl⟩, h⟩
          · split at h
            · rename_i hm1 hm2
              dsimp only at h
              refine Or.inr ⟨t', _, rfl, ?_, h⟩
              refine Or.inr ⟨hm2, ?_, rfl, rfl⟩
              simp only [tokenCode, q3GMkToken]
              rw [decode_encode]
            · exact Or.inl ⟨h, fun t0 ht0 => by
                rw [← Option.some.inj ht0]; exact hle⟩

/-- Provenance of the right (responder) output of the selected move. -/
theorem q3_right_cases {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step : Nat) (site : Fin n) (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : (q3GMoveToken hpsi kind step site l r gl gr).right = some z) :
    gr = some z ∨
      ∃ z0 v,
        (gl = some z0 ∨
          (z0 = q3GBirth hpsi kind step site l.id ∧
            l.dist.val = tokenD' psi kind ∧ l.last = false)) ∧
        q3MoveR hpsi z0.value v ∧ z = q3Bump z0 v ∧ q3GLocalValid kind r v := by
  unfold q3GMoveToken at h
  dsimp only at h
  split at h
  · rename_i hlast
    rcases q3_finish_right hpsi kind _ _ _ _ _ _ z h with hgr | ⟨t, v, hlv, hmv, hb⟩
    · exact Or.inl (q3_shadow kind r gr z hgr).1
    · obtain ⟨z0, hg2, hz, hLV⟩ := q3_bump_live kind r v _ z hb
      right
      by_cases hbc : (l.dist.val = tokenD' psi kind ∧ q3GLiveValue kind l = none)
      · simp only [if_pos hbc] at hg2 hlv
        by_cases hcol : ((some (q3GBirth hpsi kind step site l.id).value : Option (TokenData psi)) ≠ none ∧
            q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2 hlv
          have e1 := Option.some.inj hg2
          have e2 := Option.some.inj hlv
          subst e1
          refine ⟨_, v, Or.inr ⟨rfl, hbc.1, hlast.1⟩, ?_, hz, hLV⟩
          rw [e2]; exact hmv
      · simp only [if_neg hbc] at hg2 hlv
        by_cases hcol : (q3GLiveValue kind l ≠ none ∧ q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2 hlv
          have hsh := q3_shadow kind l gl z0 hg2
          have hlv' := q3_liveValue kind l t hlv
          have ht : z0.value = t := by
            rw [hsh.2] at hlv'; exact Option.some.inj hlv'
          refine ⟨z0, v, Or.inl hsh.1, ?_, hz, hLV⟩
          rw [ht]; exact hmv
  · exact Or.inl (q3_shadow kind r gr z h).1

/-- Provenance of the left (initiator) output of the selected move. -/
theorem q3_left_cases {n psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step : Nat) (site : Fin n) (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) (z : GhostToken n psi)
    (h : (q3GMoveToken hpsi kind step site l r gl gr).left = some z) :
    gl = some z ∨
      ∃ z0 v, gr = some z0 ∧ q3MoveL hpsi l z0.value v ∧ z = q3Bump z0 v ∧
        q3GLocalValid kind l v := by
  unfold q3GMoveToken at h
  dsimp only at h
  split at h
  · rcases q3_finish_left hpsi kind _ _ _ _ _ _ z h with ⟨hg2, hle⟩ | ⟨t, v, hrv, hmv, hb⟩
    · left
      by_cases hbc : (l.dist.val = tokenD' psi kind ∧ q3GLiveValue kind l = none)
      · simp only [if_pos hbc] at hg2 hle
        by_cases hcol : ((some (q3GBirth hpsi kind step site l.id).value : Option (TokenData psi)) ≠ none ∧
            q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hle
          exfalso
          have := hle (q3GBirth hpsi kind step site l.id).value rfl
          simp only [q3GBirth, tokenCode, q3GMkToken] at this
          rw [decodeOffset_psi psi hpsi] at this
          omega
      · simp only [if_neg hbc] at hg2
        by_cases hcol : (q3GLiveValue kind l ≠ none ∧ q3GLiveValue kind r ≠ none)
        · rw [if_pos hcol] at hg2
          cases hg2
        · rw [if_neg hcol] at hg2
          exact (q3_shadow kind l gl z hg2).1
    · obtain ⟨z0, hg0, hz, hLV⟩ := q3_bump_live kind l v _ z hb
      have hsh := q3_shadow kind r gr z0 hg0
      have hrv' := q3_liveValue kind r t hrv
      have ht : z0.value = t := by
        rw [hsh.2] at hrv'; exact Option.some.inj hrv'
      right
      refine ⟨z0, v, hsh.1, ?_, hz, hLV⟩
      rw [ht]; exact hmv
  · exact Or.inl (q3_shadow kind l gl z h).1

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q3_right_cases
#print axioms PPL.Convergence.L18.q3_left_cases
