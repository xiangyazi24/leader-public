import Leader.PPL.Safety.PeacefulProps
import Leader.PPL.Safety.SPL
import Leader.PPL.TransitionFacts

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-
Restated verbatim, with the connectives written as ASCII And.  No Unicode conjunction/disjunction
notation is used in this declaration.
-/
def SPLAlgorithm3IdempotentIdRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    let p :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e)
          (C (ring.rightNeighbor e))
    let b :=
      PPL.moveToken hpsi .black p.1 p.2
    let w :=
      PPL.moveToken hpsi .white b.1 b.2
    And
      (p.1.leader = false ->
        w.1.leader = false)
      (And
        (p.2.leader = false ->
          w.2.leader = false)
        (And
          (w.1.id = p.1.id)
          (w.2.id = p.2.id)))

/-! -------------------------------------------------------------------------
    Small ring geometry
------------------------------------------------------------------------- -/

private theorem idRow_shiftRight_add
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) (a b : Nat) :
    shiftRight ring (shiftRight ring i a) b =
      shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

@[simp] private theorem idRow_shiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt i.isLt]

@[simp] private theorem idRow_shiftRight_n
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    shiftRight ring i n = i := by
  apply Fin.ext
  simp [shiftRight, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]

private theorem idRow_cyclicOffset_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    cyclicOffset ring root i < n := by
  unfold cyclicOffset
  exact Nat.mod_lt _ ring.hn

private theorem idRow_cyclicOffset_shiftRight_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) :
    cyclicOffset ring i (shiftRight ring i d) = d := by
  unfold cyclicOffset
  change ((i.val + d) % n + n - i.val) % n = d
  have hi : i.val < n := i.isLt
  have hn : 0 < n := ring.hn
  have hmod :
      (i.val + d) % n =
        if i.val + d < n then
          i.val + d
        else
          i.val + d - n := by
    by_cases h : i.val + d < n
    · rw [if_pos h, Nat.mod_eq_of_lt h]
    · rw [if_neg h]
      have hlt2 : i.val + d < 2 * n := by
        omega
      have hge : n <= i.val + d := by
        omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt
          (by omega : i.val + d - n < n)]
  rw [hmod]
  split
  · have h1 : i.val + d + n - i.val = d + n := by
      omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · have h1 : i.val + d - n + n - i.val = d := by
      omega
    rw [h1, Nat.mod_eq_of_lt hd]

private theorem idRow_shiftRight_cyclicOffset
    {n : Nat}
    (ring : DirectedRing n)
    (a b : Fin n) :
    shiftRight ring a
        (cyclicOffset ring a b) = b := by
  apply Fin.ext
  change
    (a.val +
        ((b.val + n - a.val) % n)) % n =
      b.val
  by_cases hab : a.val <= b.val
  · have heq :
        b.val + n - a.val =
          n + (b.val - a.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt
        (by omega : b.val - a.val < n)]
    have hsum :
        a.val + (b.val - a.val) = b.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt b.isLt]
  · have hlt :
        b.val + n - a.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        a.val + (b.val + n - a.val) =
          b.val + n := by
      omega
    rw [hsum, Nat.add_mod_right,
      Nat.mod_eq_of_lt b.isLt]

private theorem idRow_rightNeighbor_offset_of_ne_root
    {n : Nat}
    (ring : DirectedRing n)
    (root e : Fin n)
    (hne : ring.rightNeighbor e ≠ root) :
    cyclicOffset ring root
        (ring.rightNeighbor e) =
      cyclicOffset ring root e + 1 := by
  let x := cyclicOffset ring root e
  have hxlt : x < n := by
    exact idRow_cyclicOffset_lt ring root e
  have heq :
      e = shiftRight ring root x := by
    exact (idRow_shiftRight_cyclicOffset
      ring root e).symm
  have hr :
      ring.rightNeighbor e =
        shiftRight ring root (x + 1) := by
    calc
      ring.rightNeighbor e =
          shiftRight ring e 1 := rfl
      _ =
          shiftRight ring
            (shiftRight ring root x) 1 := by
              rw [heq]
      _ =
          shiftRight ring root (x + 1) :=
        idRow_shiftRight_add ring root x 1
  by_cases hx1 : x + 1 < n
  · rw [hr]
    simpa [x] using
      idRow_cyclicOffset_shiftRight_of_lt
        ring root (x + 1) hx1
  · have hxn : x + 1 = n := by
      omega
    have hroot :
        ring.rightNeighbor e = root := by
      rw [hr, hxn, idRow_shiftRight_n]
    exact False.elim (hne hroot)

private theorem idRow_inSegment_zero_of_offset_lt
    {n psi : Nat}
    (ring : DirectedRing n)
    (root i : Fin n)
    (hoff : cyclicOffset ring root i < psi) :
    InSegment ring root psi 0 i := by
  unfold InSegment
  dsimp only
  constructor
  · omega
  · have hn :
        cyclicOffset ring root i < n :=
      idRow_cyclicOffset_lt ring root i
    exact Nat.lt_min.mpr ⟨by omega, hn⟩

private theorem idRow_tokenTarget_one
    {n psi : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hc1 :
      decodeOffset psi (tokenCode t) = (1 : Int)) :
    tokenTargetSite ring e t =
      ring.rightNeighbor e := by
  have h :
      tokenTargetSite ring e t =
        shiftRight ring e 1 := by
    unfold tokenTargetSite
    rw [hc1]
    simp
  exact h

/-! -------------------------------------------------------------------------
    The Algorithm-2 prefix fields needed by this row
------------------------------------------------------------------------- -/

private theorem idRow_determineMode_frame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    And
      (d.1.dist = l.dist)
      (And
        (d.1.id = l.id)
        (And
          (tokenAt kind d.1 =
            tokenAt kind l)
          (And
            (d.2.last = r.last)
            (And
              (d.2.id = r.id)
              (And
                (tokenAt kind d.2 =
                  tokenAt kind r)
                (d.2.leader = r.leader)))))) := by
  cases kind <;>
    simp only [PPL.determineMode, tokenAt]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact
      ⟨rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩

private theorem idRow_line6_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    let s :=
      PPL.createLeaderThroughLine6 hpsi l r
    And
      (s.left.dist = d.1.dist)
      (And
        (s.left.id = d.1.id)
        (And
          (tokenAt kind s.left =
            tokenAt kind d.1)
          (And
            (s.right.last = d.2.last)
            (And
              (s.right.id = d.2.id)
              (And
                (tokenAt kind s.right =
                  tokenAt kind d.2)
                (d.2.leader = true ->
                  s.right.leader = true)))))) := by
  dsimp only
  unfold PPL.createLeaderThroughLine6
  dsimp only
  split
  · cases kind <;>
      exact
        ⟨rfl, rfl, rfl, rfl,
          rfl, rfl, by intro _; rfl⟩
  · cases kind <;>
      exact
        ⟨rfl, rfl, rfl, rfl,
          rfl, rfl, by intro h; exact h⟩

private theorem idRow_preToken_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi l r
    And
      (p.1.dist = l.dist)
      (And
        (tokenAt kind p.1 =
          tokenAt kind l)
        (And
          (p.2.last = r.last)
          (And
            (p.2.id = r.id)
            (r.leader = true ->
              p.1.last = true)))) := by
  let d := PPL.determineMode l r
  let s :=
    PPL.createLeaderThroughLine6 hpsi l r
  have hd0 :=
    idRow_determineMode_frame
      kind l r
  have hd :
      And
        (d.1.dist = l.dist)
        (And
          (d.1.id = l.id)
          (And
            (tokenAt kind d.1 =
              tokenAt kind l)
            (And
              (d.2.last = r.last)
              (And
                (d.2.id = r.id)
                (And
                  (tokenAt kind d.2 =
                    tokenAt kind r)
                  (d.2.leader = r.leader)))))) := by
    simpa [d] using hd0
  have hs0 :=
    idRow_line6_frame
      hpsi kind l r
  have hs :
      And
        (s.left.dist = d.1.dist)
        (And
          (s.left.id = d.1.id)
          (And
            (tokenAt kind s.left =
              tokenAt kind d.1)
            (And
              (s.right.last = d.2.last)
              (And
                (s.right.id = d.2.id)
                (And
                  (tokenAt kind s.right =
                    tokenAt kind d.2)
                  (d.2.leader = true ->
                    s.right.leader = true)))))) := by
    simpa [d, s] using hs0

  let r1 : State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  let l1 : State psi kappa :=
    if r1.leader = true then
      { s.left with last := true }
    else if
        Or (r1.dist.val = 0)
          (r1.dist.val = psi) then
      { s.left with last := false }
    else
      { s.left with last := r1.last }

  have hr1Last :
      r1.last = r.last := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hs.2.2.2.1, hd.2.2.2.1]
    · simp [r1, hm, hs.2.2.2.1, hd.2.2.2.1]
  have hr1Id :
      r1.id = r.id := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hs.2.2.2.2.1, hd.2.2.2.2.1]
    · simp [r1, hm, hs.2.2.2.2.1, hd.2.2.2.2.1]
  have hsDist :
      s.left.dist = l.dist :=
    hs.1.trans hd.1
  have hl1Dist :
      l1.dist = l.dist := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead] using hsDist
    · by_cases hboundary :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hboundary] using hsDist
      · simpa [l1, hlead, hboundary] using hsDist
  have hsToken :
      tokenAt kind s.left =
        tokenAt kind l :=
    hs.2.2.1.trans hd.2.2.1
  have hl1Token :
      tokenAt kind l1 =
        tokenAt kind l := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead, tokenAt] using hsToken
    · by_cases hboundary :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hboundary, tokenAt]
          using hsToken
      · simpa [l1, hlead, hboundary, tokenAt]
          using hsToken
  have hrightTrue :
      r.leader = true ->
        r1.leader = true := by
    intro hr
    have hdtrue :
        d.2.leader = true := by
      rw [hd.2.2.2.2.2.2, hr]
    have hstrue :
        s.right.leader = true :=
      hs.2.2.2.2.2.2 hdtrue
    by_cases hm : s.right.mode = false
    · simpa [r1, hm] using hstrue
    · simpa [r1, hm] using hstrue
  have hrootBlock :
      r.leader = true ->
        l1.last = true := by
    intro hr
    have hr1 := hrightTrue hr
    simp [l1, hr1]

  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  have hpdef : p = (l1, r1) := by
    rfl
  change
    p.1.dist = l.dist ∧
      tokenAt kind p.1 = tokenAt kind l ∧
      p.2.last = r.last ∧
      p.2.id = r.id ∧
      (r.leader = true → p.1.last = true)
  rw [hpdef]
  exact
    ⟨hl1Dist, hl1Token,
      hr1Last, hr1Id, hrootBlock⟩

/-! -------------------------------------------------------------------------
    A public-name mirror of the literal selected-color MoveToken row
------------------------------------------------------------------------- -/

private def idRowBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def idRowMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) :
    TokenData psi :=
  ((offset, bit), carry)

private def idRowLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And
        (((psi : Nat) : Int) <= target)
        (target <=
          (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And
        (1 <= target)
        (target <=
          (((psi - 1 : Nat)) : Int))))

private instance instDecidableIdRowLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (idRowLocalValid kind q t) := by
  unfold idRowLocalValid
  infer_instance

private def idRowClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if idRowLocalValid kind q t then
        q
      else
        PPL.sourceSet kind q none

private theorem idRow_sourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    PPL.sourceClear kind q =
      idRowClearInvalid kind q := by
  cases kind <;> rfl

@[simp] private theorem idRow_sourceSet_tokenAt
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind
      (PPL.sourceSet kind q t) = t := by
  cases kind <;> rfl

@[simp] private theorem idRow_sourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (PPL.sourceSet kind q t).id = q.id := by
  cases kind <;> rfl

@[simp] private theorem idRow_sourceSet_leader
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (PPL.sourceSet kind q t).leader =
      q.leader := by
  cases kind <;> rfl

@[simp] private theorem idRow_sourceSet_last
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (PPL.sourceSet kind q t).last = q.last := by
  cases kind <;> rfl

private theorem idRow_sourceClear_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).id = q.id := by
  rw [idRow_sourceClear_eq]
  unfold idRowClearInvalid
  cases htok : tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv :
          idRowLocalValid kind q t
      · simp only [if_pos hv, dif_pos hv]
      · simp only [if_neg hv, dif_neg hv]
        exact idRow_sourceSet_id kind q none

private theorem idRow_sourceClear_leader
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).leader =
      q.leader := by
  rw [idRow_sourceClear_eq]
  unfold idRowClearInvalid
  cases htok : tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv :
          idRowLocalValid kind q t
      · simp only [if_pos hv, dif_pos hv]
      · simp only [if_neg hv, dif_neg hv]
        exact idRow_sourceSet_leader kind q none

private theorem idRow_sourceClear_last
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).last =
      q.last := by
  rw [idRow_sourceClear_eq]
  unfold idRowClearInvalid
  cases htok : tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv :
          idRowLocalValid kind q t
      · simp only [if_pos hv, dif_pos hv]
      · simp only [if_neg hv, dif_neg hv]
        exact idRow_sourceSet_last kind q none

private theorem idRow_sourceClear_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt kind
          (PPL.sourceClear kind q) =
        some t) :
    And
      (tokenAt kind q = some t)
      (idRowLocalValid kind q t) := by
  rw [idRow_sourceClear_eq] at h
  unfold idRowClearInvalid at h
  cases hq : tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      by_cases hv :
          idRowLocalValid kind q u
      · simp only [hq, if_pos hv, dif_pos hv] at h
        have hut : u = t := by
          exact Option.some.inj h
        subst u
        exact ⟨rfl, hv⟩
      · simp only [hq, if_neg hv, dif_neg hv] at h
        rw [idRow_sourceSet_tokenAt] at h
        contradiction

private def idRowNegTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    idRowMkToken
      (offsetPsiCode psi hpsi)
      (idRowBitToFin (!sourceBit))
      (idRowBitToFin sourceBit)
  else
    idRowMkToken
      (offsetPsiCode psi hpsi)
      (idRowBitToFin sourceBit)
      (0 : Fin 2)

private def idRowFreshenLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l : State psi kappa) :
    State psi kappa :=
  if And
      (l.dist.val = tokenD' psi kind)
      (tokenAt kind l = none) then
    PPL.sourceSet kind l
      (some
        (idRowMkToken
          (offsetPsiCode psi hpsi)
          (idRowBitToFin (!l.id))
          (idRowBitToFin l.id)))
  else
    l

private def idRowCollisionLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa :=
  if And
      (tokenAt kind l ≠ none)
      (tokenAt kind r ≠ none) then
    PPL.sourceSet kind l none
  else
    l

private def idRowMoveLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  match tokenAt kind r with
  | none =>
      (l, r)
  | some t =>
      let c :=
        decodeOffset psi (tokenCode t)
      if hm1 : c = -1 then
        let next :=
          idRowNegTurnNext hpsi l.id t
        let l :=
          PPL.sourceSet kind l (some next)
        let r :=
          PPL.sourceSet kind r none
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
          PPL.sourceSet kind l
            (some
              (idRowMkToken
                nextOffset t.1.2 t.2))
        let r :=
          PPL.sourceSet kind r none
        (l, r)
      else
        (l, r)

private def idRowMoveRightOne
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi) :
    State psi kappa × State psi kappa :=
  let bit := tokenBitBool t
  let r :=
    if And
        (r.mode = true)
        (bit ≠ r.id) then
      PPL.sourceBirth r
    else if r.mode = false then
      { r with id := bit }
    else
      r
  let r :=
    PPL.sourceSet kind r
      (some
        (idRowMkToken
          (offsetNegPsiPlusOneCode psi hpsi)
          t.1.2 t.2))
  let l :=
    PPL.sourceSet kind l none
  (l, r)

private def idRowMoveTokenCore
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  if hlast :
      And (l.last = false) (r.last = false) then
    let l :=
      idRowFreshenLeft hpsi kind l
    let l :=
      idRowCollisionLeft kind l r
    match tokenAt kind l with
    | none =>
        idRowMoveLeft hpsi kind l r
    | some t =>
        let c :=
          decodeOffset psi (tokenCode t)
        if hc1 : c = 1 then
          idRowMoveRightOne hpsi kind l r t
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
            PPL.sourceSet kind r
              (some
                (idRowMkToken
                  nextOffset t.1.2 t.2))
          let l :=
            PPL.sourceSet kind l none
          (l, r)
        else
          idRowMoveLeft hpsi kind l r
  else
    (l, r)

private def idRowMoveToken
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  idRowMoveTokenCore hpsi kind
    (PPL.sourceClear kind l)
    (PPL.sourceClear kind r)

private theorem idRowMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    idRowMoveToken hpsi kind l r =
      PPL.moveToken hpsi kind l r := by
  cases kind <;> rfl

private def idRowSelectedLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa :=
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r
  idRowCollisionLeft kind
    (idRowFreshenLeft hpsi kind l0) r0

private theorem idRow_selected_c1_origin
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hsel :
      tokenAt kind
          (idRowSelectedLeft
            hpsi kind l r) =
        some t)
    (hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int)) :
    And
      (tokenAt kind l = some t)
      (idRowLocalValid kind l t) := by
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r
  let l1 :=
    idRowFreshenLeft hpsi kind l0
  let l2 :=
    idRowCollisionLeft kind l1 r0
  have hsel2 :
      tokenAt kind l2 = some t := by
    simpa [idRowSelectedLeft,
      l0, r0, l1, l2] using hsel

  by_cases hcol :
      And
        (tokenAt kind l1 ≠ none)
        (tokenAt kind r0 ≠ none)
  · have hnone :
        tokenAt kind l2 = none := by
      simp [l2, idRowCollisionLeft, hcol]
    rw [hnone] at hsel2
    contradiction
  · have hsel1 :
        tokenAt kind l1 = some t := by
      simpa [l2, idRowCollisionLeft, hcol]
        using hsel2
    by_cases hborn :
        And
          (l0.dist.val = tokenD' psi kind)
          (tokenAt kind l0 = none)
    · let fresh : TokenData psi :=
        idRowMkToken
          (offsetPsiCode psi hpsi)
          (idRowBitToFin (!l0.id))
          (idRowBitToFin l0.id)
      have hfresh :
          tokenAt kind l1 = some fresh := by
        simp [l1, idRowFreshenLeft,
          hborn, fresh]
      rw [hfresh] at hsel1
      have htf : t = fresh := by
        exact Option.some.inj hsel1.symm
      subst t
      have hdecode :
          decodeOffset psi
              (tokenCode fresh) =
            ((psi : Nat) : Int) := by
        simpa [fresh, idRowMkToken,
          tokenCode] using
          decodeOffset_psi psi hpsi
      rw [hdecode] at hc1
      omega
    · have hsel0 :
          tokenAt kind l0 = some t := by
        simpa [l1, idRowFreshenLeft,
          hborn] using hsel1
      exact
        idRow_sourceClear_some
          kind l t
          (by simpa [l0] using hsel0)

/-! -------------------------------------------------------------------------
    The only branch that can write leader/id
------------------------------------------------------------------------- -/

private def idRowLeaderIdFrame
    {psi kappa : Nat}
    (l r : State psi kappa)
    (q : State psi kappa × State psi kappa) :
    Prop :=
  And
    (q.1.leader = l.leader)
    (And
      (q.2.leader = r.leader)
      (And
        (q.1.id = l.id)
        (q.2.id = r.id)))

private theorem idRow_freshen_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l : State psi kappa) :
    And
      ((idRowFreshenLeft
        hpsi kind l).leader = l.leader)
      ((idRowFreshenLeft
        hpsi kind l).id = l.id) := by
  unfold idRowFreshenLeft
  by_cases h :
      And
        (l.dist.val = tokenD' psi kind)
        (tokenAt kind l = none)
  · simp [h]
  · simp [h]

private theorem idRow_collision_frame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      ((idRowCollisionLeft
        kind l r).leader = l.leader)
      ((idRowCollisionLeft
        kind l r).id = l.id) := by
  unfold idRowCollisionLeft
  by_cases h :
      And
        (tokenAt kind l ≠ none)
        (tokenAt kind r ≠ none)
  · simp [h]
  · simp [h]

private theorem idRow_moveLeft_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    idRowLeaderIdFrame l r
      (idRowMoveLeft hpsi kind l r) := by
  unfold idRowMoveLeft
  cases htok : tokenAt kind r with
  | none =>
      exact ⟨rfl, rfl, rfl, rfl⟩
  | some t =>
      dsimp only
      by_cases hm1 :
          decodeOffset psi (tokenCode t) = -1
      · simp only [if_pos hm1, dif_pos hm1]
        try dsimp only
        exact
          ⟨idRow_sourceSet_leader kind l _,
            idRow_sourceSet_leader kind r _,
            idRow_sourceSet_id kind l _,
            idRow_sourceSet_id kind r _⟩
      · simp only [if_neg hm1, dif_neg hm1]
        by_cases hm2 :
            decodeOffset psi (tokenCode t) <= -2
        · simp only [if_pos hm2, dif_pos hm2]
          try dsimp only
          exact
          ⟨idRow_sourceSet_leader kind l _,
            idRow_sourceSet_leader kind r _,
            idRow_sourceSet_id kind l _,
            idRow_sourceSet_id kind r _⟩
        · simp only [if_neg hm2, dif_neg hm2]
          exact ⟨rfl, rfl, rfl, rfl⟩

private theorem idRow_moveRightOne_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hbit : tokenBitBool t = r.id) :
    idRowLeaderIdFrame l r
      (idRowMoveRightOne
        hpsi kind l r t) := by
  unfold idRowMoveRightOne
  dsimp only
  have hbirth :
      Not
        (And
          (r.mode = true)
          (tokenBitBool t ≠ r.id)) := by
    intro h
    exact h.2 hbit
  simp only [if_neg hbirth, dif_neg hbirth]
  by_cases hm : r.mode = false
  · simp only [if_pos hm, dif_pos hm]
    try dsimp only
    first
      | exact
          ⟨idRow_sourceSet_leader kind l _,
            idRow_sourceSet_leader kind _ _,
            idRow_sourceSet_id kind l _,
            idRow_sourceSet_id kind _ _⟩
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | simp [idRowLeaderIdFrame, hbit]
  · simp only [if_neg hm, dif_neg hm]
    try dsimp only
    first
      | exact
          ⟨idRow_sourceSet_leader kind l _,
            idRow_sourceSet_leader kind _ _,
            idRow_sourceSet_id kind l _,
            idRow_sourceSet_id kind _ _⟩
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | simp [idRowLeaderIdFrame, hbit]

private theorem idRow_moveTokenCore_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hsafe :
      forall (t : TokenData psi),
        l.last = false ->
        r.last = false ->
        tokenAt kind
            (idRowCollisionLeft kind
              (idRowFreshenLeft hpsi kind l) r) =
          some t ->
        decodeOffset psi (tokenCode t) =
          (1 : Int) ->
        tokenBitBool t = r.id) :
    idRowLeaderIdFrame l r
      (idRowMoveTokenCore
        hpsi kind l r) := by
  unfold idRowMoveTokenCore
  by_cases hlast :
      And (l.last = false) (r.last = false)
  · simp only [if_pos hlast, dif_pos hlast]
    try dsimp only
    generalize h1 :
      idRowFreshenLeft hpsi kind l = l1
    generalize h2 :
      idRowCollisionLeft kind l1 r = l2
    have hf1 :=
      idRow_freshen_frame hpsi kind l
    have hf2 :=
      idRow_collision_frame kind l1 r
    have hl1Leader :
        l1.leader = l.leader := by
      rw [← h1]
      exact hf1.1
    have hl1Id :
        l1.id = l.id := by
      rw [← h1]
      exact hf1.2
    have hl2Leader :
        l2.leader = l.leader := by
      calc
        l2.leader = l1.leader := by
          rw [← h2]
          exact hf2.1
        _ = l.leader := hl1Leader
    have hl2Id :
        l2.id = l.id := by
      calc
        l2.id = l1.id := by
          rw [← h2]
          exact hf2.2
        _ = l.id := hl1Id

    cases htok : tokenAt kind l2 with
    | none =>
        have hm :=
          idRow_moveLeft_frame
            hpsi kind l2 r
        exact
          ⟨hm.1.trans hl2Leader,
            hm.2.1,
            hm.2.2.1.trans hl2Id,
            hm.2.2.2⟩
    | some t =>
        dsimp only
        by_cases hc1 :
            decodeOffset psi
                (tokenCode t) = 1
        · simp only [if_pos hc1, dif_pos hc1]
          have htok0 := htok
          rw [← h2, ← h1] at htok0
          have hbit :=
            hsafe t hlast.1 hlast.2
              htok0 hc1
          have hm :=
            idRow_moveRightOne_frame
              hpsi kind l2 r t
              (by simpa [hl2Id] using hbit)
          exact
            ⟨hm.1.trans hl2Leader,
              hm.2.1,
              hm.2.2.1.trans hl2Id,
              hm.2.2.2⟩
        · simp only [if_neg hc1, dif_neg hc1]
          by_cases hc2 :
              2 <=
                decodeOffset psi
                  (tokenCode t)
          · simp only [if_pos hc2, dif_pos hc2]
            try dsimp only
            exact
              ⟨by
                  rw [idRow_sourceSet_leader]
                  exact hl2Leader,
                by
                  rw [idRow_sourceSet_leader],
                by
                  rw [idRow_sourceSet_id]
                  exact hl2Id,
                by
                  rw [idRow_sourceSet_id]⟩
          · simp only [if_neg hc2, dif_neg hc2]
            have hm :=
              idRow_moveLeft_frame
                hpsi kind l2 r
            exact
              ⟨hm.1.trans hl2Leader,
                hm.2.1,
                hm.2.2.1.trans hl2Id,
                hm.2.2.2⟩
  · simp only [if_neg hlast, dif_neg hlast]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem idRow_moveToken_frame_of_c1_safe
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hsafe :
      forall (t : TokenData psi),
        (PPL.sourceClear kind l).last = false ->
        (PPL.sourceClear kind r).last = false ->
        tokenAt kind
            (idRowSelectedLeft
              hpsi kind l r) =
          some t ->
        decodeOffset psi (tokenCode t) =
          (1 : Int) ->
        tokenBitBool t =
          (PPL.sourceClear kind r).id) :
    idRowLeaderIdFrame l r
      (PPL.moveToken hpsi kind l r) := by
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r
  have hcore :
      idRowLeaderIdFrame l0 r0
        (idRowMoveTokenCore
          hpsi kind l0 r0) := by
    apply idRow_moveTokenCore_frame
    intro t hl hr htok hc1
    exact
      hsafe t hl hr
        (by simpa
          [idRowSelectedLeft, l0, r0]
          using htok)
        hc1

  have hlLeader :
      l0.leader = l.leader := by
    simpa [l0] using
      idRow_sourceClear_leader kind l
  have hrLeader :
      r0.leader = r.leader := by
    simpa [r0] using
      idRow_sourceClear_leader kind r
  have hlId :
      l0.id = l.id := by
    simpa [l0] using
      idRow_sourceClear_id kind l
  have hrId :
      r0.id = r.id := by
    simpa [r0] using
      idRow_sourceClear_id kind r

  rw [← idRowMoveToken_eq
    hpsi kind l r]
  unfold idRowMoveToken
  exact
    ⟨hcore.1.trans hlLeader,
      hcore.2.1.trans hrLeader,
      hcore.2.2.1.trans hlId,
      hcore.2.2.2.trans hrId⟩

/-! -------------------------------------------------------------------------
    Binary add-one view of rooted segment IDs
------------------------------------------------------------------------- -/

private def idRowWord
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    Nat -> Nat -> Nat
  | 0, _ => 0
  | len + 1, j =>
      (if
          (C (shiftRight ring start j)).id =
            true
        then 1
        else 0) +
        2 * idRowWord ring C start len (j + 1)

private theorem idRowWord_factor
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    forall len j : Nat,
      segmentIdAux ring C start len j =
        2 ^ j *
          idRowWord ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [segmentIdAux, idRowWord]
  | succ len ih =>
      intro j
      simp only [segmentIdAux, idRowWord]
      rw [ih (j + 1)]
      cases hb :
          (C (shiftRight ring start j)).id <;>
        simp [hb, Nat.pow_succ,
          Nat.mul_add, Nat.mul_assoc]

private theorem idRow_segmentIdFrom_word
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (len : Nat) :
    segmentIdFrom ring C start len =
      idRowWord ring C start len 0 := by
  unfold segmentIdFrom
  rw [idRowWord_factor]
  simp

private theorem idRowWord_lt_pow
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    forall len j : Nat,
      idRowWord ring C start len j <
        2 ^ len := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [idRowWord]
  | succ len ih =>
      intro j
      have ht := ih (j + 1)
      cases hb :
          (C (shiftRight ring start j)).id <;>
        simp [idRowWord, hb, Nat.pow_succ] <;>
        omega

private theorem idRowWord_eq_bit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (a b : Fin n) :
    forall fuel j x : Nat,
      j <= x ->
      x < j + fuel ->
      idRowWord ring C a fuel j =
        idRowWord ring C b fuel j ->
      (C (shiftRight ring a x)).id =
        (C (shiftRight ring b x)).id := by
  intro fuel
  induction fuel with
  | zero =>
      intro j x hj hx _
      omega
  | succ fuel ih =>
      intro j x hj hx heq
      cases ha :
          (C (shiftRight ring a j)).id <;>
      cases hb :
          (C (shiftRight ring b j)).id
      · by_cases hxj : x = j
        · subst x
          simpa [ha, hb]
        · have htail :
              idRowWord ring C a fuel (j + 1) =
                idRowWord ring C b fuel (j + 1) := by
            simp [idRowWord, ha, hb] at heq
            omega
          exact
            ih (j + 1) x
              (by omega) (by omega) htail
      · simp [idRowWord, ha, hb] at heq
        omega
      · simp [idRowWord, ha, hb] at heq
        omega
      · by_cases hxj : x = j
        · subst x
          simpa [ha, hb]
        · have htail :
              idRowWord ring C a fuel (j + 1) =
                idRowWord ring C b fuel (j + 1) := by
            simp [idRowWord, ha, hb] at heq
            omega
          exact
            ih (j + 1) x
              (by omega) (by omega) htail

private theorem idRow_firstZeroAux_ge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    forall fuel j : Nat,
      j <=
        firstZeroAux ring C start fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j
      simp [firstZeroAux]
  | succ fuel ih =>
      intro j
      cases hb :
          (C (shiftRight ring start j)).id with
      | false =>
          simp [firstZeroAux, hb]
      | true =>
          have ht := ih (j + 1)
          simp [firstZeroAux, hb]
          omega

private theorem idRowWord_add_one_bit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (source target : Fin n) :
    forall fuel j x : Nat,
      j <= x ->
      x < j + fuel ->
      idRowWord ring C target fuel j =
        (idRowWord ring C source fuel j + 1) %
          (2 ^ fuel) ->
      (C (shiftRight ring target x)).id =
        (if
            x <=
              firstZeroAux
                ring C source fuel j
          then
            !(C (shiftRight ring source x)).id
          else
            (C (shiftRight ring source x)).id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j x hj hx _
      omega
  | succ fuel ih =>
      intro j x hj hx heq
      have hsTailLt :=
        idRowWord_lt_pow
          ring C source fuel (j + 1)
      cases hs :
          (C (shiftRight ring source j)).id with
      | false =>
          have hsumlt :
              idRowWord ring C source
                    (fuel + 1) j + 1 <
                2 ^ (fuel + 1) := by
            simp [idRowWord, hs, Nat.pow_succ]
            omega
          have heq' := heq
          rw [Nat.mod_eq_of_lt hsumlt] at heq'
          cases ht :
              (C (shiftRight ring target j)).id with
          | false =>
              simp [idRowWord, hs, ht] at heq'
              omega
          | true =>
              have htail :
                  idRowWord ring C target
                      fuel (j + 1) =
                    idRowWord ring C source
                      fuel (j + 1) := by
                simp [idRowWord, hs, ht] at heq'
                omega
              have hfirst :
                  firstZeroAux ring C source
                      (fuel + 1) j = j := by
                simp [firstZeroAux, hs]
              by_cases hxj : x = j
              · subst x
                simp [hfirst, hs, ht]
              · have hsame :=
                  idRowWord_eq_bit
                    ring C target source
                    fuel (j + 1) x
                    (by omega) (by omega) htail
                have hnot : Not (x <= j) := by
                  omega
                simpa [hfirst, hnot] using hsame
      | true =>
          have hpair :
              And
                ((C (shiftRight ring target j)).id =
                  false)
                (idRowWord ring C target
                    fuel (j + 1) =
                  (idRowWord ring C source
                        fuel (j + 1) + 1) %
                    (2 ^ fuel)) := by
            by_cases hsmall :
                idRowWord ring C source
                      fuel (j + 1) + 1 <
                  2 ^ fuel
            · have hsumlt :
                  idRowWord ring C source
                        (fuel + 1) j + 1 <
                    2 ^ (fuel + 1) := by
                simp [idRowWord, hs, Nat.pow_succ]
                omega
              have heq' := heq
              rw [Nat.mod_eq_of_lt hsumlt] at heq'
              cases ht :
                  (C (shiftRight ring target j)).id with
              | false =>
                  have htail0 :
                      idRowWord ring C target
                          fuel (j + 1) =
                        idRowWord ring C source
                            fuel (j + 1) + 1 := by
                    simp [idRowWord, hs, ht] at heq'
                    omega
                  have htail :
                      idRowWord ring C target
                          fuel (j + 1) =
                        (idRowWord ring C source
                              fuel (j + 1) + 1) %
                          (2 ^ fuel) := by
                    rw [Nat.mod_eq_of_lt hsmall]
                    exact htail0
                  exact ⟨rfl, htail⟩
              | true =>
                  simp [idRowWord, hs, ht] at heq'
                  omega
            · have hover :
                  idRowWord ring C source
                        fuel (j + 1) + 1 =
                    2 ^ fuel := by
                omega
              have hsum :
                  idRowWord ring C source
                        (fuel + 1) j + 1 =
                    2 ^ (fuel + 1) := by
                simp [idRowWord, hs, Nat.pow_succ]
                omega
              have hzero :
                  idRowWord ring C target
                      (fuel + 1) j = 0 := by
                rw [heq, hsum, Nat.mod_self]
              cases ht :
                  (C (shiftRight ring target j)).id with
              | false =>
                  have htail0 :
                      idRowWord ring C target
                          fuel (j + 1) = 0 := by
                    simp [idRowWord, ht] at hzero
                    omega
                  have htail :
                      idRowWord ring C target
                          fuel (j + 1) =
                        (idRowWord ring C source
                              fuel (j + 1) + 1) %
                          (2 ^ fuel) := by
                    rw [htail0, hover, Nat.mod_self]
                  exact ⟨rfl, htail⟩
              | true =>
                  simp [idRowWord, ht] at hzero
          rcases hpair with ⟨ht, htail⟩
          have hfirst :
              firstZeroAux ring C source
                  (fuel + 1) j =
                firstZeroAux ring C source
                  fuel (j + 1) := by
            simp [firstZeroAux, hs]
          by_cases hxj : x = j
          · subst x
            have hge :=
              idRow_firstZeroAux_ge
                ring C source fuel (j + 1)
            have hjle :
                j <=
                  firstZeroAux ring C source
                    fuel (j + 1) := by
              omega
            simp [hfirst, hs, ht, hjle]
          · have hrec :=
              ih (j + 1) x
                (by omega) (by omega) htail
            simpa [hfirst] using hrec

private theorem idRow_interior_lengths
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (seg : Fin (segmentCount n psi - 2)) :
    And
      (segmentLength n psi seg.val = psi)
      (segmentLength n psi
        (seg.val + 1) = psi) := by
  have hz :
      seg.val + 3 <= segmentCount n psi := by
    have hs := seg.isLt
    omega
  unfold segmentCount at hz
  have hmul :
      (seg.val + 3) * psi <=
        n + psi - 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).mp hz
  have h2 :
      (seg.val + 2) * psi < n := by
    simp [Nat.add_mul] at hmul ⊢
    omega
  have h1 :
      (seg.val + 1) * psi < n := by
    simp [Nat.add_mul] at h2 ⊢
    omega
  constructor
  · unfold segmentLength
    have hle : (seg.val + 1) * psi <= n := by
      omega
    have hm : Nat.min ((seg.val + 1) * psi) n = (seg.val + 1) * psi :=
      Nat.min_eq_left hle
    rw [hm]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · unfold segmentLength
    have hle : (seg.val + 1 + 1) * psi <= n := by
      simp only [Nat.add_mul, Nat.one_mul] at h2 ⊢
      omega
    have hm : Nat.min ((seg.val + 1 + 1) * psi) n = (seg.val + 1 + 1) * psi :=
      Nat.min_eq_left hle
    rw [hm]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

private theorem idRow_successor_segment_bit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (seg : Fin (segmentCount n psi - 2))
    (hsucc :
      rootedSegmentId ring root C
          (seg.val + 1) =
        (rootedSegmentId ring root C seg.val + 1) %
          (2 ^ psi))
    (x : Nat)
    (hx : x < psi) :
    (C
      (shiftRight ring
        (shiftRight ring root
          ((seg.val + 1) * psi))
        x)).id =
      (if
          x <=
            firstZeroBit ring C
              (shiftRight ring root
                (seg.val * psi))
        then
          !(C
            (shiftRight ring
              (shiftRight ring root
                (seg.val * psi))
              x)).id
        else
          (C
            (shiftRight ring
              (shiftRight ring root
                (seg.val * psi))
              x)).id) := by
  have hlens :=
    idRow_interior_lengths hpsi seg
  have hword := hsucc
  unfold rootedSegmentId at hword
  rw [hlens.1, hlens.2] at hword
  simp only [idRow_segmentIdFrom_word] at hword
  have hbit :=
    idRowWord_add_one_bit
      ring C
      (shiftRight ring root (seg.val * psi))
      (shiftRight ring root
        ((seg.val + 1) * psi))
      psi 0 x
      (by omega) (by omega) hword
  exact hbit

/-! -------------------------------------------------------------------------
    A live c=1 token can only hit an interior target
------------------------------------------------------------------------- -/

private theorem idRow_inSegment_of_div
    {n psi : Nat}
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (root i : Fin n)
    (y : Nat)
    (hy :
      cyclicOffset ring root i = y)
    (k : Nat)
    (hk : k = y / psi) :
    InSegment ring root psi k i := by
  have hrem :
      y % psi + psi * (y / psi) = y :=
    Nat.mod_add_div y psi
  have hremLt : y % psi < psi :=
    Nat.mod_lt _ hpsi
  have hyN :
      y < n := by
    rw [← hy]
    exact idRow_cyclicOffset_lt ring root i
  have hlower :
      k * psi <= y := by
    rw [hk]
    rw [Nat.mul_comm]
    omega
  have hupper :
      y < (k + 1) * psi := by
    rw [hk]
    simp [Nat.add_mul]
    rw [Nat.mul_comm psi (y / psi)] at hrem
    omega
  unfold InSegment
  dsimp only
  rw [hy]
  constructor
  · exact hlower
  · exact Nat.lt_min.mpr ⟨hupper, hyN⟩

private theorem idRow_c1_interior_working
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (hC : SPLAt ring root C)
    (ht :
      tokenAt kind (C e) = some t)
    (hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int))
    (hjne :
      ring.rightNeighbor e ≠ root)
    (hjlast :
      (C (ring.rightNeighbor e)).last =
        false) :
    Exists fun
      seg : Fin (segmentCount n psi - 2) =>
        WorkingFor
          ring root C e kind seg.val := by
  let j := ring.rightNeighbor e
  let x := cyclicOffset ring root e
  let y := cyclicOffset ring root j
  let zeta := segmentCount n psi
  let start := psi * (zeta - 1)

  have hyx :
      y = x + 1 := by
    simpa [x, y, j] using
      idRow_rightNeighbor_offset_of_ne_root
        ring root e
        (by simpa [j] using hjne)

  have hyN : y < n := by
    exact idRow_cyclicOffset_lt ring root j

  have hgeomJ := hC.1.2.2 j
  dsimp only at hgeomJ
  have hnotFinal :
      Not (start <= y) := by
    intro hs
    have htLast :
        (C j).last = true :=
      hgeomJ.2.mpr
        (by simpa [start, zeta, y] using hs)
    rw [hjlast] at htLast
    contradiction
  have hyStart : y < start := by
    omega

  have hyPsi : psi <= y := by
    by_cases hy0 : y < psi
    · have hx0 : x < psi := by
        omega
      have hSe :
          InSegment ring root psi 0 e :=
        idRow_inSegment_zero_of_offset_lt
          ring root e
          (by simpa [x] using hx0)
      have hSj :
          InSegment ring root psi 0 j :=
        idRow_inSegment_zero_of_offset_lt
          ring root j
          (by simpa [y] using hy0)
      have hriskKind :
          tokenRisky ring root C e kind := by
        unfold tokenRisky
        rw [ht]
        dsimp only
        rw [hc1]
        constructor
        · omega
        · intro h
          have hv : h.val = 0 ∨ h.val = 1 := by
            have hh := h.isLt
            simp at hh
            omega
          rcases hv with h0 | h1
          · rw [h0, idRow_shiftRight_zero]
            exact hSe
          · have hstep :
                shiftRight ring e 1 = j := by
              rfl
            rw [h1, hstep]
            exact hSj
      have hrisk :
          Risky ring root C e := by
        cases kind with
        | black =>
            exact Or.inl hriskKind
        | white =>
            exact Or.inr hriskKind
      exact False.elim ((hC.2.1 e) hrisk)
    · omega

  let k := y / psi
  have hrem :
      y % psi + psi * k = y := by
    simpa [k] using Nat.mod_add_div y psi
  have hkPos : 1 <= k := by
    have h0 : 0 < psi := by
      omega
    first
      | exact (Nat.le_div_iff_mul_le h0).mpr (by omega)
      | exact Nat.div_pos hyPsi h0
      | exact Nat.div_pos h0 hyPsi
  have hkUpper : k < zeta - 1 := by
    by_cases hk : k < zeta - 1
    · exact hk
    · have hle : zeta - 1 <= k := by
        omega
      have hmul :=
        Nat.mul_le_mul_left psi hle
      dsimp [start] at hyStart
      omega

  let sv := k - 1
  have hsv : sv < zeta - 2 := by
    dsimp [sv]
    omega
  let seg : Fin (zeta - 2) :=
    ⟨sv, hsv⟩

  have hInJ :
      InSegment ring root psi k j := by
    exact
      idRow_inSegment_of_div
        (by omega) ring root j y
        (by rfl) k (by rfl)

  have hkZeta : k < zeta := by
    omega
  have hidx :
      (seg.val + 1) % zeta = k := by
    dsimp [seg, sv]
    have hka : k - 1 + 1 = k :=
      Nat.sub_add_cancel hkPos
    rw [hka, Nat.mod_eq_of_lt hkZeta]

  have htarget :
      tokenTargetSite ring e t = j := by
    exact idRow_tokenTarget_one ring e t hc1

  refine ⟨seg, ?_⟩
  unfold WorkingFor
  rw [ht]
  dsimp only
  rw [hc1]
  have hzpos : 0 < zeta := by
    omega
  refine
    And.intro hzpos
      (Or.inl
        (And.intro (by omega) ?_))
  rw [hidx, htarget]
  exact hInJ

/-! -------------------------------------------------------------------------
    Correct c=1 payload equals the actual target ID bit
------------------------------------------------------------------------- -/

private theorem idRow_correct_c1_target_bit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (seg : Fin (segmentCount n psi - 2))
    (ht :
      tokenAt kind (C e) = some t)
    (hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int))
    (hsucc :
      rootedSegmentId ring root C
          (seg.val + 1) =
        (rootedSegmentId ring root C seg.val + 1) %
          (2 ^ psi))
    (hcorr :
      CorrectToken
        ring root C e kind seg.val) :
    tokenBitBool t =
      (C (ring.rightNeighbor e)).id := by
  let source :=
    shiftRight ring root (seg.val * psi)
  let target :=
    tokenTargetSite ring e t
  let rel :=
    cyclicOffset ring source target
  let x := rel - psi
  let targetStart :=
    shiftRight ring root
      ((seg.val + 1) * psi)

  have hc := hcorr
  unfold CorrectToken at hc
  rw [ht] at hc
  dsimp only at hc
  rw [hc1, if_pos (by omega)] at hc
  rcases hc with
    ⟨_hparity, hrel, hx, hpay⟩
  have hrel' : psi <= rel := by
    simpa [source, target, rel] using hrel
  have hx' : x < psi := by
    simpa [source, target, rel, x] using hx
  have hpay' :
      payloadCorrect ring C source x t := by
    simpa [source, target, rel, x]
      using hpay

  have hstart :
      targetStart =
        shiftRight ring source psi := by
    dsimp [targetStart, source]
    calc
      shiftRight ring root
          ((seg.val + 1) * psi) =
        shiftRight ring root
          (seg.val * psi + psi) := by
            congr 2
            simp [Nat.add_mul]
      _ =
        shiftRight ring
          (shiftRight ring root
            (seg.val * psi)) psi :=
        (idRow_shiftRight_add
          ring root (seg.val * psi) psi).symm

  have hrelEq : psi + x = rel := by
    dsimp [x]
    omega

  have hsite :
      shiftRight ring targetStart x =
        target := by
    rw [hstart]
    calc
      shiftRight ring
          (shiftRight ring source psi) x =
        shiftRight ring source (psi + x) :=
          idRow_shiftRight_add
            ring source psi x
      _ = shiftRight ring source rel := by
        rw [hrelEq]
      _ = target :=
        idRow_shiftRight_cyclicOffset
          ring source target

  have hsuccBit :=
    idRow_successor_segment_bit
      hpsi ring root C seg hsucc x hx'
  have htargetBit :
      (C target).id =
        (if
            x <= firstZeroBit ring C source
          then
            !(C (shiftRight ring source x)).id
          else
            (C (shiftRight ring source x)).id) := by
    rw [← hsite]
    simpa [source, targetStart]
      using hsuccBit

  unfold payloadCorrect at hpay'
  dsimp only at hpay'
  have htargetOne :
      target = ring.rightNeighbor e := by
    dsimp [target]
    exact idRow_tokenTarget_one ring e t hc1

  calc
    tokenBitBool t =
        (if
            x <= firstZeroBit ring C source
          then
            !(C (shiftRight ring source x)).id
          else
            (C (shiftRight ring source x)).id) :=
      hpay'.1
    _ = (C target).id := htargetBit.symm
    _ = (C (ring.rightNeighbor e)).id := by
      rw [htargetOne]

/-! -------------------------------------------------------------------------
    One SPL-safe selected-color pass
------------------------------------------------------------------------- -/

private theorem idRow_valid_of_local
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (e : Fin n)
    (l : State psi kappa)
    (t : TokenData psi)
    (hdist : l.dist = (C e).dist)
    (htl : tokenAt kind l = some t)
    (htC : tokenAt kind (C e) = some t)
    (hv : idRowLocalValid kind l t) :
    ValidToken kind C e := by
  unfold idRowLocalValid at hv
  unfold ValidToken
  rw [htC]
  dsimp only
  simpa [tokenTargetCoordinate, hdist] using hv

private theorem idRow_moveToken_of_SPL
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hlDist : l.dist = (C e).dist)
    (hrLast :
      r.last =
        (C (ring.rightNeighbor e)).last)
    (hrId :
      r.id =
        (C (ring.rightNeighbor e)).id)
    (hlTok :
      tokenAt kind l =
        tokenAt kind (C e))
    (hrootBlock :
      (C (ring.rightNeighbor e)).leader = true ->
        l.last = true) :
    idRowLeaderIdFrame l r
      (PPL.moveToken hpsi kind l r) := by
  apply
    idRow_moveToken_frame_of_c1_safe
      hpsi kind l r
  intro t hlc hrc hsel hc1

  have hlFalse : l.last = false := by
    calc
      l.last =
          (PPL.sourceClear kind l).last :=
        (idRow_sourceClear_last kind l).symm
      _ = false := hlc
  have hrFalse : r.last = false := by
    calc
      r.last =
          (PPL.sourceClear kind r).last :=
        (idRow_sourceClear_last kind r).symm
      _ = false := hrc

  have horigin :=
    idRow_selected_c1_origin
      hpsi kind l r t hsel hc1
  rcases horigin with ⟨htl, hvLocal⟩
  have htC :
      tokenAt kind (C e) = some t := by
    calc
      tokenAt kind (C e) =
          tokenAt kind l := hlTok.symm
      _ = some t := htl
  have hvalid :
      ValidToken kind C e :=
    idRow_valid_of_local
      kind C e l t
      hlDist htl htC hvLocal

  let j := ring.rightNeighbor e
  have hjne : j ≠ root := by
    intro hj
    have hjLead :
        (C j).leader = true :=
      (hC.1.2.1 j).2 hj
    have hlTrue :
        l.last = true := by
      exact hrootBlock
        (by simpa [j] using hjLead)
    rw [hlFalse] at hlTrue
    contradiction

  have hjLast :
      (C j).last = false := by
    calc
      (C j).last = r.last := by
        simpa [j] using hrLast.symm
      _ = false := hrFalse

  rcases
      idRow_c1_interior_working
        hpsi ring root C e kind t
        hC htC hc1
        (by simpa [j] using hjne)
        (by simpa [j] using hjLast)
    with ⟨seg, hwork⟩

  have hrow := hC.2.2 seg
  have hcorr :
      CorrectToken
        ring root C e kind seg.val := by
    cases kind with
    | black =>
        exact hrow.2 e |>.1
          (And.intro hvalid hwork)
    | white =>
        exact hrow.2 e |>.2
          (And.intro hvalid hwork)

  have hbit :=
    idRow_correct_c1_target_bit
      hpsi ring root C e kind t seg
      htC hc1 hrow.1 hcorr

  calc
    tokenBitBool t =
        (C (ring.rightNeighbor e)).id :=
      hbit
    _ = r.id := hrId.symm
    _ = (PPL.sourceClear kind r).id :=
      (idRow_sourceClear_id kind r).symm

/-! -------------------------------------------------------------------------
    Black pass -> white pass field transport
------------------------------------------------------------------------- -/

private theorem idRow_moveToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    And
      (q.1.dist = l.dist)
      (And
        (q.1.last = l.last)
        (q.2.last = r.last)) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l r
    with hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId,
          PPL.birthFields]

private theorem idRow_black_white_token
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    let q :=
      PPL.moveToken hpsi .black l r
    And
      (tokenAt .white q.1 =
        tokenAt .white l)
      (tokenAt .white q.2 =
        tokenAt .white r) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi .black l r
  have hi' :=
    congrArg
      (fun q : State psi kappa =>
        tokenAt .white q) hi
  have hleft :
      tokenAt .white
          (PPL.moveToken hpsi .black l r).1 =
        tokenAt .white l := by
    simpa
      [PPL.eraseKindToken,
        tokenAt] using hi'

  rcases
      PPL.moveToken_responder_fields
        hpsi .black l r
    with hr | hr
  · have hr' :=
      congrArg
        (fun q : State psi kappa =>
          tokenAt .white q) hr
    refine And.intro hleft ?_
    simpa
      [PPL.eraseKindTokenId,
        PPL.eraseKindToken,
        tokenAt] using hr'
  · have hr' :=
      congrArg
        (fun q : State psi kappa =>
          tokenAt .white q) hr
    refine And.intro hleft ?_
    simpa
      [PPL.eraseKindTokenId,
        PPL.eraseKindToken,
        PPL.birthFields,
        tokenAt] using hr'

/-! -------------------------------------------------------------------------
    Assembly
------------------------------------------------------------------------- -/

theorem splAlgorithm3IdempotentIdRow_proved :
    SPLAlgorithm3IdempotentIdRow := by
  unfold SPLAlgorithm3IdempotentIdRow
  intro n psi kappa
  intro hn3 hpsi ring root C e hC

  let j := ring.rightNeighbor e
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C j)
  let b :=
    PPL.moveToken hpsi .black p.1 p.2
  let w :=
    PPL.moveToken hpsi .white b.1 b.2

  have hpB0 :=
    idRow_preToken_frame
      hpsi TokenKind.black
      (C e) (C j)
  have hpB :
      And
        (p.1.dist = (C e).dist)
        (And
          (tokenAt .black p.1 =
            tokenAt .black (C e))
          (And
            (p.2.last = (C j).last)
            (And
              (p.2.id = (C j).id)
              ((C j).leader = true ->
                p.1.last = true)))) := by
    simpa [p] using hpB0
  rcases hpB with
    ⟨hpDist, hpTokB, hpRLast,
      hpRId, hpRootBlock⟩

  have hpW0 :=
    idRow_preToken_frame
      hpsi TokenKind.white
      (C e) (C j)
  have hpTokW :
      tokenAt .white p.1 =
        tokenAt .white (C e) := by
    have h :
        And
          (p.1.dist = (C e).dist)
          (And
            (tokenAt .white p.1 =
              tokenAt .white (C e))
            (And
              (p.2.last = (C j).last)
              (And
                (p.2.id = (C j).id)
                ((C j).leader = true ->
                  p.1.last = true)))) := by
      simpa [p] using hpW0
    exact h.2.1

  have hbFrame0 :=
    idRow_moveToken_of_SPL
      hn3 hpsi ring root C e hC
      TokenKind.black p.1 p.2
      hpDist
      (by simpa [j] using hpRLast)
      (by simpa [j] using hpRId)
      hpTokB
      (by simpa [j] using hpRootBlock)
  have hbFrame :
      idRowLeaderIdFrame p.1 p.2 b := by
    simpa [b] using hbFrame0

  have hbGeom0 :=
    idRow_moveToken_dist_last
      hpsi TokenKind.black p.1 p.2
  have hbGeom :
      And
        (b.1.dist = p.1.dist)
        (And
          (b.1.last = p.1.last)
          (b.2.last = p.2.last)) := by
    simpa [b] using hbGeom0

  have hbWhite0 :=
    idRow_black_white_token
      hpsi p.1 p.2
  have hbWhite :
      tokenAt .white b.1 =
        tokenAt .white p.1 := by
    simpa [b] using hbWhite0.1

  have hbDist :
      b.1.dist = (C e).dist :=
    hbGeom.1.trans hpDist
  have hbRLast :
      b.2.last = (C j).last :=
    hbGeom.2.2.trans hpRLast
  have hbRId :
      b.2.id = (C j).id :=
    hbFrame.2.2.2.trans hpRId
  have hbTokW :
      tokenAt .white b.1 =
        tokenAt .white (C e) :=
    hbWhite.trans hpTokW
  have hbRootBlock :
      (C j).leader = true ->
        b.1.last = true := by
    intro h
    calc
      b.1.last = p.1.last := hbGeom.2.1
      _ = true := hpRootBlock h

  have hwFrame0 :=
    idRow_moveToken_of_SPL
      hn3 hpsi ring root C e hC
      TokenKind.white b.1 b.2
      hbDist
      (by simpa [j] using hbRLast)
      (by simpa [j] using hbRId)
      hbTokW
      (by simpa [j] using hbRootBlock)
  have hwFrame :
      idRowLeaderIdFrame b.1 b.2 w := by
    simpa [w] using hwFrame0

  refine
    And.intro ?_
      (And.intro ?_
        (And.intro ?_ ?_))
  · intro hp
    calc
      w.1.leader = b.1.leader := hwFrame.1
      _ = p.1.leader := hbFrame.1
      _ = false := hp
  · intro hp
    calc
      w.2.leader = b.2.leader := hwFrame.2.1
      _ = p.2.leader := hbFrame.2.1
      _ = false := hp
  · calc
      w.1.id = b.1.id := hwFrame.2.2.1
      _ = p.1.id := hbFrame.2.2.1
  · calc
      w.2.id = b.2.id := hwFrame.2.2.2
      _ = p.2.id := hbFrame.2.2.2

#print axioms idRow_shiftRight_add
#print axioms idRow_shiftRight_zero
#print axioms idRow_shiftRight_n
#print axioms idRow_cyclicOffset_lt
#print axioms idRow_cyclicOffset_shiftRight_of_lt
#print axioms idRow_shiftRight_cyclicOffset
#print axioms idRow_rightNeighbor_offset_of_ne_root
#print axioms idRow_inSegment_zero_of_offset_lt
#print axioms idRow_tokenTarget_one
#print axioms idRow_determineMode_frame
#print axioms idRow_line6_frame
#print axioms idRow_preToken_frame
#print axioms idRow_sourceClear_eq
#print axioms idRow_sourceSet_tokenAt
#print axioms idRow_sourceSet_id
#print axioms idRow_sourceSet_leader
#print axioms idRow_sourceSet_last
#print axioms idRow_sourceClear_id
#print axioms idRow_sourceClear_leader
#print axioms idRow_sourceClear_last
#print axioms idRow_sourceClear_some
#print axioms idRowMoveToken_eq
#print axioms idRow_selected_c1_origin
#print axioms idRow_freshen_frame
#print axioms idRow_collision_frame
#print axioms idRow_moveLeft_frame
#print axioms idRow_moveRightOne_frame
#print axioms idRow_moveTokenCore_frame
#print axioms idRow_moveToken_frame_of_c1_safe
#print axioms idRowWord_factor
#print axioms idRow_segmentIdFrom_word
#print axioms idRowWord_lt_pow
#print axioms idRowWord_eq_bit
#print axioms idRow_firstZeroAux_ge
#print axioms idRowWord_add_one_bit
#print axioms idRow_interior_lengths
#print axioms idRow_successor_segment_bit
#print axioms idRow_inSegment_of_div
#print axioms idRow_c1_interior_working
#print axioms idRow_correct_c1_target_bit
#print axioms idRow_valid_of_local
#print axioms idRow_moveToken_of_SPL
#print axioms idRow_moveToken_dist_last
#print axioms idRow_black_white_token
#print axioms splAlgorithm3IdempotentIdRow_proved

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splAlgorithm3IdempotentIdRow_proved
