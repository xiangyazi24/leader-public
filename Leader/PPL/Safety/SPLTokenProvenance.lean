import Leader.PPL.Safety.SPLFieldFrame

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# S_PL post-token provenance

The first theorem classifies every post token, not only every post valid token.
At the selected pair it records the exact selected MoveToken output and the
only old input that can own it under Algorithm 3's collision orientation.
The remaining alternative is the literal line-14/15 birth guard at a border.

The second section reduces no-new-risky to the two interacted sites.  This
reduction is exact because Risky depends only on the token at its host and
static ring/root geometry, while an off-pair site is a literal state frame.
-/

/-! -------------------------------------------------------------------------
    Public-name mirrors for line 12 and the selected Algorithm-3 row
------------------------------------------------------------------------- -/

private def splProvBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def splProvMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def splProvLocalValid
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

private instance instDecidableSplProvLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (splProvLocalValid kind q t) := by
  unfold splProvLocalValid
  infer_instance

private def splProvSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := x }
  | .white => { q with tokenW := x }

private def splProvClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if splProvLocalValid kind q t then
        q
      else
        splProvSetToken kind q none

private theorem splProvSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    PPL.sourceClear kind q =
      splProvClearInvalid kind q := by
  cases kind <;> rfl

private theorem splProvSourceClear_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt kind (PPL.sourceClear kind q) =
        some t) :
    tokenAt kind q = some t := by
  rw [splProvSourceClear_eq] at h
  unfold splProvClearInvalid at h
  cases hq : tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      rw [hq] at h
      dsimp only at h
      by_cases hv : splProvLocalValid kind q u
      · rw [if_pos hv] at h
        rw [hq] at h
        exact h
      · rw [if_neg hv] at h
        unfold splProvSetToken at h
        cases kind <;> simp [tokenAt] at h

private theorem splProvSourceClear_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).dist = q.dist := by
  rw [splProvSourceClear_eq]
  unfold splProvClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      rfl
  | some u =>
      by_cases hv : splProvLocalValid kind q u
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold splProvSetToken
        cases kind <;> rfl

@[simp] private theorem splProvSourceSet_tokenAt
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    tokenAt kind (PPL.sourceSet kind q x) = x := by
  cases kind <;> rfl

private def splProvNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    splProvMkToken
      (offsetPsiCode psi hpsi)
      (splProvBitToFin (!sourceBit))
      (splProvBitToFin sourceBit)
  else
    splProvMkToken
      (offsetPsiCode psi hpsi)
      (splProvBitToFin sourceBit)
      (0 : Fin 2)

private def splProvMoveTokenMirror
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := PPL.sourceClear kind l
  let r := PPL.sourceClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧
          tokenAt kind l = none then
        PPL.sourceSet kind l
          (some
            (splProvMkToken
              (offsetPsiCode psi hpsi)
              (splProvBitToFin (!l.id))
              (splProvBitToFin l.id)))
      else
        l
    let l :=
      if tokenAt kind l ≠ none ∧
          tokenAt kind r ≠ none then
        PPL.sourceSet kind l none
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
                splProvNegTurnNext hpsi l.id t
              (PPL.sourceSet kind l (some next),
                PPL.sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                splProvMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              (PPL.sourceSet kind l (some next),
                PPL.sourceSet kind r none)
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
              PPL.sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          let r :=
            PPL.sourceSet kind r
              (some
                (splProvMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2))
          let l :=
            PPL.sourceSet kind l none
          (l, r)
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            splProvMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          (PPL.sourceSet kind l none,
            PPL.sourceSet kind r (some next))
        else
          moveLeft l r
  else
    (l, r)

private theorem splProvMoveTokenMirror_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    splProvMoveTokenMirror hpsi kind l r =
      PPL.moveToken hpsi kind l r := by
  cases kind <;> rfl

private theorem splProvMoveToken_gate_closed
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hgate :
      ¬ ((PPL.sourceClear kind l).last = false ∧
        (PPL.sourceClear kind r).last = false)) :
    let q := PPL.moveToken hpsi kind l r
    tokenAt kind q.1 =
        tokenAt kind (PPL.sourceClear kind l) ∧
      tokenAt kind q.2 =
        tokenAt kind (PPL.sourceClear kind r) := by
  dsimp only
  rw [← splProvMoveTokenMirror_eq hpsi kind l r]
  simp [splProvMoveTokenMirror, hgate]

private theorem splProvNoLiveOutput_forces_border
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hgate :
      (PPL.sourceClear kind l).last = false ∧
        (PPL.sourceClear kind r).last = false)
    (hl :
      tokenAt kind (PPL.sourceClear kind l) = none)
    (hr :
      tokenAt kind (PPL.sourceClear kind r) = none)
    (t' : TokenData psi)
    (hpost :
      tokenAt kind (PPL.moveToken hpsi kind l r).1 =
          some t' ∨
        tokenAt kind (PPL.moveToken hpsi kind l r).2 =
          some t') :
    (PPL.sourceClear kind l).dist.val =
      tokenD' psi kind := by
  by_cases hb :
      (PPL.sourceClear kind l).dist.val =
        tokenD' psi kind
  · exact hb
  · rcases hpost with hpost | hpost
    · rw [← splProvMoveTokenMirror_eq hpsi kind l r] at hpost
      simp
        [splProvMoveTokenMirror, hgate, hl, hr, hb]
        at hpost
    · rw [← splProvMoveTokenMirror_eq hpsi kind l r] at hpost
      simp
        [splProvMoveTokenMirror, hgate, hl, hr, hb]
        at hpost

/-! -------------------------------------------------------------------------
    Algorithm-2 prefix token frames
------------------------------------------------------------------------- -/

private theorem splProvDetermineMode_frame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.dist = l.dist ∧
      tokenAt kind d.1 = tokenAt kind l ∧
      tokenAt kind d.2 = tokenAt kind r := by
  cases kind <;>
    simp only [PPL.determineMode, tokenAt]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl, rfl⟩

private theorem splProvLine6_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    s.left.dist = d.1.dist ∧
      tokenAt kind s.left = tokenAt kind d.1 ∧
      tokenAt kind s.right = tokenAt kind d.2 := by
  dsimp only
  unfold PPL.createLeaderThroughLine6
  dsimp only
  split
  · cases kind <;> exact ⟨rfl, rfl, rfl⟩
  · cases kind <;> exact ⟨rfl, rfl, rfl⟩

private theorem splProvPreToken_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p :=
      PPL.Safety.PeacefulProps.preTokenPair hpsi l r
    p.1.dist = l.dist ∧
      tokenAt kind p.1 = tokenAt kind l ∧
      tokenAt kind p.2 = tokenAt kind r := by
  let d := PPL.determineMode l r
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hd0 := splProvDetermineMode_frame kind l r
  have hd :
      d.1.dist = l.dist ∧
        tokenAt kind d.1 = tokenAt kind l ∧
        tokenAt kind d.2 = tokenAt kind r := by
    simpa [d] using hd0
  have hs0 := splProvLine6_frame hpsi kind l r
  have hs :
      s.left.dist = d.1.dist ∧
        tokenAt kind s.left = tokenAt kind d.1 ∧
        tokenAt kind s.right = tokenAt kind d.2 := by
    simpa [d, s] using hs0

  let r1 : State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  let l1 : State psi kappa :=
    if r1.leader = true then
      { s.left with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { s.left with last := false }
    else
      { s.left with last := r1.last }

  have hrTok :
      tokenAt kind r1 = tokenAt kind r := by
    have h0 := hs.2.2.trans hd.2.2
    by_cases hm : s.right.mode = false
    · simpa [r1, hm, tokenAt] using h0
    · simpa [r1, hm, tokenAt] using h0

  have hlDist0 :
      s.left.dist = l.dist :=
    hs.1.trans hd.1
  have hlDist :
      l1.dist = l.dist := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead] using hlDist0
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hb] using hlDist0
      · simpa [l1, hlead, hb] using hlDist0

  have hlTok0 :
      tokenAt kind s.left = tokenAt kind l :=
    hs.2.1.trans hd.2.1
  have hlTok :
      tokenAt kind l1 = tokenAt kind l := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead, tokenAt] using hlTok0
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hb, tokenAt] using hlTok0
      · simpa [l1, hlead, hb, tokenAt] using hlTok0

  let p :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  have hp : p = (l1, r1) := by
    rfl
  change
    p.1.dist = l.dist ∧
      tokenAt kind p.1 = tokenAt kind l ∧
      tokenAt kind p.2 = tokenAt kind r
  rw [hp]
  exact ⟨hlDist, hlTok, hrTok⟩

private theorem splProvBlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .white
        (PPL.moveToken hpsi .black l r).1 =
      tokenAt .white l ∧
    tokenAt .white
        (PPL.moveToken hpsi .black l r).2 =
      tokenAt .white r := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi .black l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenW) hi
  have hleft :
      tokenAt .white
          (PPL.moveToken hpsi .black l r).1 =
        tokenAt .white l := by
    simpa [PPL.eraseKindToken, tokenAt] using hil
  rcases
      PPL.moveToken_responder_fields
        hpsi .black l r with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenW) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken, tokenAt]
            using hrr⟩
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenW) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken,
              PPL.birthFields, tokenAt]
            using hrr⟩

private theorem splProvMoveToken_left_dist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (PPL.moveToken hpsi kind l r).1.dist =
      l.dist := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  have hd :=
    congrArg
      (fun q : State psi kappa => q.dist) hi
  cases kind <;>
    simpa [PPL.eraseKindToken] using hd

private def splProvSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  match kind with
  | .black => p
  | .white =>
      PPL.moveToken hpsi .black p.1 p.2

private theorem splProvSelectedInput_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := splProvSelectedInput hpsi kind l r
    p.1.dist = l.dist ∧
      tokenAt kind p.1 = tokenAt kind l ∧
      tokenAt kind p.2 = tokenAt kind r := by
  cases kind with
  | black =>
      simpa [splProvSelectedInput] using
        (splProvPreToken_frame
          hpsi TokenKind.black l r)
  | white =>
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair hpsi l r
      have hp :=
        splProvPreToken_frame
          hpsi TokenKind.white l r
      have hb :=
        splProvBlackPreservesWhite
          hpsi p.1 p.2
      have hbd :=
        splProvMoveToken_left_dist
          hpsi TokenKind.black p.1 p.2
      dsimp only at hp
      change
        (PPL.moveToken hpsi TokenKind.black p.1 p.2).1.dist =
            l.dist ∧
          tokenAt TokenKind.white
              (PPL.moveToken hpsi TokenKind.black p.1 p.2).1 =
            tokenAt TokenKind.white l ∧
          tokenAt TokenKind.white
              (PPL.moveToken hpsi TokenKind.black p.1 p.2).2 =
            tokenAt TokenKind.white r
      exact
        ⟨hbd.trans hp.1,
          hb.1.trans hp.2.1,
          hb.2.trans hp.2.2⟩

/-! -------------------------------------------------------------------------
    Full P_PL token projection to the selected MoveToken call
------------------------------------------------------------------------- -/

private theorem splProvElimTokenLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (PPL.eliminateLeaders l r).1 =
      tokenAt kind l := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, tokenAt] using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, tokenAt] using ht

private theorem splProvElimTokenRight
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (PPL.eliminateLeaders l r).2 =
      tokenAt kind r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, tokenAt] using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, tokenAt] using ht

private theorem splProvWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black
        (PPL.moveToken hpsi .white l r).1 =
      tokenAt .black l ∧
    tokenAt .black
        (PPL.moveToken hpsi .white l r).2 =
      tokenAt .black r := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi .white l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  have hleft :
      tokenAt .black
          (PPL.moveToken hpsi .white l r).1 =
        tokenAt .black l := by
    simpa [PPL.eraseKindToken, tokenAt] using hil
  rcases
      PPL.moveToken_responder_fields
        hpsi .white l r with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenB) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken, tokenAt]
            using hrr⟩
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenB) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken,
              PPL.birthFields, tokenAt]
            using hrr⟩

private theorem splProvPplSelectedTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := splProvSelectedInput hpsi kind l r
    tokenAt kind (PPL.ppl hpsi l r).1 =
        tokenAt kind
          (PPL.moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind (PPL.ppl hpsi l r).2 =
        tokenAt kind
          (PPL.moveToken hpsi kind p.1 p.2).2 := by
  cases kind with
  | black =>
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair hpsi l r
      let b :=
        PPL.moveToken hpsi .black p.1 p.2
      let w :=
        PPL.moveToken hpsi .white b.1 b.2
      have hw :=
        splProvWhitePreservesBlack hpsi b.1 b.2
      have hel :=
        splProvElimTokenLeft .black w.1 w.2
      have her :=
        splProvElimTokenRight .black w.1 w.2
      have hfull :
          PPL.ppl hpsi l r =
            PPL.eliminateLeaders w.1 w.2 := by
        rfl
      rw [hfull]
      change
        tokenAt .black (PPL.eliminateLeaders w.1 w.2).1 =
            tokenAt .black b.1 ∧
          tokenAt .black (PPL.eliminateLeaders w.1 w.2).2 =
            tokenAt .black b.2
      exact
        ⟨hel.trans hw.1,
          her.trans hw.2⟩
  | white =>
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair hpsi l r
      let b :=
        PPL.moveToken hpsi .black p.1 p.2
      let w :=
        PPL.moveToken hpsi .white b.1 b.2
      have hel :=
        splProvElimTokenLeft .white w.1 w.2
      have her :=
        splProvElimTokenRight .white w.1 w.2
      have hfull :
          PPL.ppl hpsi l r =
            PPL.eliminateLeaders w.1 w.2 := by
        rfl
      rw [hfull]
      change
        tokenAt .white (PPL.eliminateLeaders w.1 w.2).1 =
            tokenAt .white w.1 ∧
          tokenAt .white (PPL.eliminateLeaders w.1 w.2).2 =
            tokenAt .white w.2
      exact ⟨hel, her⟩

private theorem splProvRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 ≤ n)
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

private theorem splProvStepTokenPair
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    let p :=
      splProvSelectedInput hpsi kind
        (C e) (C (ring.rightNeighbor e))
    tokenAt kind (nextConfig ring C e e) =
        tokenAt kind
          (PPL.moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind
          (nextConfig ring C e
            (ring.rightNeighbor e)) =
        tokenAt kind
          (PPL.moveToken hpsi kind p.1 p.2).2 := by
  dsimp only
  have hne :=
    splProvRightNeighbor_ne_self hn3 ring e
  have hp :=
    splProvPplSelectedTokenPair
      hpsi kind
      (C e) (C (ring.rightNeighbor e))
  dsimp only at hp
  unfold nextConfig
  have hl :
      PopulationProtocol.step
          (PPL.protocol psi kappa)
          ring C e e =
        (PPL.ppl hpsi
          (C e) (C (ring.rightNeighbor e))).1 := by
    simp
      [PopulationProtocol.step, PPL.protocol,
        PPL.transition, hpsi]
  have hr :
      PopulationProtocol.step
          (PPL.protocol psi kappa)
          ring C e (ring.rightNeighbor e) =
        (PPL.ppl hpsi
          (C e) (C (ring.rightNeighbor e))).2 := by
    simp
      [PopulationProtocol.step, PPL.protocol,
        PPL.transition, hpsi, hne]
  exact
    ⟨by rw [hl]; exact hp.1,
      by rw [hr]; exact hp.2⟩

private theorem splProvStep_other
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    nextConfig ring C e i = C i := by
  unfold nextConfig PopulationProtocol.step
  simp [hie, hir]

/-! -------------------------------------------------------------------------
    Provenance interface
------------------------------------------------------------------------- -/

/--
An old-image certificate for a post selected token.

The selected input is the exact pair seen by the chosen black/white MoveToken
call.  With an open gate a live responder selected token owns every surviving
selected output, because collision deletes the left contender.  If the
responder slot is empty, a live left token owns the selected output.  With a
closed gate each endpoint keeps its own cleared token.  Off-pair sites are
literal frames.
-/
def SPLPostTokenOldImage
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (kind : TokenKind)
    (t' : TokenData psi) : Prop :=
  let rsite := ring.rightNeighbor e
  let p :=
    splProvSelectedInput hpsi kind (C e) (C rsite)
  let l0 := PPL.sourceClear kind p.1
  let r0 := PPL.sourceClear kind p.2
  let q := PPL.moveToken hpsi kind p.1 p.2
  let gate := l0.last = false ∧ r0.last = false
  ∃ j : Fin n, ∃ t : TokenData psi,
    (j = e ∨ j = rsite ∨ j = i) ∧
      tokenAt kind (C j) = some t ∧
      ((j = e ∧
          tokenAt kind l0 = some t ∧
          ((¬ gate ∧ i = e ∧
              tokenAt kind q.1 = some t') ∨
            (gate ∧ tokenAt kind r0 = none ∧
              ((i = e ∧ tokenAt kind q.1 = some t') ∨
                (i = rsite ∧
                  tokenAt kind q.2 = some t'))))) ∨
        (j = rsite ∧
          tokenAt kind r0 = some t ∧
          ((¬ gate ∧ i = rsite ∧
              tokenAt kind q.2 = some t') ∨
            (gate ∧
              ((i = e ∧ tokenAt kind q.1 = some t') ∨
                (i = rsite ∧
                  tokenAt kind q.2 = some t'))))) ∨
        (j = i ∧ i ≠ e ∧ i ≠ rsite ∧ t' = t))

/--
The alternative source is the literal line-14/15 birth at the initiator,
followed, when the row immediately moves it, by that same selected MoveToken.
The existing FreshAt predicate is recorded with the actual proof-step number.
-/
def SPLFreshBorderBirthImage
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (step : Nat)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (kind : TokenKind)
    (t' : TokenData psi) : Prop :=
  let rsite := ring.rightNeighbor e
  let p :=
    splProvSelectedInput hpsi kind (C e) (C rsite)
  let l0 := PPL.sourceClear kind p.1
  let r0 := PPL.sourceClear kind p.2
  let q := PPL.moveToken hpsi kind p.1 p.2
  IsBorder C e ∧
    l0.last = false ∧
    r0.last = false ∧
    tokenAt kind l0 = none ∧
    tokenAt kind r0 = none ∧
    l0.dist.val = tokenD' psi kind ∧
    ((i = e ∧ tokenAt kind q.1 = some t') ∨
      (i = rsite ∧ tokenAt kind q.2 = some t')) ∧
    ∃ m : LineageMeta n,
      FreshAt kind e m ∧
        m.id = .born kind step

def SPLPostTokenProvenance : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (step : Nat)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀ (i : Fin n) (kind : TokenKind)
      (t' : TokenData psi),
      tokenAt kind (nextConfig ring C e i) = some t' →
      SPLPostTokenOldImage
          hpsi ring C e i kind t' ∨
        SPLFreshBorderBirthImage
          hpsi step ring C e i kind t'

private theorem splProvBirthGuard_isBorder
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (e : Fin n)
    (p : State psi kappa × State psi kappa)
    (hpDist : p.1.dist = (C e).dist)
    (hb :
      (PPL.sourceClear kind p.1).dist.val =
        tokenD' psi kind) :
    IsBorder C e := by
  have hc :
      (C e).dist.val = tokenD' psi kind := by
    calc
      (C e).dist.val = p.1.dist.val := by
        exact congrArg Fin.val hpDist.symm
      _ = (PPL.sourceClear kind p.1).dist.val := by
        exact
          congrArg Fin.val
            (splProvSourceClear_dist kind p.1).symm
      _ = tokenD' psi kind := hb
  unfold IsBorder
  cases kind with
  | black =>
      exact Or.inl (by simpa [tokenD'] using hc)
  | white =>
      exact Or.inr (by simpa [tokenD'] using hc)

theorem splPostTokenProvenance_proved :
    SPLPostTokenProvenance := by
  unfold SPLPostTokenProvenance
  intro n psi kappa
  intro hn3 hpsi step ring root C e _hSPL
  intro i kind t' hpost

  let rsite := ring.rightNeighbor e
  let p :=
    splProvSelectedInput
      hpsi kind (C e) (C rsite)
  let l0 := PPL.sourceClear kind p.1
  let r0 := PPL.sourceClear kind p.2
  let q := PPL.moveToken hpsi kind p.1 p.2
  let gate := l0.last = false ∧ r0.last = false

  have hp0 :=
    splProvSelectedInput_frame
      hpsi kind (C e) (C rsite)
  have hp :
      p.1.dist = (C e).dist ∧
        tokenAt kind p.1 = tokenAt kind (C e) ∧
        tokenAt kind p.2 = tokenAt kind (C rsite) := by
    simpa [p, rsite] using hp0

  have hstep0 :=
    splProvStepTokenPair
      hn3 hpsi ring C e kind
  have hstep :
      tokenAt kind (nextConfig ring C e e) =
          tokenAt kind q.1 ∧
        tokenAt kind (nextConfig ring C e rsite) =
          tokenAt kind q.2 := by
    simpa [q, p, rsite] using hstep0

  have hpreLeft :
      ∀ t : TokenData psi,
        tokenAt kind l0 = some t →
          tokenAt kind (C e) = some t := by
    intro t ht
    have h :=
      splProvSourceClear_some kind p.1 t
        (by simpa [l0] using ht)
    rw [hp.2.1] at h
    exact h

  have hpreRight :
      ∀ t : TokenData psi,
        tokenAt kind r0 = some t →
          tokenAt kind (C rsite) = some t := by
    intro t ht
    have h :=
      splProvSourceClear_some kind p.2 t
        (by simpa [r0] using ht)
    rw [hp.2.2] at h
    exact h

  by_cases hie : i = e
  · subst i
    have hq :
        tokenAt kind q.1 = some t' := by
      rw [← hstep.1]
      exact hpost
    by_cases hg : gate
    · cases hr : tokenAt kind r0 with
      | some tr =>
          left
          unfold SPLPostTokenOldImage
          dsimp only
          refine
            ⟨rsite, tr,
              Or.inr (Or.inl rfl),
              hpreRight tr hr, ?_⟩
          exact
            Or.inr
              (Or.inl
                ⟨rfl, hr,
                  Or.inr
                    ⟨by simpa [gate] using hg,
                      Or.inl ⟨rfl, hq⟩⟩⟩)
      | none =>
          cases hl : tokenAt kind l0 with
          | some tl =>
              left
              unfold SPLPostTokenOldImage
              dsimp only
              refine
                ⟨e, tl, Or.inl rfl,
                  hpreLeft tl hl, Or.inl ?_⟩
              exact
                ⟨rfl, hl,
                  Or.inr
                    ⟨by simpa [gate] using hg,
                      by simpa [r0] using hr,
                      Or.inl ⟨rfl, hq⟩⟩⟩
          | none =>
              have hb :
                  l0.dist.val =
                    tokenD' psi kind := by
                apply
                  splProvNoLiveOutput_forces_border
                    hpsi kind p.1 p.2
                · simpa [l0, r0, gate] using hg
                · simpa [l0] using hl
                · simpa [r0] using hr
                · exact Or.inl (by simpa [q] using hq)
                all_goals exact t'
              have hborder :
                  IsBorder C e :=
                splProvBirthGuard_isBorder
                  hpsi kind C e p hp.1
                  (by simpa [l0] using hb)
              right
              unfold SPLFreshBorderBirthImage
              dsimp only
              refine
                ⟨hborder,
                  hg.1, hg.2, hl, hr, hb,
                  Or.inl ⟨rfl, hq⟩, ?_⟩
              let m : LineageMeta n :=
                { id := .born kind step
                  birthSite := e
                  birthStep := step
                  moves := 0 }
              refine ⟨m, ?_, rfl⟩
              exact ⟨step, rfl, rfl⟩
    · have hc :=
        splProvMoveToken_gate_closed
          hpsi kind p.1 p.2
          (by simpa [l0, r0, gate] using hg)
      have hc' :
          tokenAt kind q.1 = tokenAt kind l0 ∧
            tokenAt kind q.2 = tokenAt kind r0 := by
        simpa [q, l0, r0] using hc
      have hl :
          tokenAt kind l0 = some t' := by
        rw [← hc'.1]
        exact hq
      left
      unfold SPLPostTokenOldImage
      dsimp only
      refine
        ⟨e, t', Or.inl rfl,
          hpreLeft t' hl, Or.inl ?_⟩
      exact
        ⟨rfl, hl,
          Or.inl
            ⟨by simpa [gate] using hg,
              rfl, hq⟩⟩

  · by_cases hir : i = rsite
    · subst i
      have hq :
          tokenAt kind q.2 = some t' := by
        rw [← hstep.2]
        exact hpost
      by_cases hg : gate
      · cases hr : tokenAt kind r0 with
        | some tr =>
            left
            unfold SPLPostTokenOldImage
            dsimp only
            refine
              ⟨rsite, tr,
                Or.inr (Or.inl rfl),
                hpreRight tr hr, ?_⟩
            exact
              Or.inr
                (Or.inl
                  ⟨rfl, hr,
                    Or.inr
                      ⟨by simpa [gate] using hg,
                        Or.inr ⟨rfl, hq⟩⟩⟩)
        | none =>
            cases hl : tokenAt kind l0 with
            | some tl =>
                left
                unfold SPLPostTokenOldImage
                dsimp only
                refine
                  ⟨e, tl, Or.inl rfl,
                    hpreLeft tl hl, Or.inl ?_⟩
                exact
                  ⟨rfl, hl,
                    Or.inr
                      ⟨by simpa [gate] using hg,
                        by simpa [r0] using hr,
                        Or.inr ⟨rfl, hq⟩⟩⟩
            | none =>
                have hb :
                    l0.dist.val =
                      tokenD' psi kind := by
                  apply
                    splProvNoLiveOutput_forces_border
                      hpsi kind p.1 p.2
                  · simpa [l0, r0, gate] using hg
                  · simpa [l0] using hl
                  · simpa [r0] using hr
                  · exact Or.inr (by simpa [q] using hq)
                  all_goals exact t'
                have hborder :
                    IsBorder C e :=
                  splProvBirthGuard_isBorder
                    hpsi kind C e p hp.1
                    (by simpa [l0] using hb)
                right
                unfold SPLFreshBorderBirthImage
                dsimp only
                refine
                  ⟨hborder,
                    hg.1, hg.2, hl, hr, hb,
                    Or.inr ⟨rfl, hq⟩, ?_⟩
                let m : LineageMeta n :=
                  { id := .born kind step
                    birthSite := e
                    birthStep := step
                    moves := 0 }
                refine ⟨m, ?_, rfl⟩
                exact ⟨step, rfl, rfl⟩
      · have hc :=
          splProvMoveToken_gate_closed
            hpsi kind p.1 p.2
            (by simpa [l0, r0, gate] using hg)
        have hc' :
            tokenAt kind q.1 = tokenAt kind l0 ∧
              tokenAt kind q.2 = tokenAt kind r0 := by
          simpa [q, l0, r0] using hc
        have hr :
            tokenAt kind r0 = some t' := by
          rw [← hc'.2]
          exact hq
        left
        unfold SPLPostTokenOldImage
        dsimp only
        refine
          ⟨rsite, t',
            Or.inr (Or.inl rfl),
            hpreRight t' hr, ?_⟩
        exact
          Or.inr
            (Or.inl
              ⟨rfl, hr,
                Or.inl
                  ⟨by simpa [gate] using hg,
                    rfl, hq⟩⟩)
    · left
      have hframe :=
        splProvStep_other
          ring C e i hie hir
      have htC :
          tokenAt kind (C i) = some t' := by
        rw [← hframe]
        exact hpost
      unfold SPLPostTokenOldImage
      dsimp only
      refine
        ⟨i, t',
          Or.inr (Or.inr rfl),
          htC, ?_⟩
      exact
        Or.inr
          (Or.inr
            ⟨rfl, hie, hir, rfl⟩)

/-! -------------------------------------------------------------------------
    Exact no-new-risky remainder
------------------------------------------------------------------------- -/

/--
After the off-pair frame, no-new-risky has exactly two sites left.

The remaining local audit is: an old positive token preserves its physical
target under ordinary right motion; a new border token points out of S_0; and
the only positive wrap into S_0 would cross the final-to-root boundary, whose
canonical last=true value closes Algorithm 3's line-13 gate.
-/
def SPLNoNewRiskySelectedPair : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ¬ Risky ring root (nextConfig ring C e) e ∧
      ¬ Risky ring root
        (nextConfig ring C e)
        (ring.rightNeighbor e)

theorem splNoNewRisky_of_selectedPair
    (hselected : SPLNoNewRiskySelectedPair) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (root : Fin n)
      (C : Config n psi kappa)
      (e : Fin n),
      SPLAt ring root C →
      ∀ i : Fin n,
        ¬ Risky ring root
          (nextConfig ring C e) i := by
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  have hs :=
    hselected
      hn3 hpsi ring root C e hSPL
  intro i
  by_cases hie : i = e
  · subst i
    exact hs.1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      exact hs.2
    · have hframe :=
        splProvStep_other
          ring C e i hie hir
      intro hrisk
      apply hSPL.2.1 i
      unfold Risky at hrisk ⊢
      rcases hrisk with hb | hw
      · left
        unfold tokenRisky at hb ⊢
        rw [hframe] at hb
        exact hb
      · right
        unfold tokenRisky at hw ⊢
        rw [hframe] at hw
        exact hw

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splPostTokenProvenance_proved
#print axioms PPL.Safety.SPL.splNoNewRisky_of_selectedPair
