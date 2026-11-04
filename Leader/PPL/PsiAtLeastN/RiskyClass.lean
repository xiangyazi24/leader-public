import Leader.PPL.PsiAtLeastN.SafeTarget

/-!
# The closed non-S_PL class when `psi ≥ n` (ERRATA S3.14, kernel-checked)

`RiskyCDLClassAt ring root C` = rooted `C_DL` at `root` plus at least one
valid risky token.  With one segment (`segmentCount n psi = 1`, e.g.
`3 ≤ n ≤ psi`):

* `riskyCDLClassAt_step_closed`: the class is closed under every
  interaction.  `C_DL` is closed (`cdlAt_step_closed_of_single_segment`), and
  a valid token is never moved or cleared: the line-13 gate is shut (every
  `last` is `true`), line 12 clears only invalid tokens, and `dist` is frozen,
  so the token and its validity and riskiness are unchanged
  (`validToken_step_frame_of_single_segment`).
* `riskyCDLClassAt_not_SPL`: no member is in `S_PL` (the root is the unique
  leader, and `SPLAt` forbids risky tokens at that root).
* `riskyCDLClassAt_never_reaches_SPL`: hence `S_PL` is unreachable from the
  class — the Lemma-18 step "every risky token becomes non-risky" fails.
* `riskyWitness_mem`: the class is nonempty for every `3 ≤ n ≤ psi` and every
  `kappa` (canonical CDL at root 0 with a white token of offset `+1` at the
  root; the witness of `run/verification/ppl-psi-ge-n/PsiGeN.lean`).

The class is safe (it lies inside `Theorem1SafeTarget`), so the printed
Theorem 1 claim "reaches a safe configuration" is not refuted; only reaching
`S_PL` is.

The first block copies the private public-name mirrors of Algorithm 3 from
`Leader/PPL/Safety/SPLTokenProvenance.lean` (prefix `splProv` renamed
`riskyK`), unchanged.
-/

namespace PPL.PsiAtLeastN

open PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Algorithm 3 public-name mirrors (copied from `SPLTokenProvenance`) -/

/-! -------------------------------------------------------------------------
    Public-name mirrors for line 12 and the selected Algorithm-3 row
------------------------------------------------------------------------- -/

private def riskyKBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def riskyKMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def riskyKLocalValid
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
    Decidable (riskyKLocalValid kind q t) := by
  unfold riskyKLocalValid
  infer_instance

private def riskyKSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := x }
  | .white => { q with tokenW := x }

private def riskyKClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if riskyKLocalValid kind q t then
        q
      else
        riskyKSetToken kind q none

private theorem riskyKSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    PPL.sourceClear kind q =
      riskyKClearInvalid kind q := by
  cases kind <;> rfl

private theorem riskyKSourceClear_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt kind (PPL.sourceClear kind q) =
        some t) :
    tokenAt kind q = some t := by
  rw [riskyKSourceClear_eq] at h
  unfold riskyKClearInvalid at h
  cases hq : tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      rw [hq] at h
      dsimp only at h
      by_cases hv : riskyKLocalValid kind q u
      · rw [if_pos hv] at h
        rw [hq] at h
        exact h
      · rw [if_neg hv] at h
        unfold riskyKSetToken at h
        cases kind <;> simp [tokenAt] at h

private theorem riskyKSourceClear_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).dist = q.dist := by
  rw [riskyKSourceClear_eq]
  unfold riskyKClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      rfl
  | some u =>
      by_cases hv : riskyKLocalValid kind q u
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold riskyKSetToken
        cases kind <;> rfl

@[simp] private theorem riskyKSourceSet_tokenAt
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    tokenAt kind (PPL.sourceSet kind q x) = x := by
  cases kind <;> rfl

private def riskyKNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    riskyKMkToken
      (offsetPsiCode psi hpsi)
      (riskyKBitToFin (!sourceBit))
      (riskyKBitToFin sourceBit)
  else
    riskyKMkToken
      (offsetPsiCode psi hpsi)
      (riskyKBitToFin sourceBit)
      (0 : Fin 2)

private def riskyKMoveTokenMirror
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
            (riskyKMkToken
              (offsetPsiCode psi hpsi)
              (riskyKBitToFin (!l.id))
              (riskyKBitToFin l.id)))
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
                riskyKNegTurnNext hpsi l.id t
              (PPL.sourceSet kind l (some next),
                PPL.sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                riskyKMkToken
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
                (riskyKMkToken
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
            riskyKMkToken
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

private theorem riskyKMoveTokenMirror_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    riskyKMoveTokenMirror hpsi kind l r =
      PPL.moveToken hpsi kind l r := by
  cases kind <;> rfl

private theorem riskyKMoveToken_gate_closed
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
  rw [← riskyKMoveTokenMirror_eq hpsi kind l r]
  simp [riskyKMoveTokenMirror, hgate]
private theorem riskyKDetermineMode_frame
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

private theorem riskyKLine6_frame
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

private theorem riskyKPreToken_frame
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
  have hd0 := riskyKDetermineMode_frame kind l r
  have hd :
      d.1.dist = l.dist ∧
        tokenAt kind d.1 = tokenAt kind l ∧
        tokenAt kind d.2 = tokenAt kind r := by
    simpa [d] using hd0
  have hs0 := riskyKLine6_frame hpsi kind l r
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

private theorem riskyKBlackPreservesWhite
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

private theorem riskyKMoveToken_left_dist
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

private def riskyKSelectedInput
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

private theorem riskyKSelectedInput_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := riskyKSelectedInput hpsi kind l r
    p.1.dist = l.dist ∧
      tokenAt kind p.1 = tokenAt kind l ∧
      tokenAt kind p.2 = tokenAt kind r := by
  cases kind with
  | black =>
      simpa [riskyKSelectedInput] using
        (riskyKPreToken_frame
          hpsi TokenKind.black l r)
  | white =>
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair hpsi l r
      have hp :=
        riskyKPreToken_frame
          hpsi TokenKind.white l r
      have hb :=
        riskyKBlackPreservesWhite
          hpsi p.1 p.2
      have hbd :=
        riskyKMoveToken_left_dist
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

private theorem riskyKElimTokenLeft
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

private theorem riskyKElimTokenRight
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

private theorem riskyKWhitePreservesBlack
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

private theorem riskyKPplSelectedTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := riskyKSelectedInput hpsi kind l r
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
        riskyKWhitePreservesBlack hpsi b.1 b.2
      have hel :=
        riskyKElimTokenLeft .black w.1 w.2
      have her :=
        riskyKElimTokenRight .black w.1 w.2
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
        riskyKElimTokenLeft .white w.1 w.2
      have her :=
        riskyKElimTokenRight .white w.1 w.2
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

private theorem riskyKRightNeighbor_ne_self
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

private theorem riskyKStepTokenPair
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    let p :=
      riskyKSelectedInput hpsi kind
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
    riskyKRightNeighbor_ne_self hn3 ring e
  have hp :=
    riskyKPplSelectedTokenPair
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

private theorem riskyKStep_other
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    nextConfig ring C e i = C i := by
  unfold nextConfig PopulationProtocol.step
  simp [hie, hir]


/-! ## A valid token is frozen when the gate is shut -/

/-- Line 12 keeps a locally valid token: `clearInvalid` is the identity. -/
private theorem riskyKSourceClear_of_valid
    {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) (ht : tokenAt kind q = some t)
    (hv : riskyKLocalValid kind q t) :
    PPL.sourceClear kind q = q := by
  rw [riskyKSourceClear_eq]
  unfold riskyKClearInvalid
  rw [ht]
  dsimp only
  rw [if_pos hv]

/-- Local validity reads the host only through `dist`. -/
private theorem riskyKLocalValid_of_dist
    {psi kappa : Nat} (kind : TokenKind) (q q' : State psi kappa)
    (t : TokenData psi) (hd : q'.dist = q.dist)
    (hv : riskyKLocalValid kind q t) :
    riskyKLocalValid kind q' t := by
  unfold riskyKLocalValid tokenTargetCoordinate at hv ⊢
  rw [hd]
  exact hv

/-- `ValidToken` unfolds to local validity of the hosted token. -/
private theorem riskyKValidToken_some
    {n psi kappa : Nat} (kind : TokenKind) (C : Config n psi kappa)
    (i : Fin n) (hv : ValidToken kind C i) :
    Exists fun t : TokenData psi =>
      And (tokenAt kind (C i) = some t) (riskyKLocalValid kind (C i) t) := by
  unfold ValidToken at hv
  cases ht : tokenAt kind (C i) with
  | none =>
      rw [ht] at hv
      exact hv.elim
  | some t =>
      rw [ht] at hv
      exact ⟨t, rfl, hv⟩

/-- In the single-segment CDL geometry the selected `MoveToken` call sees an
initiator with `last = true`, and a responder with its original `dist`. -/
private theorem riskyKSelectedInput_last_dist
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hseg : segmentCount n psi = 1) (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) (e : Fin n)
    (hC : CDLAt ring root C) (kind : TokenKind) :
    let P := riskyKSelectedInput hpsi kind (C e) (C (ring.rightNeighbor e))
    And (P.1.last = true) (P.2.dist = (C (ring.rightNeighbor e)).dist) := by
  have hL := cdlAlgorithm2LastWriteIdempotent hn3 hpsi ring root C e hC
  have hD := cdlAlgorithm2DistWriteIdempotent hn3 hpsi ring root C e hC
  dsimp only at hL hD
  have hp1 :
      (PPL.Safety.PeacefulProps.preTokenPair hpsi (C e)
        (C (ring.rightNeighbor e))).1.last = true :=
    hL.1.trans (cdlAt_last_true_of_single_segment hseg hC e)
  have hp2 :
      (PPL.Safety.PeacefulProps.preTokenPair hpsi (C e)
        (C (ring.rightNeighbor e))).2.dist = (C (ring.rightNeighbor e)).dist :=
    hD.2.2.2.2.1
  cases kind with
  | black =>
      exact ⟨hp1, hp2⟩
  | white =>
      have hI :=
        eraseKindToken_fields
          (PPL.moveToken_initiator_fields hpsi .black
            (PPL.Safety.PeacefulProps.preTokenPair hpsi (C e)
              (C (ring.rightNeighbor e))).1
            (PPL.Safety.PeacefulProps.preTokenPair hpsi (C e)
              (C (ring.rightNeighbor e))).2)
      have hR :=
        eraseKindToken_fields
          (moveToken_responder_eq_of_initiator_last hpsi .black
            (PPL.Safety.PeacefulProps.preTokenPair hpsi (C e)
              (C (ring.rightNeighbor e))).1
            (PPL.Safety.PeacefulProps.preTokenPair hpsi (C e)
              (C (ring.rightNeighbor e))).2 hp1)
      exact ⟨hI.2.2.2.trans hp1, hR.2.2.1.trans hp2⟩

/-- **A valid token never moves, changes or disappears** in one interaction
from a single-segment rooted CDL configuration; `dist` is frozen too. -/
theorem validToken_step_frame_of_single_segment
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hseg : segmentCount n psi = 1) (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) (e : Fin n)
    (hC : CDLAt ring root C) (kind : TokenKind) (i : Fin n)
    (hv : ValidToken kind C i) :
    And (tokenAt kind (nextConfig ring C e i) = tokenAt kind (C i))
      ((nextConfig ring C e i).dist = (C i).dist) := by
  have hframe := cdlSingleSegmentFieldFrame hn3 hpsi hseg ring root C e hC
  dsimp only at hframe
  have hdist := hframe.2.1 i
  refine ⟨?_, hdist⟩
  obtain ⟨t, ht, hvt⟩ := riskyKValidToken_some kind C i hv
  let j := ring.rightNeighbor e
  let P := riskyKSelectedInput hpsi kind (C e) (C j)
  have hsel := riskyKSelectedInput_frame hpsi kind (C e) (C j)
  have hld := riskyKSelectedInput_last_dist hn3 hpsi hseg ring root C e hC kind
  dsimp only at hsel hld
  have hcl1 : (PPL.sourceClear kind P.1).last = true :=
    (eraseKindToken_fields (erase_sourceClear_eq kind P.1)).2.2.2.trans hld.1
  have hgate :
      ¬ ((PPL.sourceClear kind P.1).last = false ∧
        (PPL.sourceClear kind P.2).last = false) := by
    intro h
    rw [hcl1] at h
    exact absurd h.1 (by simp)
  have hmg := riskyKMoveToken_gate_closed hpsi kind P.1 P.2 hgate
  have hst := riskyKStepTokenPair hn3 hpsi ring C e kind
  dsimp only at hmg hst
  by_cases hie : i = e
  · subst hie
    have hvP : riskyKLocalValid kind P.1 t :=
      riskyKLocalValid_of_dist kind (C i) P.1 t hsel.1 hvt
    have hPt : tokenAt kind P.1 = some t := hsel.2.1.trans ht
    have hclr := riskyKSourceClear_of_valid kind P.1 t hPt hvP
    rw [hst.1, hmg.1, hclr, hPt, ht]
  · by_cases hij : i = j
    · subst hij
      have hvP : riskyKLocalValid kind P.2 t :=
        riskyKLocalValid_of_dist kind (C (ring.rightNeighbor e)) P.2 t
          hld.2 hvt
      have hPt : tokenAt kind P.2 = some t := hsel.2.2.trans ht
      have hclr := riskyKSourceClear_of_valid kind P.2 t hPt hvP
      rw [hst.2, hmg.2, hclr, hPt, ht]
    · rw [riskyKStep_other ring C e i hie hij]

/-- Transfer of `ValidToken` along equal hosted token and `dist`. -/
theorem validToken_of_token_dist_eq
    {n psi kappa : Nat} (kind : TokenKind) (C D : Config n psi kappa)
    (i : Fin n) (ht : tokenAt kind (D i) = tokenAt kind (C i))
    (hd : (D i).dist = (C i).dist) (hv : ValidToken kind C i) :
    ValidToken kind D i := by
  obtain ⟨t, hct, hvt⟩ := riskyKValidToken_some kind C i hv
  unfold ValidToken
  rw [ht, hct]
  exact riskyKLocalValid_of_dist kind (C i) (D i) t hd hvt

/-- Transfer of `tokenRisky` along an equal hosted token. -/
theorem tokenRisky_of_token_eq
    {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n)
    (kind : TokenKind) (C D : Config n psi kappa) (i : Fin n)
    (ht : tokenAt kind (D i) = tokenAt kind (C i))
    (hr : tokenRisky ring root C i kind) :
    tokenRisky ring root D i kind := by
  unfold tokenRisky at hr ⊢
  rw [ht]
  exact hr

/-! ## The class K and its closure -/

/-- ERRATA S3.14's class `K(root)`: rooted `C_DL` at `root` and at least one
valid risky token. -/
def RiskyCDLClassAt {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) : Prop :=
  And (CDLAt ring root C)
    (Exists fun i : Fin n => Exists fun kind : TokenKind =>
      And (ValidToken kind C i) (tokenRisky ring root C i kind))

/-- **K is closed** under every interaction when there is one segment. -/
theorem riskyCDLClassAt_step_closed
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hseg : segmentCount n psi = 1) (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) (e : Fin n)
    (hK : RiskyCDLClassAt ring root C) :
    RiskyCDLClassAt ring root
      (PopulationProtocol.step (PPL.protocol psi kappa) ring C e) := by
  obtain ⟨hC, i, kind, hv, hr⟩ := hK
  have hfr :=
    validToken_step_frame_of_single_segment hn3 hpsi hseg ring root C e hC
      kind i hv
  refine ⟨cdlAt_step_closed_of_single_segment hn3 hpsi hseg ring root C e hC,
    i, kind, ?_, ?_⟩
  · exact validToken_of_token_dist_eq kind C (nextConfig ring C e) i
      hfr.1 hfr.2 hv
  · exact tokenRisky_of_token_eq ring root kind C (nextConfig ring C e) i
      hfr.1 hr

/-- Closed-predicate form. -/
theorem riskyCDLClassAt_closedPred
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hseg : segmentCount n psi = 1) (ring : DirectedRing n)
    (root : Fin n) :
    PopulationProtocol.ClosedPred (PPL.protocol psi kappa) ring
      (RiskyCDLClassAt ring root) := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  exact riskyCDLClassAt_step_closed hn3 hpsi hseg ring root C e hC

/-- **K is disjoint from `S_PL`** (any number of segments). -/
theorem riskyCDLClassAt_not_SPL
    {n psi kappa : Nat} {ring : DirectedRing n} {root : Fin n}
    {C : Config n psi kappa} (hK : RiskyCDLClassAt ring root C) :
    ¬ SPL ring C := by
  intro hspl
  rcases hspl with ⟨root', hroot'⟩
  have hlead : (C root).leader = true := (hK.1.2.1 root).2 rfl
  have hsame : root = root' := (hroot'.1.2.1 root).1 hlead
  subst hsame
  obtain ⟨i, kind, _, hr⟩ := hK.2
  apply hroot'.2.1 i
  cases kind with
  | black => exact Or.inl hr
  | white => exact Or.inr hr

/-- **S_PL is unreachable from K** when there is one segment. -/
theorem riskyCDLClassAt_never_reaches_SPL
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hseg : segmentCount n psi = 1) (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa)
    (hK : RiskyCDLClassAt ring root C) :
    forall C' : Config n psi kappa,
      PopulationProtocol.Reachable (PPL.protocol psi kappa) ring C C' ->
        ¬ SPL ring C' := by
  intro C' hr
  exact riskyCDLClassAt_not_SPL
    (PopulationProtocol.ClosedPred.reachable
      (riskyCDLClassAt_closedPred hn3 hpsi hseg ring root) hK hr)

/-- K lies inside the safe target (so K is safe). -/
theorem riskyCDLClassAt_safeTarget
    {n psi kappa : Nat} (hseg : segmentCount n psi = 1)
    {ring : DirectedRing n} {root : Fin n} {C : Config n psi kappa}
    (hK : RiskyCDLClassAt ring root C) :
    Theorem1SafeTarget ring C :=
  Or.inr ⟨hseg, root, hK.1⟩

/-! ## Non-vacuity: a member of K for every `3 ≤ n ≤ psi` -/

/-- Canonical rooted CDL at agent 0 (all `last = true`), no bullets, with a
white token of offset `+1` at the root. -/
def riskyWitness (n psi kappa : Nat) (hpsi : 2 ≤ psi) :
    Config n psi kappa := fun i =>
  { leader := decide (i.val = 0)
    id := false
    dist := ⟨i.val % (2 * psi), Nat.mod_lt _ (by omega)⟩
    last := true
    tokenB := none
    tokenW :=
      if i.val = 0 then some ((offsetOneCode psi hpsi, 0), 0) else none
    mode := false
    clock := ⟨0, Nat.succ_pos _⟩
    signalR := ⟨0, Nat.succ_pos _⟩
    hits := ⟨0, Nat.succ_pos _⟩
    bullet := 0
    shield := false
    signalB := false }

/-- **K is nonempty**: the witness is in `K(0)` for every `3 ≤ n ≤ psi`, any
ring and any `kappa`. -/
theorem riskyWitness_mem
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hge : n ≤ psi)
    (ring : DirectedRing n) :
    RiskyCDLClassAt ring ⟨0, by omega⟩ (riskyWitness n psi kappa hpsi) := by
  have hseg : segmentCount n psi = 1 := segmentCount_eq_one_of_le (by omega) hge
  have hoff : forall i : Fin n,
      cyclicOffset ring ⟨0, by omega⟩ i = i.val := by
    intro i
    unfold cyclicOffset
    simp only [Nat.sub_zero, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt i.isLt
  have hdec : decodeOffset psi (offsetOneCode psi hpsi) = 1 :=
    decodeOffset_one psi hpsi
  have htok :
      tokenAt .white (riskyWitness n psi kappa hpsi ⟨0, by omega⟩) =
        some ((offsetOneCode psi hpsi, 0), 0) := by
    simp [riskyWitness, tokenAt]
  refine ⟨⟨⟨⟨⟨0, by omega⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ⟨0, by omega⟩, .white, ?_, ?_⟩
  · simp [riskyWitness]
  · intro i hb
    simp [riskyWitness] at hb
  · intro i
    simp [riskyWitness, Fin.ext_iff]
  · intro i
    dsimp only
    rw [hoff i, hseg]
    refine ⟨rfl, ?_⟩
    simp [riskyWitness]
  · unfold ValidToken
    rw [htok]
    dsimp only
    left
    have htgt :
        tokenTargetCoordinate .white
            (riskyWitness n psi kappa hpsi ⟨0, by omega⟩)
            ((offsetOneCode psi hpsi, 0), 0) =
          ((psi : Nat) : Int) + 1 := by
      unfold tokenTargetCoordinate
      have hd :
          (riskyWitness n psi kappa hpsi ⟨0, by omega⟩).dist.val = 0 := by
        simp [riskyWitness]
      simp only [tokenCode, hdec, tokenD', hd]
      rw [Int.emod_eq_of_lt] <;> omega
    rw [htgt]
    simp only [tokenCode, hdec]
    omega
  · unfold tokenRisky
    rw [htok]
    dsimp only
    refine ⟨by simp only [tokenCode, hdec]; omega, ?_⟩
    intro h
    have hh : h.val < 2 := by
      have := h.isLt
      simp only [tokenCode, hdec] at this
      exact this
    unfold InSegment
    dsimp only
    rw [hoff]
    unfold shiftRight
    dsimp only
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
    refine ⟨Nat.zero_le _, ?_⟩
    have hmin : Nat.min psi n = n := Nat.min_eq_right hge
    rw [hmin]
    omega

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.validToken_step_frame_of_single_segment
#print axioms PPL.PsiAtLeastN.riskyCDLClassAt_step_closed
#print axioms PPL.PsiAtLeastN.riskyCDLClassAt_not_SPL
#print axioms PPL.PsiAtLeastN.riskyCDLClassAt_never_reaches_SPL
#print axioms PPL.PsiAtLeastN.riskyCDLClassAt_safeTarget
#print axioms PPL.PsiAtLeastN.riskyWitness_mem
