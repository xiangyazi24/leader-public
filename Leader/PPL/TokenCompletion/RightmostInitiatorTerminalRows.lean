import Leader.PPL.TokenCompletion.RightmostInitiatorTerminalLocal
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Lemma 4, rightmost initiator: the two terminal local rows

This file proves the two residual rows of
`TokenCorrectnessLemma4RightmostInitiatorTerminalLocal`:

* `Lemma4RightmostInitiatorTerminalFinalShapeRow`: a tracked rightmost
  initiator that leaves no same-ID owner in either selected output sits at
  window coordinate `2*psi-2` with offset `1`;
* `Lemma4RightmostInitiatorTerminalFinalCompletionRow`: that final `c = 1`
  service logs a fresh completion;

and hence the state-local terminal residual.

Proof architecture.  Pre/post `C_d` fix the `dist`/`last` fields of the
selected-colour inputs of the interaction (the selected move preserves those
fields, and the literal step output agrees with the selected output on them).
The selected-colour token of each input is the physical token.  Hence:

1. the tracked initiator is live and shadowed by `z` in the selected input;
2. it is not at the last coordinate `2*psi-1` (no Definition-3 valid token
   can sit there under `C_d`), so the responder is the next window site;
3. rightmostness gives the responder no ghost owner, and coverage then rules
   out any valid physical responder token, so the responder live value is
   empty.

With these facts the literal ghost move takes one explicit branch per offset
class: `c < 0` keeps `z` on the left, `c >= 2` bumps `z` to a valid right
token, and `c = 1` bumps `z` to a valid right token unless `x = 2*psi-2`.
In the terminal branch the bump logs the advanced metadata, whose move count
is the Definition-4 trajectory length by the intrinsic kinematics and the
strict age bound (which pins the unwrapped coordinate to the first lap).

The selected-colour mirror below is copied from
`TokenCorrectnessLemma4SweepEmptyBirth` (renamed); it is definitionally the
private mirror inside `TokenCorrectness`.
-/

private def rtrBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def rtrMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def rtrLocalValid
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


private instance instDecidableRtrLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (rtrLocalValid kind q t) := by
  unfold rtrLocalValid
  infer_instance


private def rtrSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def rtrClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if rtrLocalValid kind q t then
        q
      else
        rtrSetToken kind q none


private def rtrLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


private theorem rtrSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      rtrSetToken kind q t := by
  cases kind <;> rfl


private theorem rtrSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      rtrClearInvalid kind q := by
  cases kind <;> rfl


private theorem rtrSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = rtrLeaderBirth q := by
  rfl


private theorem rtrSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q t) = t := by
  rw [rtrSourceSet_eq]
  cases kind <;> rfl


private theorem rtrSourceSet_static
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).dist = q.dist ∧
      (sourceSet kind q t).last = q.last ∧
      (sourceSet kind q t).id = q.id := by
  rw [rtrSourceSet_eq]
  cases kind <;> exact ⟨rfl, rfl, rfl⟩


private def rtrLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if rtrLocalValid kind q t then
        some t
      else
        none


private theorem rtrSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      rtrLiveValue kind q := by
  rw [rtrSourceClear_eq]
  unfold rtrClearInvalid rtrLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : rtrLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold rtrSetToken
        cases kind <;> rfl


private theorem rtrSourceClear_static
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    let q0 := sourceClear kind q
    q0.dist = q.dist ∧
      q0.last = q.last ∧
      q0.id = q.id := by
  dsimp only
  rw [rtrSourceClear_eq]
  unfold rtrClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      refine ⟨?_, ?_, ?_⟩ <;>
        first | rfl | trivial
  | some t =>
      by_cases hv : rtrLocalValid kind q t
      · simp only [if_pos hv]
        refine ⟨?_, ?_, ?_⟩ <;>
          first | rfl | trivial
      · simp only [if_neg hv]
        unfold rtrSetToken
        cases kind <;>
          (refine ⟨?_, ?_, ?_⟩ <;>
            first | rfl | trivial)


private def rtrNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    rtrMkToken
      (offsetPsiCode psi hpsi)
      (rtrBitToFin (!sourceBit))
      (rtrBitToFin sourceBit)
  else
    rtrMkToken
      (offsetPsiCode psi hpsi)
      (rtrBitToFin sourceBit)
      (0 : Fin 2)


private def rtrPrelude
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


private def rtrSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := rtrPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2


private def rtrSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := rtrSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2


/-! ## Selected input field frames -/


private theorem rtrDetermineMode_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
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


private theorem rtrThroughLine6_token
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := createLeaderThroughLine6 hpsi l r
    tokenAt kind q.left = tokenAt kind l ∧
      tokenAt kind q.right = tokenAt kind r := by
  have hd := rtrDetermineMode_token kind l r
  dsimp only
  by_cases hguard :
      createLeaderLine6Guard hpsi l r
  · simp only
      [createLeaderThroughLine6, if_pos hguard]
    constructor
    · exact hd.1
    · change
        tokenAt kind
            (sourceBirth (determineMode l r).2) =
          tokenAt kind r
      rw [rtrSourceBirth_eq]
      cases kind <;>
        simpa [rtrLeaderBirth, tokenAt]
          using hd.2
  · simp only
      [createLeaderThroughLine6, if_neg hguard]
    exact hd


private theorem rtrPrelude_token
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (rtrPrelude hpsi l r).1 =
        tokenAt kind l ∧
      tokenAt kind (rtrPrelude hpsi l r).2 =
        tokenAt kind r := by
  have hs :=
    rtrThroughLine6_token
      hpsi kind l r
  dsimp only at hs
  constructor
  · calc
      tokenAt kind
            (rtrPrelude hpsi l r).1 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).left := by
        unfold rtrPrelude
        cases kind <;>
          (try simp only [tokenAt]) <;>
          (repeat' split) <;>
          (try rfl)
      _ = tokenAt kind l := hs.1
  · calc
      tokenAt kind
            (rtrPrelude hpsi l r).2 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).right := by
        unfold rtrPrelude
        cases kind <;>
          (try simp only [tokenAt]) <;>
          (repeat' split) <;>
          (try rfl)
      _ = tokenAt kind r := hs.2


private theorem rtrBlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .white
        (moveToken hpsi .black l r).1 =
        tokenAt .white l ∧
      tokenAt .white
        (moveToken hpsi .black l r).2 =
        tokenAt .white r := by
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


private theorem rtrSelectedInput_token
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (rtrSelectedInput hpsi kind l r).1 =
        tokenAt kind l ∧
      tokenAt kind
        (rtrSelectedInput hpsi kind l r).2 =
        tokenAt kind r := by
  cases kind with
  | black =>
      exact
        rtrPrelude_token
          hpsi .black l r
  | white =>
      let p := rtrPrelude hpsi l r
      have hp :=
        rtrPrelude_token
          hpsi .white l r
      have hb :=
        rtrBlackPreservesWhite
          hpsi p.1 p.2
      dsimp only [rtrSelectedInput]
      exact
        ⟨hb.1.trans hp.1,
          hb.2.trans hp.2⟩


private structure RtrStaticFrame
    {psi kappa : Nat}
    (before after :
      State psi kappa × State psi kappa) : Prop where
  leftDist : after.1.dist = before.1.dist
  leftLast : after.1.last = before.1.last
  rightDist : after.2.dist = before.2.dist
  rightLast : after.2.last = before.2.last


private theorem rtrMove_static
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    RtrStaticFrame
      (l, r) (moveToken hpsi kind l r) := by
  have hi :=
    moveToken_initiator_fields hpsi kind l r
  have hleftDist :
      (moveToken hpsi kind l r).1.dist = l.dist := by
    have h :=
      congrArg
        (fun q : State psi kappa => q.dist) hi
    cases kind <;>
      simpa [eraseKindToken] using h
  have hleftLast :
      (moveToken hpsi kind l r).1.last = l.last := by
    have h :=
      congrArg
        (fun q : State psi kappa => q.last) hi
    cases kind <;>
      simpa [eraseKindToken] using h
  rcases
      moveToken_responder_fields
        hpsi kind l r with hr | hr
  · have hrightDist :
        (moveToken hpsi kind l r).2.dist = r.dist := by
      have h :=
        congrArg
          (fun q : State psi kappa => q.dist) hr
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken]
          using h
    have hrightLast :
        (moveToken hpsi kind l r).2.last = r.last := by
      have h :=
        congrArg
          (fun q : State psi kappa => q.last) hr
      cases kind <;>
        simpa [eraseKindTokenId, eraseKindToken]
          using h
    exact
      { leftDist := hleftDist
        leftLast := hleftLast
        rightDist := hrightDist
        rightLast := hrightLast }
  · have hrightDist :
        (moveToken hpsi kind l r).2.dist = r.dist := by
      have h :=
        congrArg
          (fun q : State psi kappa => q.dist) hr
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken,
            birthFields] using h
    have hrightLast :
        (moveToken hpsi kind l r).2.last = r.last := by
      have h :=
        congrArg
          (fun q : State psi kappa => q.last) hr
      cases kind <;>
        simpa
          [eraseKindTokenId, eraseKindToken,
            birthFields] using h
    exact
      { leftDist := hleftDist
        leftLast := hleftLast
        rightDist := hrightDist
        rightLast := hrightLast }


private structure RtrPairFrame
    {psi kappa : Nat}
    (kind : TokenKind)
    (before after :
      State psi kappa × State psi kappa) : Prop where
  leftToken :
    tokenAt kind after.1 =
      tokenAt kind before.1
  leftDist : after.1.dist = before.1.dist
  leftLast : after.1.last = before.1.last
  rightToken :
    tokenAt kind after.2 =
      tokenAt kind before.2
  rightDist : after.2.dist = before.2.dist
  rightLast : after.2.last = before.2.last


private theorem rtrEliminate_frame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    RtrPairFrame
      kind (l, r) (eliminateLeaders l r) := by
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  cases kind with
  | black =>
      exact
        { leftToken := by
            have h :=
              congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.tokenB) hl
            simpa [PPL.Elim.otherView, tokenAt]
              using h
          leftDist :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.dist) hl
          leftLast :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.last) hl
          rightToken := by
            have h :=
              congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.tokenB) hr
            simpa [PPL.Elim.otherView, tokenAt]
              using h
          rightDist :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.dist) hr
          rightLast :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.last) hr }
  | white =>
      exact
        { leftToken := by
            have h :=
              congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.tokenW) hl
            simpa [PPL.Elim.otherView, tokenAt]
              using h
          leftDist :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.dist) hl
          leftLast :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.last) hl
          rightToken := by
            have h :=
              congrArg
                (fun q : PPL.Elim.OtherFields
                  psi kappa => q.tokenW) hr
            simpa [PPL.Elim.otherView, tokenAt]
              using h
          rightDist :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.dist) hr
          rightLast :=
            congrArg
              (fun q : PPL.Elim.OtherFields
                psi kappa => q.last) hr }


private theorem rtrWhite_preserves_black_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    RtrPairFrame
      .black (l, r)
      (moveToken hpsi .white l r) := by
  have hs :=
    rtrMove_static
      hpsi .white l r
  have hi :=
    moveToken_initiator_fields
      hpsi TokenKind.white l r
  have htokL :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  have htokR :
      tokenAt .black
          (moveToken hpsi .white l r).2 =
        tokenAt .black r := by
    rcases
        moveToken_responder_fields
          hpsi TokenKind.white l r with hr | hr
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          tokenAt] using h
    · have h :=
        congrArg
          (fun q : State psi kappa => q.tokenB) hr
      simpa
        [eraseKindTokenId, eraseKindToken,
          birthFields, tokenAt] using h
  exact
    { leftToken := by
        simpa [eraseKindToken, tokenAt] using htokL
      leftDist := hs.leftDist
      leftLast := hs.leftLast
      rightToken := htokR
      rightDist := hs.rightDist
      rightLast := hs.rightLast }


private theorem rtrPplSelected_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let s := rtrSelectedOutput hpsi kind l r
    let q := ppl hpsi l r
    RtrPairFrame kind s q := by
  cases kind with
  | black =>
      let p := rtrPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        rtrWhite_preserves_black_frame
          hpsi b.1 b.2
      have he :=
        rtrEliminate_frame
          TokenKind.black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          rtrSelectedOutput
              hpsi TokenKind.black l r =
            b := by
        rfl
      rw [hfull, hselected]
      exact
        { leftToken :=
            he.leftToken.trans hw.leftToken
          leftDist :=
            he.leftDist.trans hw.leftDist
          leftLast :=
            he.leftLast.trans hw.leftLast
          rightToken :=
            he.rightToken.trans hw.rightToken
          rightDist :=
            he.rightDist.trans hw.rightDist
          rightLast :=
            he.rightLast.trans hw.rightLast }
  | white =>
      let p := rtrPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        rtrEliminate_frame
          TokenKind.white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          rtrSelectedOutput
              hpsi TokenKind.white l r =
            w := by
        rfl
      rw [hfull, hselected]
      exact he


private theorem rtrStep_endpoints
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (ghostStep hpsi ring step G e).phys e =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).1 ∧
      (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) =
        (ppl hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))).2 := by
  have hp :=
    ghostStep_phys_export
      hpsi ring step G e
  constructor
  · rw [hp]
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi]
  · rw [hp]
    simp
      [PopulationProtocol.step, protocol,
        transition, hpsi, hne]


private theorem rtrCdGeometryEq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (hC : Cd ring k kind C)
    (hC' : Cd ring k kind C')
    (i : Fin n)
    (hi : Lemma4InWindow ring k psi i) :
    (C i).dist = (C' i).dist ∧
      (C i).last = (C' i).last := by
  rcases hi with ⟨x, rfl⟩
  have h0 := hC x
  have h1 := hC' x
  dsimp only at h0 h1
  constructor
  · apply Fin.ext
    exact h0.1.trans h1.1.symm
  · exact h0.2.trans h1.2.symm


private theorem rtrSelectedInput_static_pre
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
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
    (hwinL : Lemma4InWindow ring k psi e)
    (hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e)) :
    let p :=
      rtrSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    p.1.dist = (G.phys e).dist ∧
      p.1.last = (G.phys e).last ∧
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist ∧
      p.2.last =
        (G.phys (ring.rightNeighbor e)).last := by
  let p :=
    rtrSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  let s := moveToken hpsi kind p.1 p.2
  let q := ppl hpsi
    (G.phys e)
    (G.phys (ring.rightNeighbor e))
  have hm :=
    rtrMove_static
      hpsi kind p.1 p.2
  have hf :=
    rtrPplSelected_frame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hs :=
    rtrStep_endpoints
      hpsi ring step G e hne
  have hgL :=
    rtrCdGeometryEq
      ring k kind G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' e hwinL
  have hgR :=
    rtrCdGeometryEq
      ring k kind G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' (ring.rightNeighbor e) hwinR
  dsimp only at hf
  have hsL :
      q.1 =
        (ghostStep hpsi ring step G e).phys e := by
    exact hs.1.symm
  have hsR :
      q.2 =
        (ghostStep hpsi ring step G e).phys
          (ring.rightNeighbor e) := by
    exact hs.2.symm
  dsimp only [p, s, q] at hm hsL hsR
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      p.1.dist = s.1.dist :=
        hm.leftDist.symm
      _ = q.1.dist :=
        hf.leftDist.symm
      _ =
          ((ghostStep hpsi ring step G e).phys e).dist := by
        rw [hsL]
      _ = (G.phys e).dist :=
        hgL.1.symm
  · calc
      p.1.last = s.1.last :=
        hm.leftLast.symm
      _ = q.1.last :=
        hf.leftLast.symm
      _ =
          ((ghostStep hpsi ring step G e).phys e).last := by
        rw [hsL]
      _ = (G.phys e).last :=
        hgL.2.symm
  · calc
      p.2.dist = s.2.dist :=
        hm.rightDist.symm
      _ = q.2.dist :=
        hf.rightDist.symm
      _ =
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).dist := by
        rw [hsR]
      _ =
          (G.phys (ring.rightNeighbor e)).dist :=
        hgR.1.symm
  · calc
      p.2.last = s.2.last :=
        hm.rightLast.symm
      _ = q.2.last :=
        hf.rightLast.symm
      _ =
          ((ghostStep hpsi ring step G e).phys
            (ring.rightNeighbor e)).last := by
        rw [hsR]
      _ =
          (G.phys (ring.rightNeighbor e)).last :=
        hgR.2.symm


private def rtrBirthValue
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (idBit : Bool) : TokenData psi :=
  rtrMkToken
    (offsetPsiCode psi hpsi)
    (rtrBitToFin (!idBit))
    (rtrBitToFin idBit)

private def rtrBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value := rtrBirthValue hpsi idBit
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def rtrLiveShadow
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
              rtrLocalValid kind q t then
            some z
          else
            none


private def rtrBumpTo
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
        if rtrLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def rtrFinishMove
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
          rtrMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          rtrBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          rtrMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          rtrBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                rtrNegTurnNext hpsi l.id t
              let b :=
                rtrBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                rtrMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                rtrBumpTo kind l next gr0
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
              rtrNegTurnNext hpsi l.id t
            let b :=
              rtrBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              rtrMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              rtrBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩


private def rtrGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := rtrLiveValue kind l
  let rv0 := rtrLiveValue kind r
  let gl0 := rtrLiveShadow kind l gl
  let gr0 := rtrLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (rtrBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (rtrBirthGhost
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
    rtrFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩


private def rtrSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    rtrSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  rtrGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))


private theorem rtrSelectedPair_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    rtrSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

private theorem rtrShiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) :
    shiftRight ring k 0 = k := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt k.isLt]


private theorem rtrRightNeighbor_eq_shiftOne
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) :
    ring.rightNeighbor k =
      shiftRight ring k 1 := by
  rfl


private theorem rtrCd_window_fits
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
  have hnlt : n < 2 * psi := by
    omega
  let x0 : Fin (2 * psi) :=
    ⟨0, by omega⟩
  let xn : Fin (2 * psi) :=
    ⟨n, hnlt⟩
  have h0 := (hCd x0).1
  have hnrow := (hCd xn).1
  dsimp only [x0, xn] at h0 hnrow
  have hs :
      shiftRight ring k 0 =
        shiftRight ring k n := by
    apply Fin.ext
    simp only [shiftRight]
    rw [Nat.add_zero,
      Nat.mod_eq_of_lt k.isLt,
      Nat.add_mod_right,
      Nat.mod_eq_of_lt k.isLt]
  rw [hs] at h0
  have heq := h0.symm.trans hnrow
  cases kind with
  | black =>
      simp only [tokenD', Nat.add_zero,
        Nat.zero_mod] at heq
      rw [Nat.mod_eq_of_lt hnlt] at heq
      have hnpos := ring.hn
      omega
  | white =>
      simp only [tokenD', Nat.zero_add] at heq
      rw [Nat.mod_eq_of_lt
        (by omega : psi < 2 * psi)] at heq
      by_cases hsum : n + psi < 2 * psi
      · rw [Nat.mod_eq_of_lt hsum] at heq
        have hnpos := ring.hn
        omega
      · have hge : 2 * psi ≤ n + psi := by
          omega
        have hsub :
            n + psi - 2 * psi < 2 * psi := by
          omega
        rw [Nat.mod_eq_sub_mod hge,
          Nat.mod_eq_of_lt hsub] at heq
        have hnpos := ring.hn
        omega


private theorem rtrCyclicOffset_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (d : Nat)
    (hd : d < n) :
    cyclicOffset ring k
        (shiftRight ring k d) = d := by
  unfold cyclicOffset
  change
    (((k.val + d) % n + n - k.val) % n) = d
  by_cases hs : k.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        k.val + d + n - k.val =
          n + d := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt hd]
  · have hge : n ≤ k.val + d := by
      omega
    have hlt : k.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        k.val + d - n + n - k.val = d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]


private theorem rtrWindowSites_ne
    {n psi : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (hfit : 2 * psi ≤ n)
    (x y : Fin (2 * psi))
    (hxy : x.val ≠ y.val) :
    shiftRight ring k x.val ≠
      shiftRight ring k y.val := by
  intro h
  have hc :=
    congrArg
      (fun i : Fin n =>
        cyclicOffset ring k i) h
  have hxlt : x.val < n := by
    omega
  have hylt : y.val < n := by
    omega
  rw [
    rtrCyclicOffset_shiftRight
      ring k x.val hxlt,
    rtrCyclicOffset_shiftRight
      ring k y.val hylt
  ] at hc
  exact hxy hc



/-! ## Ghost-step mirror for the completed list -/


private def rtrSetTwo
    {n : Nat} {A : Type}
    (f : Fin n → A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n → A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k


private def rtrGhostStep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let pre :=
    rtrPrelude hpsi
      (G.phys e) (G.phys rsite)
  let gb :=
    rtrGhostMoveToken hpsi .black step e
      pre.1 pre.2 (G.black e) (G.black rsite)
  let qb := moveToken hpsi .black pre.1 pre.2
  let gw :=
    rtrGhostMoveToken hpsi .white step e
      qb.1 qb.2 (G.white e) (G.white rsite)
  { phys :=
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e
    black :=
      rtrSetTwo G.black e rsite gb.left gb.right
    white :=
      rtrSetTwo G.white e rsite gw.left gw.right
    completed := G.completed ++ gb.done ++ gw.done }


private theorem rtrGhostStep_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    rtrGhostStep hpsi ring step G e =
      ghostStep hpsi ring step G e := by
  unfold rtrGhostStep ghostStep
  unfoldGhostStepCore
  rfl


private theorem rtrGhostStep_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (rtrGhostStep hpsi ring step G e).completed =
      G.completed ++
        (rtrSelectedPair
          hpsi ring step G e .black).done ++
        (rtrSelectedPair
          hpsi ring step G e .white).done := by
  rfl


/-- A selected-colour done entry is appended to the literal completed list. -/
private theorem rtrSelectedDone_mem_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (m : LineageMeta n)
    (hm :
      m ∈
        (ghostStepSelectedPair
          hpsi ring step G e kind).done) :
    m ∈
      (ghostStep hpsi ring step G e).completed := by
  rw [← rtrSelectedPair_eq] at hm
  rw [← rtrGhostStep_eq hpsi ring step G e]
  rw [rtrGhostStep_completed hpsi ring step G e]
  simp only [List.mem_append]
  cases kind with
  | black =>
      exact .inl (.inr hm)
  | white =>
      exact .inr hm


/-! ## Ring geometry and soundness projections -/


private theorem rtrRightNeighbor_ne
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem rtrRightNeighbor_shiftRight
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


private theorem rtrGhostSoundAt
    {n psi kappa : Nat}
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧
      rtrLocalValid kind (G.phys i) z.value := by
  cases kind with
  | black =>
      exact hsound.1 i z howner
  | white =>
      exact hsound.2 i z howner


/-! ## Target-coordinate arithmetic under `C_d` -/


/-- The three possible reductions of `a % M` for `-M ≤ a < 2M`. -/
private theorem rtrEmodCases
    (a M : Int)
    (hM : 0 < M)
    (hlo : -M ≤ a)
    (hhi : a < 2 * M) :
    (a % M = a ∧ 0 ≤ a ∧ a < M) ∨
      (a % M = a - M ∧ M ≤ a) ∨
      (a % M = a + M ∧ a < 0) := by
  by_cases h0 : 0 ≤ a
  · by_cases h1 : a < M
    · exact Or.inl ⟨Int.emod_eq_of_lt h0 h1, h0, h1⟩
    · have h := Int.add_emod_right (a - M) M
      have ha : a - M + M = a := by
        omega
      rw [ha] at h
      refine Or.inr (Or.inl ⟨?_, by omega⟩)
      rw [h]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  · have h := Int.add_emod_right a M
    refine Or.inr (Or.inr ⟨?_, by omega⟩)
    rw [← h]
    exact Int.emod_eq_of_lt (by omega) (by omega)


/--
Under the `C_d` distance labelling, the Definition-3 target of a token at
window coordinate `w` is `(w + c) mod 2 psi`, for both colours.
-/
private theorem rtrTargetAt
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (w : Nat)
    (hw : w < 2 * psi)
    (hdist :
      q.dist.val =
        (w + tokenD' psi kind) % (2 * psi)) :
    tokenTargetCoordinate kind q t =
      ((((w : Nat)) : Int) +
          decodeOffset psi (tokenCode t)) %
        (((2 * psi : Nat)) : Int) := by
  cases kind with
  | black =>
      have hd : q.dist.val = w := by
        rw [hdist]
        simp only [tokenD', Nat.add_zero]
        exact Nat.mod_eq_of_lt hw
      unfold tokenTargetCoordinate
      rw [hd]
      simp only [tokenD']
      congr 1
      omega
  | white =>
      by_cases hlt : w + psi < 2 * psi
      · have hd : q.dist.val = w + psi := by
          rw [hdist]
          simp only [tokenD']
          exact Nat.mod_eq_of_lt hlt
        unfold tokenTargetCoordinate
        rw [hd]
        simp only [tokenD']
        have h :=
          Int.add_emod_right
            ((((w : Nat)) : Int) +
              decodeOffset psi (tokenCode t))
            (((2 * psi : Nat)) : Int)
        rw [← h]
        congr 1
        omega
      · have hd : q.dist.val = w - psi := by
          rw [hdist]
          simp only [tokenD']
          have hge : 2 * psi ≤ w + psi := by
            omega
          rw [Nat.mod_eq_sub_mod hge,
            Nat.mod_eq_of_lt
              (show w + psi - 2 * psi < 2 * psi by omega)]
          omega
        unfold tokenTargetCoordinate
        rw [hd]
        simp only [tokenD']
        congr 1
        omega


/-- No Definition-3 valid token sits at window coordinate `2*psi-1`. -/
private theorem rtrNotLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hq :
      q.dist.val =
        (2 * psi - 1 + tokenD' psi kind) % (2 * psi))
    (hv : rtrLocalValid kind q t) :
    False := by
  have ht :=
    rtrTargetAt hpsi kind q t (2 * psi - 1)
      (by omega) hq
  have hc :=
    decodeOffset_valid psi (by omega) (tokenCode t)
  unfold ValidOffset at hc
  unfold rtrLocalValid at hv
  dsimp only at hv
  rw [ht] at hv
  generalize decodeOffset psi (tokenCode t) = c at hv hc
  rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
  rcases
      rtrEmodCases
        ((((2 * psi - 1 : Nat)) : Int) + c)
        (((2 * psi : Nat)) : Int)
        (by omega) (by omega) (by omega) with
    ⟨h, _, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
  rw [h] at hv <;>
  rcases hv with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
  omega


/-- An ordinary right move (`c >= 2`) keeps the target, hence validity. -/
private theorem rtrPosMoveValid
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (x : Nat)
    (hx1 : x + 1 < 2 * psi)
    (hq :
      q.dist.val =
        (x + tokenD' psi kind) % (2 * psi))
    (hq' :
      q'.dist.val =
        (x + 1 + tokenD' psi kind) % (2 * psi))
    (hv : rtrLocalValid kind q t)
    (h2 : 2 ≤ decodeOffset psi (tokenCode t))
    (hdec :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) - 1) :
    rtrLocalValid kind q' t' := by
  have ht :=
    rtrTargetAt hpsi kind q t x (by omega) hq
  have ht' :=
    rtrTargetAt hpsi kind q' t' (x + 1) hx1 hq'
  unfold rtrLocalValid at hv ⊢
  dsimp only at hv ⊢
  rw [ht] at hv
  rw [ht', hdec]
  have hsame :
      ((((x + 1 : Nat)) : Int) +
          (decodeOffset psi (tokenCode t) - 1)) =
        (((x : Nat)) : Int) +
          decodeOffset psi (tokenCode t) := by
    omega
  rw [hsame]
  rcases hv with ⟨_, hlo, hhi⟩ | ⟨hneg, _, _⟩
  · left
    exact ⟨by omega, hlo, hhi⟩
  · omega


/--
A `c = 1` arrival from coordinate `x <= 2*psi-3` produces a valid negative
token `1 - psi` at coordinate `x + 1`.
-/
private theorem rtrArrivalValid
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (x : Nat)
    (hx2 : x + 2 < 2 * psi)
    (hq :
      q.dist.val =
        (x + tokenD' psi kind) % (2 * psi))
    (hq' :
      q'.dist.val =
        (x + 1 + tokenD' psi kind) % (2 * psi))
    (hv : rtrLocalValid kind q t)
    (h1 : decodeOffset psi (tokenCode t) = 1)
    (hnew :
      decodeOffset psi (tokenCode t') =
        1 - ((psi : Nat) : Int)) :
    rtrLocalValid kind q' t' := by
  have ht :=
    rtrTargetAt hpsi kind q t x (by omega) hq
  have ht' :=
    rtrTargetAt hpsi kind q' t' (x + 1)
      (by omega) hq'
  unfold rtrLocalValid at hv ⊢
  dsimp only at hv ⊢
  rw [ht, h1] at hv
  rw [ht', hnew]
  have e1 :
      ((((x : Nat)) : Int) + 1) %
          (((2 * psi : Nat)) : Int) =
        (((x : Nat)) : Int) + 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [e1] at hv
  rcases hv with ⟨_, hlo, _⟩ | ⟨hneg, _, _⟩
  · have e2 :
        ((((x + 1 : Nat)) : Int) +
              (1 - ((psi : Nat) : Int))) %
            (((2 * psi : Nat)) : Int) =
          (((x + 1 : Nat)) : Int) +
            (1 - ((psi : Nat) : Int)) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [e2]
    right
    exact ⟨by omega, by omega, by omega⟩
  · omega


/-! ## The literal ghost move on a clean pair -/


/--
Clean-pair reduction: gate open, initiator live and shadowed by `z`,
responder live value empty.  Then the birth guard and the collision guard are
both off, and the move is the finishing branch on `z`.
-/
private theorem rtrGhostMove_clean
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hl : l.last = false)
    (hr : r.last = false)
    (hlv : rtrLiveValue kind l = some z.value)
    (hgl : rtrLiveShadow kind l (some z) = some z)
    (hrv : rtrLiveValue kind r = none) :
    rtrGhostMoveToken hpsi kind step site l r (some z) gr =
      rtrFinishMove hpsi kind l r
        (some z.value) none (some z)
        (rtrLiveShadow kind r gr) := by
  unfold rtrGhostMoveToken
  simp [hl, hr, hlv, hgl, hrv]


private theorem rtrFinish_neg
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (hneg : decodeOffset psi (tokenCode t) < 0) :
    (rtrFinishMove hpsi kind l r
        (some t) none gl gr).left = gl := by
  have h1 : decodeOffset psi (tokenCode t) ≠ 1 := by
    omega
  have h2 : ¬ 2 ≤ decodeOffset psi (tokenCode t) := by
    omega
  simp [rtrFinishMove, h1, h2]


private theorem rtrFinish_one
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (h1 : decodeOffset psi (tokenCode t) = 1) :
    (rtrFinishMove hpsi kind l r
        (some t) rv gl gr).right =
        (rtrBumpTo kind r
          (rtrMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2) gl).live ∧
      (rtrFinishMove hpsi kind l r
        (some t) rv gl gr).done =
        (rtrBumpTo kind r
          (rtrMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2) gl).done := by
  constructor <;> simp [rtrFinishMove, h1]


private theorem rtrFinish_two
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (h2 : 2 ≤ decodeOffset psi (tokenCode t)) :
    ∃ nxt : TokenData psi,
      decodeOffset psi (tokenCode nxt) =
          decodeOffset psi (tokenCode t) - 1 ∧
        (rtrFinishMove hpsi kind l r
            (some t) none gl gr).right =
          (rtrBumpTo kind r nxt gl).live := by
  have h1 : ¬ decodeOffset psi (tokenCode t) = 1 := by
    omega
  unfold rtrFinishMove
  dsimp only
  rw [dif_neg h1, dif_pos h2]
  refine ⟨_, ?_, rfl⟩
  dsimp only [rtrMkToken, tokenCode]
  exact decode_encode _ _ _


private theorem rtrBump_live
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (nxt : TokenData psi)
    (z : GhostToken n psi)
    (hv : rtrLocalValid kind q nxt) :
    (rtrBumpTo kind q nxt (some z)).live =
      some
        ({ value := nxt
           lmeta := ghostStepLineageAdvance z.lmeta } :
          GhostToken n psi) := by
  show
    (if rtrLocalValid kind q nxt then
        some
          ({ value := nxt
             lmeta := ghostStepLineageAdvance z.lmeta } :
            GhostToken n psi)
      else none) = _
  rw [if_pos hv]


private theorem rtrBump_done
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (nxt : TokenData psi)
    (z : GhostToken n psi)
    (hm :
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi) :
    (rtrBumpTo kind q nxt (some z)).done =
      [ghostStepLineageAdvance z.lmeta] := by
  show
    (if (ghostStepLineageAdvance z.lmeta).moves =
          tokenTrajectoryMoves psi then
        [ghostStepLineageAdvance z.lmeta]
      else []) = _
  rw [if_pos hm]


/-! ## The clean selected pair of a rightmost initiator -/


/--
Setup for a tracked rightmost initiator at coordinate `x` under pre/post
`C_d`, coverage and soundness: `x` is not the last coordinate, and the
selected-colour inputs of the interaction form a clean pair.
-/
private theorem rtrSetup
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
    (he : e = shiftRight ring k x.val)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (hright : Lemma4RightmostAt ring k kind G x z) :
    ∃ P : State psi kappa × State psi kappa,
      rtrSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e)) = P ∧
        x.val + 1 < 2 * psi ∧
        P.1.last = false ∧
        P.2.last = false ∧
        rtrLiveValue kind P.1 = some z.value ∧
        rtrLiveShadow kind P.1 (some z) = some z ∧
        rtrLiveValue kind P.2 = none ∧
        rtrLocalValid kind P.1 z.value ∧
        P.1.dist.val =
          (x.val + tokenD' psi kind) % (2 * psi) ∧
        P.2.dist.val =
          (x.val + 1 + tokenD' psi kind) % (2 * psi) := by
  have hR := hright
  unfold Lemma4RightmostAt at hR
  dsimp only at hR
  obtain ⟨hown, _hvalid, hempty⟩ := hR
  rw [← he] at hown
  have hfit :=
    rtrCd_window_fits hpsi ring k kind G.phys hCd
  have hne : ring.rightNeighbor e ≠ e :=
    rtrRightNeighbor_ne ring (by omega) e
  have hsnd :=
    rtrGhostSoundAt G kind e z hsound hown
  have hpreDist :
      (G.phys e).dist.val =
        (x.val + tokenD' psi kind) % (2 * psi) := by
    have h := (hCd x).1
    try dsimp only at h
    rw [← he] at h
    exact h
  have hpreLast : (G.phys e).last = false := by
    have h := (hCd x).2
    try dsimp only at h
    rw [← he] at h
    exact h
  have hx1 : x.val + 1 < 2 * psi := by
    by_cases hlt : x.val + 1 < 2 * psi
    · exact hlt
    · have hxl : x.val = 2 * psi - 1 := by
        have := x.isLt
        omega
      rw [hxl] at hpreDist
      exact
        False.elim
          (rtrNotLast hpsi kind (G.phys e) z.value
            hpreDist hsnd.2)
  let y : Fin (2 * psi) := ⟨x.val + 1, hx1⟩
  have hr :
      ring.rightNeighbor e =
        shiftRight ring k y.val := by
    rw [he]
    exact rtrRightNeighbor_shiftRight ring k x.val
  have hwinL : Lemma4InWindow ring k psi e :=
    ⟨x, he⟩
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e) :=
    ⟨y, hr⟩
  have hrDist :
      (G.phys (ring.rightNeighbor e)).dist.val =
        (x.val + 1 + tokenD' psi kind) % (2 * psi) := by
    have h := (hCd y).1
    try dsimp only at h
    rw [← hr] at h
    exact h
  have hrLast :
      (G.phys (ring.rightNeighbor e)).last = false := by
    have h := (hCd y).2
    try dsimp only at h
    rw [← hr] at h
    exact h
  have hnone :
      ghostTokenAt kind G
          (ring.rightNeighbor e) = none := by
    have h :
        ghostTokenAt kind G
            (shiftRight ring k y.val) = none :=
      hempty y (Nat.lt_succ_self _)
    rw [hr]
    exact h
  have hstatic :=
    rtrSelectedInput_static_pre
      hpsi ring k kind step G e hne
      hCd hCd' hwinL hwinR
  dsimp only at hstatic
  have htok :=
    rtrSelectedInput_token hpsi kind
      (G.phys e) (G.phys (ring.rightNeighbor e))
  generalize hP :
      rtrSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e)) = P
    at hstatic htok
  obtain ⟨hd1, hl1, hd2, hl2⟩ := hstatic
  have htok1 : tokenAt kind P.1 = some z.value :=
    htok.1.trans hsnd.1
  have hv1 : rtrLocalValid kind P.1 z.value := by
    have h := hsnd.2
    unfold rtrLocalValid tokenTargetCoordinate at h ⊢
    rw [hd1]
    exact h
  have hlv : rtrLiveValue kind P.1 = some z.value := by
    simp [rtrLiveValue, htok1, hv1]
  have hgl : rtrLiveShadow kind P.1 (some z) = some z := by
    simp [rtrLiveShadow, htok1, hv1]
  have hrv : rtrLiveValue kind P.2 = none := by
    cases ht : tokenAt kind P.2 with
    | none =>
        simp [rtrLiveValue, ht]
    | some t =>
        by_cases hv : rtrLocalValid kind P.2 t
        · exfalso
          have ht0 :
              tokenAt kind
                  (G.phys (ring.rightNeighbor e)) =
                some t :=
            htok.2.symm.trans ht
          have hv0 :
              rtrLocalValid kind
                (G.phys (ring.rightNeighbor e)) t := by
            unfold rtrLocalValid tokenTargetCoordinate at hv ⊢
            rw [← hd2]
            exact hv
          have hvalid :
              ValidToken kind G.phys
                (ring.rightNeighbor e) := by
            unfold ValidToken
            rw [ht0]
            exact hv0
          obtain ⟨z0, hz0⟩ :=
            hcovered (ring.rightNeighbor e) hwinR hvalid
          rw [hnone] at hz0
          cases hz0
        · simp [rtrLiveValue, ht, hv]
  refine
    ⟨P, (by first | exact hP | rfl), hx1,
      hl1.trans hpreLast,
      hl2.trans hrLast,
      hlv, hgl, hrv, hv1, ?_, ?_⟩
  · rw [hd1]
    exact hpreDist
  · rw [hd2]
    exact hrDist


/-- The exported selected pair of a clean rightmost initiator is the finishing
branch on `z` with an empty responder live value. -/
private theorem rtrPairClean
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (P : State psi kappa × State psi kappa)
    (hP :
      rtrSelectedInput hpsi kind
          (G.phys e)
          (G.phys (ring.rightNeighbor e)) = P)
    (hown : ghostTokenAt kind G e = some z)
    (hl : P.1.last = false)
    (hr : P.2.last = false)
    (hlv : rtrLiveValue kind P.1 = some z.value)
    (hgl : rtrLiveShadow kind P.1 (some z) = some z)
    (hrv : rtrLiveValue kind P.2 = none) :
    ghostStepSelectedPair hpsi ring step G e kind =
      rtrFinishMove hpsi kind P.1 P.2
        (some z.value) none (some z)
        (rtrLiveShadow kind P.2
          (ghostTokenAt kind G
            (ring.rightNeighbor e))) := by
  rw [← rtrSelectedPair_eq]
  unfold rtrSelectedPair
  dsimp only
  rw [hP, hown]
  exact
    rtrGhostMove_clean hpsi kind step e P.1 P.2
      _ z hl hr hlv hgl hrv


/-! ## Row A: the terminal branch classifier -/


private theorem rtrOffsetCases
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) :
    decodeOffset psi (tokenCode t) = 1 ∨
      2 ≤ decodeOffset psi (tokenCode t) ∨
      decodeOffset psi (tokenCode t) < 0 := by
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  rcases hv with hneg | hpos
  · exact Or.inr (Or.inr (by omega))
  · by_cases h1 :
        decodeOffset psi (tokenCode t) = 1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (by omega))


/--
Row A proved.  On the clean pair, `c < 0` keeps `z` on the left, `c >= 2`
bumps `z` to a valid right owner, and `c = 1` bumps `z` to a valid right
owner whenever `x <= 2*psi-3`.  Each of these contradicts the no-same-ID
hypotheses, leaving only `x = 2*psi-2` with `c = 1`.
-/
theorem lemma4RightmostInitiatorTerminalFinalShapeRow_proved :
    Lemma4RightmostInitiatorTerminalFinalShapeRow := by
  unfold Lemma4RightmostInitiatorTerminalFinalShapeRow
  intro n psi kappa hpsi ring k kind step G e x z
  intro hCd hCd' hcovered hsound hright htrack
  intro hleft hrightOut
  have hown : ghostTokenAt kind G e = some z := by
    have hR := hright
    unfold Lemma4RightmostAt at hR
    dsimp only at hR
    rw [htrack]
    exact hR.1
  obtain
      ⟨P, hP, hx1, hl, hr, hlv, hgl, hrv,
        hv1, hd1, hd2⟩ :=
    rtrSetup hpsi ring k kind step G e x z htrack
      hCd hCd' hcovered hsound hright
  have hpair :=
    rtrPairClean hpsi ring kind step G e z P hP hown
      hl hr hlv hgl hrv
  rcases rtrOffsetCases hpsi z.value with h1 | h2 | hneg
  · refine ⟨?_, h1⟩
    by_cases hx2 : x.val + 2 < 2 * psi
    · exfalso
      have hR1 :=
        (rtrFinish_one hpsi kind P.1 P.2 z.value none
          (some z)
          (rtrLiveShadow kind P.2
            (ghostTokenAt kind G
              (ring.rightNeighbor e))) h1).1
      have hvalid :
          rtrLocalValid kind P.2
            (rtrMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              z.value.1.2 z.value.2) :=
        rtrArrivalValid hpsi kind P.1 P.2 z.value _
          x.val hx2 hd1 hd2 hv1 h1
          (decodeOffset_negPsiPlusOne psi hpsi)
      have hsome :
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some
              ({ value :=
                   rtrMkToken
                     (offsetNegPsiPlusOneCode psi hpsi)
                     z.value.1.2 z.value.2
                 lmeta :=
                   ghostStepLineageAdvance z.lmeta } :
                GhostToken n psi) := by
        rw [hpair, hR1,
          rtrBump_live kind P.2 _ z hvalid]
      exact hrightOut _ hsome rfl
    · omega
  · exfalso
    obtain ⟨nxt, hdec, hR⟩ :=
      rtrFinish_two hpsi kind P.1 P.2 z.value
        (some z)
        (rtrLiveShadow kind P.2
          (ghostTokenAt kind G
            (ring.rightNeighbor e))) h2
    have hvalid :=
      rtrPosMoveValid hpsi kind P.1 P.2 z.value nxt
        x.val hx1 hd1 hd2 hv1 h2 hdec
    have hsome :
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some
            ({ value := nxt
               lmeta :=
                 ghostStepLineageAdvance z.lmeta } :
              GhostToken n psi) := by
      rw [hpair, hR,
        rtrBump_live kind P.2 nxt z hvalid]
    exact hrightOut _ hsome rfl
  · exfalso
    have hL :=
      rtrFinish_neg hpsi kind P.1 P.2 z.value
        (some z)
        (rtrLiveShadow kind P.2
          (ghostTokenAt kind G
            (ring.rightNeighbor e))) hneg
    exact
      hleft z
        (by rw [hpair, hL])
        rfl


/-! ## Row B: the final `c = 1` service logs a fresh completion -/


/--
Age arithmetic: a positive `c = 1` trajectory point with
`moves < tokenTrajectoryMoves psi` has completed at most `psi - 1` turns, so
its unwrapped coordinate is at most `2*psi-2`.
-/
private theorem rtrFirstLap
    {psi moves X : Nat}
    (hpsi : 2 ≤ psi)
    (hpoint :
      Lemma4FreshTrajectoryPoint psi moves X (1 : Int))
    (hage : moves < tokenTrajectoryMoves psi) :
    X ≤ 2 * psi - 2 := by
  rcases hpoint with ⟨q, _, _, hXq, hmq⟩ | ⟨q, hneg, _⟩
  · change X = q + (psi - 1) at hXq
    change moves = q * (2 * psi - 1) + (psi - 1) at hmq
    rcases Nat.lt_or_ge q psi with hq | hq
    · omega
    · exfalso
      have hmul :
          psi * (2 * psi - 1) ≤ q * (2 * psi - 1) :=
        Nat.mul_le_mul hq (Nat.le_refl _)
      have hid :
          psi * (2 * psi - 1) + psi = 2 * psi * psi := by
        have h2 : 2 * psi - 1 + 1 = 2 * psi := by
          omega
        calc
          psi * (2 * psi - 1) + psi =
              psi * (2 * psi - 1 + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
          _ = psi * (2 * psi) := by
            rw [h2]
          _ = 2 * psi * psi :=
            Nat.mul_comm _ _
      unfold tokenTrajectoryMoves at hage
      generalize psi * (2 * psi - 1) = A at hmul hid
      generalize q * (2 * psi - 1) = B at hmul hmq
      generalize 2 * psi * psi = Q at hid hage
      omega
  · exfalso
    omega


/--
Row B proved.  The kinematics witness of the tracked fresh owner is on the
first lap by the age bound, hence equals `x = 2*psi-2` by window
injectivity; the final-positive trajectory arithmetic then gives
`moves + 1 = tokenTrajectoryMoves psi`.  On the clean pair the `c = 1`
bump logs the advanced metadata, which the literal step appends to
`completed`.
-/
theorem lemma4RightmostInitiatorTerminalFinalCompletionRow_proved :
    Lemma4RightmostInitiatorTerminalFinalCompletionRow := by
  unfold Lemma4RightmostInitiatorTerminalFinalCompletionRow
  intro n psi kappa hpsi ring k kind step G e x z
  intro hCd hCd' hcovered hsound hkin hage hright htrack
  intro hfresh hx hc1
  have hown : ghostTokenAt kind G e = some z := by
    have hR := hright
    unfold Lemma4RightmostAt at hR
    dsimp only at hR
    rw [htrack]
    exact hR.1
  obtain ⟨X, hXe, hpoint⟩ :=
    hkin kind e z hown hfresh
  rw [hc1] at hpoint
  have hmoves := hage hfresh
  have hXle : X ≤ 2 * psi - 2 :=
    rtrFirstLap hpsi hpoint hmoves
  have hfit :=
    rtrCd_window_fits hpsi ring k kind G.phys hCd
  have hXx : X = x.val := by
    refine Classical.byContradiction (fun hneq => ?_)
    exact
      rtrWindowSites_ne ring k hfit
        ⟨X, by omega⟩ x hneq
        (hXe.symm.trans htrack)
  rw [hXx, hx] at hpoint
  have hfin :=
    lemma4FreshTrajectoryPoint_finalPositive hpsi hpoint
  obtain
      ⟨P, hP, _hx1, hl, hr, hlv, hgl, hrv,
        _hv1, _hd1, _hd2⟩ :=
    rtrSetup hpsi ring k kind step G e x z htrack
      hCd hCd' hcovered hsound hright
  have hpair :=
    rtrPairClean hpsi ring kind step G e z P hP hown
      hl hr hlv hgl hrv
  have hD :=
    (rtrFinish_one hpsi kind P.1 P.2 z.value none
      (some z)
      (rtrLiveShadow kind P.2
        (ghostTokenAt kind G
          (ring.rightNeighbor e))) hc1).2
  have hadv :
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi :=
    hfin
  have hdoneEq :
      (ghostStepSelectedPair
          hpsi ring step G e kind).done =
        [ghostStepLineageAdvance z.lmeta] := by
    rw [hpair, hD, rtrBump_done kind P.2 _ z hadv]
  have hmem :
      ghostStepLineageAdvance z.lmeta ∈
        (ghostStepSelectedPair
          hpsi ring step G e kind).done := by
    rw [hdoneEq]
    exact List.mem_singleton_self _
  refine
    ⟨ghostStepLineageAdvance z.lmeta,
      rtrSelectedDone_mem_completed
        hpsi ring step G e kind _ hmem,
      ⟨?_, hadv⟩⟩
  rcases hfresh with ⟨t, hid, hsite⟩
  exact ⟨t, hid, hsite⟩


/-! ## The state-local terminal residual -/


/-- The state-local terminal residual, from the two proved local rows. -/
theorem lemma4RightmostInitiatorTerminalStateLocalResidual_proved :
    Lemma4RightmostInitiatorTerminalStateLocalResidual :=
  lemma4RightmostInitiatorTerminalStateLocalResidual_of_terminalLocalResiduals
    ⟨lemma4RightmostInitiatorTerminalFinalShapeRow_proved,
      lemma4RightmostInitiatorTerminalFinalCompletionRow_proved⟩


end PPL


#print axioms PPL.lemma4RightmostInitiatorTerminalFinalShapeRow_proved
#print axioms PPL.lemma4RightmostInitiatorTerminalFinalCompletionRow_proved
#print axioms PPL.lemma4RightmostInitiatorTerminalStateLocalResidual_proved
