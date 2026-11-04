import Leader.PPL.TokenCompletion.SweepRows
import Leader.PPL.TokenCompletion.CoverageOrigin
import Leader.PPL.TransitionFacts


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-! ## Local public-name mirrors -/


private def emptyBirthBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def emptyBirthMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def emptyBirthLocalValid
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


private instance instDecidableEmptyBirthLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (emptyBirthLocalValid kind q t) := by
  unfold emptyBirthLocalValid
  infer_instance


private def emptyBirthSetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def emptyBirthClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if emptyBirthLocalValid kind q t then
        q
      else
        emptyBirthSetToken kind q none


private def emptyBirthLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


private theorem emptyBirthSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      emptyBirthSetToken kind q t := by
  cases kind <;> rfl


private theorem emptyBirthSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    sourceClear kind q =
      emptyBirthClearInvalid kind q := by
  cases kind <;> rfl


private theorem emptyBirthSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = emptyBirthLeaderBirth q := by
  rfl


private theorem emptyBirthSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q t) = t := by
  rw [emptyBirthSourceSet_eq]
  cases kind <;> rfl


private theorem emptyBirthSourceSet_static
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (sourceSet kind q t).dist = q.dist ∧
      (sourceSet kind q t).last = q.last ∧
      (sourceSet kind q t).id = q.id := by
  rw [emptyBirthSourceSet_eq]
  cases kind <;> exact ⟨rfl, rfl, rfl⟩


private def emptyBirthLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if emptyBirthLocalValid kind q t then
        some t
      else
        none


private theorem emptyBirthSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      emptyBirthLiveValue kind q := by
  rw [emptyBirthSourceClear_eq]
  unfold emptyBirthClearInvalid emptyBirthLiveValue
  cases ht : tokenAt kind q with
  | none =>
      simp only [ht]
  | some t =>
      by_cases hv : emptyBirthLocalValid kind q t
      · simp only [ht, if_pos hv]
      · simp only [ht, if_neg hv]
        unfold emptyBirthSetToken
        cases kind <;> rfl


private theorem emptyBirthSourceClear_static
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    let q0 := sourceClear kind q
    q0.dist = q.dist ∧
      q0.last = q.last ∧
      q0.id = q.id := by
  dsimp only
  rw [emptyBirthSourceClear_eq]
  unfold emptyBirthClearInvalid
  cases ht : tokenAt kind q with
  | none =>
      refine ⟨?_, ?_, ?_⟩ <;>
        first | rfl | trivial
  | some t =>
      by_cases hv : emptyBirthLocalValid kind q t
      · simp only [if_pos hv]
        refine ⟨?_, ?_, ?_⟩ <;>
          first | rfl | trivial
      · simp only [if_neg hv]
        unfold emptyBirthSetToken
        cases kind <;>
          (refine ⟨?_, ?_, ?_⟩ <;>
            first | rfl | trivial)


private def emptyBirthNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    emptyBirthMkToken
      (offsetPsiCode psi hpsi)
      (emptyBirthBitToFin (!sourceBit))
      (emptyBirthBitToFin sourceBit)
  else
    emptyBirthMkToken
      (offsetPsiCode psi hpsi)
      (emptyBirthBitToFin sourceBit)
      (0 : Fin 2)


private def emptyBirthPhysicalMoveToken
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := sourceClear kind l
  let r := sourceClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧
          tokenAt kind l = none then
        sourceSet kind l
          (some
            (emptyBirthMkToken
              (offsetPsiCode psi hpsi)
              (emptyBirthBitToFin (!l.id))
              (emptyBirthBitToFin l.id)))
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
            if hm1 : c = -1 then
              let next :=
                emptyBirthNegTurnNext hpsi l.id t
              let l :=
                sourceSet kind l (some next)
              let r := sourceSet kind r none
              (l, r)
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                emptyBirthMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let l :=
                sourceSet kind l (some next)
              let r := sourceSet kind r none
              (l, r)
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
              sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          let r :=
            sourceSet kind r
              (some
                (emptyBirthMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2))
          let l := sourceSet kind l none
          (l, r)
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            emptyBirthMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let r := sourceSet kind r (some next)
          let l := sourceSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)


private theorem emptyBirthPhysicalMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    emptyBirthPhysicalMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl


private def emptyBirthPrelude
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


private def emptyBirthSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := emptyBirthPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2


private def emptyBirthSelectedOutput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := emptyBirthSelectedInput hpsi kind l r
  moveToken hpsi kind p.1 p.2


/-! ## Selected input field frames -/


private theorem emptyBirthDetermineMode_token
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


private theorem emptyBirthThroughLine6_token
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := createLeaderThroughLine6 hpsi l r
    tokenAt kind q.left = tokenAt kind l ∧
      tokenAt kind q.right = tokenAt kind r := by
  have hd := emptyBirthDetermineMode_token kind l r
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
      rw [emptyBirthSourceBirth_eq]
      cases kind <;>
        simpa [emptyBirthLeaderBirth, tokenAt]
          using hd.2
  · simp only
      [createLeaderThroughLine6, if_neg hguard]
    exact hd


private theorem emptyBirthPrelude_token
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (emptyBirthPrelude hpsi l r).1 =
        tokenAt kind l ∧
      tokenAt kind (emptyBirthPrelude hpsi l r).2 =
        tokenAt kind r := by
  have hs :=
    emptyBirthThroughLine6_token
      hpsi kind l r
  dsimp only at hs
  constructor
  · calc
      tokenAt kind
            (emptyBirthPrelude hpsi l r).1 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).left := by
        unfold emptyBirthPrelude
        cases kind <;>
          (try simp only [tokenAt]) <;>
          (repeat' split) <;>
          (try rfl)
      _ = tokenAt kind l := hs.1
  · calc
      tokenAt kind
            (emptyBirthPrelude hpsi l r).2 =
          tokenAt kind
            (createLeaderThroughLine6 hpsi l r).right := by
        unfold emptyBirthPrelude
        cases kind <;>
          (try simp only [tokenAt]) <;>
          (repeat' split) <;>
          (try rfl)
      _ = tokenAt kind r := hs.2


private theorem emptyBirthBlackPreservesWhite
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


private theorem emptyBirthSelectedInput_token
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (emptyBirthSelectedInput hpsi kind l r).1 =
        tokenAt kind l ∧
      tokenAt kind
        (emptyBirthSelectedInput hpsi kind l r).2 =
        tokenAt kind r := by
  cases kind with
  | black =>
      exact
        emptyBirthPrelude_token
          hpsi .black l r
  | white =>
      let p := emptyBirthPrelude hpsi l r
      have hp :=
        emptyBirthPrelude_token
          hpsi .white l r
      have hb :=
        emptyBirthBlackPreservesWhite
          hpsi p.1 p.2
      dsimp only [emptyBirthSelectedInput]
      exact
        ⟨hb.1.trans hp.1,
          hb.2.trans hp.2⟩


private structure EmptyBirthStaticFrame
    {psi kappa : Nat}
    (before after :
      State psi kappa × State psi kappa) : Prop where
  leftDist : after.1.dist = before.1.dist
  leftLast : after.1.last = before.1.last
  rightDist : after.2.dist = before.2.dist
  rightLast : after.2.last = before.2.last


private theorem emptyBirthMove_static
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    EmptyBirthStaticFrame
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


private structure EmptyBirthPairFrame
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


private theorem emptyBirthEliminate_frame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    EmptyBirthPairFrame
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


private theorem emptyBirthWhite_preserves_black_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    EmptyBirthPairFrame
      .black (l, r)
      (moveToken hpsi .white l r) := by
  have hs :=
    emptyBirthMove_static
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


private theorem emptyBirthPplSelected_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let s := emptyBirthSelectedOutput hpsi kind l r
    let q := ppl hpsi l r
    EmptyBirthPairFrame kind s q := by
  cases kind with
  | black =>
      let p := emptyBirthPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have hw :=
        emptyBirthWhite_preserves_black_frame
          hpsi b.1 b.2
      have he :=
        emptyBirthEliminate_frame
          TokenKind.black w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          emptyBirthSelectedOutput
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
      let p := emptyBirthPrelude hpsi l r
      let b := moveToken hpsi .black p.1 p.2
      let w := moveToken hpsi .white b.1 b.2
      have he :=
        emptyBirthEliminate_frame
          TokenKind.white w.1 w.2
      have hfull :
          ppl hpsi l r =
            eliminateLeaders w.1 w.2 := by
        rfl
      have hselected :
          emptyBirthSelectedOutput
              hpsi TokenKind.white l r =
            w := by
        rfl
      rw [hfull, hselected]
      exact he


private theorem emptyBirthStep_endpoints
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


private theorem emptyBirthCdGeometryEq
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


private theorem emptyBirthSelectedInput_static_pre
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
      emptyBirthSelectedInput hpsi kind
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    p.1.dist = (G.phys e).dist ∧
      p.1.last = (G.phys e).last ∧
      p.2.dist =
        (G.phys (ring.rightNeighbor e)).dist ∧
      p.2.last =
        (G.phys (ring.rightNeighbor e)).last := by
  let p :=
    emptyBirthSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  let s := moveToken hpsi kind p.1 p.2
  let q := ppl hpsi
    (G.phys e)
    (G.phys (ring.rightNeighbor e))
  have hm :=
    emptyBirthMove_static
      hpsi kind p.1 p.2
  have hf :=
    emptyBirthPplSelected_frame
      hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  have hs :=
    emptyBirthStep_endpoints
      hpsi ring step G e hne
  have hgL :=
    emptyBirthCdGeometryEq
      ring k kind G.phys
      (ghostStep hpsi ring step G e).phys
      hCd hCd' e hwinL
  have hgR :=
    emptyBirthCdGeometryEq
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


/-! ## Empty-window consequences -/


private theorem emptyBirthNoOwnerAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (hwin : Lemma4InWindow ring k psi i)
    (hempty :
      ¬ ∃ j : Fin n, ∃ z : GhostToken n psi,
        Lemma4InWindow ring k psi j ∧
          ghostTokenAt kind G j = some z) :
    ghostTokenAt kind G i = none := by
  cases h : ghostTokenAt kind G i with
  | none =>
      rfl
  | some z =>
      exact False.elim
        (hempty ⟨i, z, hwin, h⟩)


private theorem emptyBirthLiveValue_none
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (q : State psi kappa)
    (hwin : Lemma4InWindow ring k psi i)
    (htok :
      tokenAt kind q =
        tokenAt kind (G.phys i))
    (hdist : q.dist = (G.phys i).dist)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hempty :
      ¬ ∃ j : Fin n, ∃ z : GhostToken n psi,
        Lemma4InWindow ring k psi j ∧
          ghostTokenAt kind G j = some z) :
    emptyBirthLiveValue kind q = none := by
  cases ht : tokenAt kind q with
  | none =>
      simp [emptyBirthLiveValue, ht]
  | some t =>
      by_cases hv : emptyBirthLocalValid kind q t
      · have ht0 :
            tokenAt kind (G.phys i) = some t := by
          rw [← htok]
          exact ht
        have hv0 :
            emptyBirthLocalValid kind (G.phys i) t := by
          unfold emptyBirthLocalValid at hv ⊢
          unfold tokenTargetCoordinate at hv ⊢
          rw [← hdist]
          exact hv
        have hvalid :
            ValidToken kind G.phys i := by
          unfold ValidToken
          rw [ht0]
          exact hv0
        obtain ⟨z, hz⟩ :=
          hcovered i hwin hvalid
        exact False.elim
          (hempty ⟨i, z, hwin, hz⟩)
      · simp [emptyBirthLiveValue, ht, hv]


/-! ## Exact birth value and one right move -/


private def emptyBirthBirthValue
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (idBit : Bool) : TokenData psi :=
  emptyBirthMkToken
    (offsetPsiCode psi hpsi)
    (emptyBirthBitToFin (!idBit))
    (emptyBirthBitToFin idBit)


private def emptyBirthNextValue
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (idBit : Bool) : TokenData psi :=
  emptyBirthMkToken
    (encodeOffset psi
      (((psi : Nat) : Int) - 1)
      (by
        right
        constructor <;> omega))
    (emptyBirthBitToFin (!idBit))
    (emptyBirthBitToFin idBit)


private theorem emptyBirthBirth_decode
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (idBit : Bool) :
    decodeOffset psi
        (tokenCode
          (emptyBirthBirthValue hpsi idBit)) =
      ((psi : Nat) : Int) := by
  change
    decodeOffset psi (offsetPsiCode psi hpsi) =
      ((psi : Nat) : Int)
  exact decodeOffset_psi psi hpsi


private theorem emptyBirthNext_decode
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (idBit : Bool) :
    decodeOffset psi
        (tokenCode
          (emptyBirthNextValue hpsi idBit)) =
      ((psi : Nat) : Int) - 1 := by
  unfold emptyBirthNextValue
  change
    decodeOffset psi
        (encodeOffset psi
          (((psi : Nat) : Int) - 1) _) =
      ((psi : Nat) : Int) - 1
  exact
    decode_encode psi
      (((psi : Nat) : Int) - 1)
      (by
        right
        constructor <;> omega)


private theorem emptyBirthNext_valid
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (r : State psi kappa)
    (idBit : Bool)
    (hrdist :
      r.dist.val =
        (1 + tokenD' psi kind) % (2 * psi)) :
    emptyBirthLocalValid kind r
      (emptyBirthNextValue hpsi idBit) := by
  have hcode :=
    emptyBirthNext_decode hpsi idBit
  have htarget :
      tokenTargetCoordinate kind r
          (emptyBirthNextValue hpsi idBit) =
        ((psi : Nat) : Int) := by
    unfold tokenTargetCoordinate
    rw [hcode, hrdist]
    cases kind with
    | black =>
        simp only [tokenD', Nat.add_zero]
        rw [Nat.mod_eq_of_lt
          (by omega : 1 < 2 * psi)]
        have hsum :
            ((1 : Nat) : Int) +
                  (((psi : Nat) : Int) - 1) +
                  ((0 : Nat) : Int) =
                ((psi : Nat) : Int) := by
          omega
        rw [hsum]
        exact
          Int.emod_eq_of_lt
            (by omega) (by omega)
    | white =>
        simp only [tokenD']
        rw [Nat.mod_eq_of_lt
          (by omega : 1 + psi < 2 * psi)]
        have hsum :
            (((1 + psi : Nat) : Int) +
                  (((psi : Nat) : Int) - 1) +
                  ((psi : Nat) : Int)) =
                ((psi : Nat) : Int) +
                  (((2 * psi : Nat)) : Int) := by
          omega
        rw [hsum, Int.add_emod_right]
        exact
          Int.emod_eq_of_lt
            (by omega) (by omega)
  unfold emptyBirthLocalValid
  rw [hcode, htarget]
  left
  exact ⟨by omega, by omega, by omega⟩


private def emptyBirthBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value := emptyBirthBirthValue hpsi idBit
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def emptyBirthMovedGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value := emptyBirthNextValue hpsi idBit
    lmeta :=
      ghostStepLineageAdvance
        (emptyBirthBirthGhost
          hpsi kind step site idBit).lmeta }


private theorem emptyBirthMovedGhost_fresh
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    FreshAt kind site
      (emptyBirthMovedGhost
        hpsi kind step site idBit).lmeta := by
  refine ⟨step, ?_, ?_⟩ <;>
    rfl


/-! ## Ghost selected-row mirror -/


private def emptyBirthLiveShadow
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
              emptyBirthLocalValid kind q t then
            some z
          else
            none


private def emptyBirthBumpTo
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
        if emptyBirthLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def emptyBirthFinishMove
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
          emptyBirthMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          emptyBirthBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          emptyBirthMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          emptyBirthBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                emptyBirthNegTurnNext hpsi l.id t
              let b :=
                emptyBirthBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                emptyBirthMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                emptyBirthBumpTo kind l next gr0
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
              emptyBirthNegTurnNext hpsi l.id t
            let b :=
              emptyBirthBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              emptyBirthMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              emptyBirthBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩


private def emptyBirthGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := emptyBirthLiveValue kind l
  let rv0 := emptyBirthLiveValue kind r
  let gl0 := emptyBirthLiveShadow kind l gl
  let gr0 := emptyBirthLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (emptyBirthBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (emptyBirthBirthGhost
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
    emptyBirthFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩


private def emptyBirthSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    emptyBirthSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  emptyBirthGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))


private theorem emptyBirthSelectedPair_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    emptyBirthSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl


private theorem emptyBirthGhostMove_birth
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (hlast : l.last = false ∧ r.last = false)
    (hdist : l.dist.val = tokenD' psi kind)
    (hrdist :
      r.dist.val =
        (1 + tokenD' psi kind) % (2 * psi))
    (hlive : emptyBirthLiveValue kind l = none)
    (hrive : emptyBirthLiveValue kind r = none) :
    (emptyBirthGhostMoveToken
        hpsi kind step site l r none none).left =
        none ∧
      (emptyBirthGhostMoveToken
        hpsi kind step site l r none none).right =
        some
          (emptyBirthMovedGhost
            hpsi kind step site l.id) := by
  have hcode :=
    emptyBirthBirth_decode hpsi l.id
  have hnotOne :
      ((psi : Nat) : Int) ≠ 1 := by
    omega
  have hgeTwo :
      2 ≤ ((psi : Nat) : Int) := by
    omega
  have hvalid :=
    emptyBirthNext_valid
      hpsi kind r l.id hrdist
  constructor
  · simp [
      emptyBirthGhostMoveToken,
      emptyBirthLiveShadow,
      emptyBirthFinishMove,
      emptyBirthBumpTo,
      emptyBirthBirthGhost,
      emptyBirthMovedGhost,
      emptyBirthNextValue,
      emptyBirthMkToken,
      emptyBirthBitToFin,
      hlast, hdist, hlive, hrive,
      hcode, hnotOne, hgeTwo, hvalid,
      ghostStepLineageAdvance]
  · have hnextLocal :
        emptyBirthLocalValid kind r
          (emptyBirthMkToken
            (encodeOffset psi
              (((psi : Nat) : Int) - 1)
              (by
                right
                constructor <;> omega))
            (emptyBirthBirthValue hpsi l.id).1.2
            (emptyBirthBirthValue hpsi l.id).2) := by
      cases hid : l.id <;>
        simpa
          [emptyBirthBirthValue,
            emptyBirthNextValue,
            emptyBirthMkToken,
            emptyBirthBitToFin,
            hid]
          using hvalid
    have hbirthBit :
        (emptyBirthBirthValue hpsi l.id).1.2 =
          if l.id = false then (1 : Fin 2) else 0 := by
      cases hid : l.id <;>
        simp
          [emptyBirthBirthValue,
            emptyBirthMkToken,
            emptyBirthBitToFin,
            hid]
    have hbirthCarry :
        (emptyBirthBirthValue hpsi l.id).2 =
          if l.id = true then (1 : Fin 2) else 0 := by
      cases hid : l.id <;>
        simp
          [emptyBirthBirthValue,
            emptyBirthMkToken,
            emptyBirthBitToFin,
            hid]
    simp [
      emptyBirthGhostMoveToken,
      emptyBirthLiveShadow,
      emptyBirthFinishMove,
      emptyBirthBumpTo,
      emptyBirthBirthGhost,
      emptyBirthMovedGhost,
      emptyBirthNextValue,
      emptyBirthMkToken,
      emptyBirthBitToFin,
      hlast, hdist, hlive, hrive,
      hcode, hnotOne, hgeTwo,
      ghostStepLineageAdvance]
    exact ⟨hnextLocal, hbirthBit, hbirthCarry⟩


private theorem emptyBirthPhysicalMove_birth
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hlast : l.last = false ∧ r.last = false)
    (hdist : l.dist.val = tokenD' psi kind)
    (hrdist :
      r.dist.val =
        (1 + tokenD' psi kind) % (2 * psi))
    (hlive : emptyBirthLiveValue kind l = none)
    (hrive : emptyBirthLiveValue kind r = none) :
    tokenAt kind
        (moveToken hpsi kind l r).1 = none ∧
      tokenAt kind
        (moveToken hpsi kind l r).2 =
          some (emptyBirthNextValue hpsi l.id) := by
  let l0 := sourceClear kind l
  let r0 := sourceClear kind r
  have hl0tok :
      tokenAt kind l0 = none := by
    dsimp only [l0]
    rw [emptyBirthSourceClear_token]
    exact hlive
  have hr0tok :
      tokenAt kind r0 = none := by
    dsimp only [r0]
    rw [emptyBirthSourceClear_token]
    exact hrive
  have hl0s :=
    emptyBirthSourceClear_static kind l
  have hr0s :=
    emptyBirthSourceClear_static kind r
  have hl0last : l0.last = false :=
    hl0s.2.1.trans hlast.1
  have hr0last : r0.last = false :=
    hr0s.2.1.trans hlast.2
  have hl0dist :
      l0.dist.val = tokenD' psi kind := by
    exact (congrArg Fin.val hl0s.1).trans hdist
  have hl0id : l0.id = l.id :=
    hl0s.2.2
  have hbirth :
      l0.dist.val = tokenD' psi kind ∧
        tokenAt kind l0 = none :=
    ⟨hl0dist, hl0tok⟩
  let birthValue :=
    emptyBirthBirthValue hpsi l0.id
  let l1 :=
    sourceSet kind l0 (some birthValue)
  have hl1tok :
      tokenAt kind l1 = some birthValue := by
    dsimp only [l1]
    exact
      emptyBirthSourceSet_token
        kind l0 (some birthValue)
  have hcollision :
      ¬ (tokenAt kind l1 ≠ none ∧
        tokenAt kind r0 ≠ none) := by
    intro h
    exact h.2 hr0tok
  have hcode :
      decodeOffset psi
          (tokenCode birthValue) =
        ((psi : Nat) : Int) := by
    dsimp only [birthValue]
    exact emptyBirthBirth_decode hpsi l0.id
  have hnotOne :
      ((psi : Nat) : Int) ≠ 1 := by
    omega
  have hgeTwo :
      2 ≤ ((psi : Nat) : Int) := by
    omega
  have hnextEq :
      emptyBirthNextValue hpsi l0.id =
        emptyBirthNextValue hpsi l.id := by
    rw [hl0id]
  have hclearId :
      (sourceClear kind l).id = l.id := by
    simpa only [l0] using hl0id
  have hbirthBit :
      (emptyBirthBirthValue hpsi l.id).1.2 =
        if l.id = false then (1 : Fin 2) else 0 := by
    cases hid : l.id <;>
      simp
        [emptyBirthBirthValue,
          emptyBirthMkToken,
          emptyBirthBitToFin,
          hid]
  have hbirthCarry :
      (emptyBirthBirthValue hpsi l.id).2 =
        if l.id = true then (1 : Fin 2) else 0 := by
    cases hid : l.id <;>
      simp
        [emptyBirthBirthValue,
          emptyBirthMkToken,
          emptyBirthBitToFin,
          hid]
  have hbornEq :
      emptyBirthMkToken
          (offsetPsiCode psi hpsi)
          (emptyBirthBitToFin
            (!(sourceClear kind l).id))
          (emptyBirthBitToFin
            (sourceClear kind l).id) =
        emptyBirthBirthValue hpsi l.id := by
    rw [hclearId]
    rfl
  have hbornCode :
      decodeOffset psi
          (tokenCode
            (emptyBirthBirthValue hpsi l.id)) =
        ((psi : Nat) : Int) :=
    emptyBirthBirth_decode hpsi l.id
  have hnextPayload :
      emptyBirthMkToken
          (encodeOffset psi
            (((psi : Nat) : Int) - 1)
            (by
              right
              constructor <;> omega))
          (emptyBirthBirthValue hpsi l.id).1.2
          (emptyBirthBirthValue hpsi l.id).2 =
        emptyBirthNextValue hpsi l.id := by
    rw [hbirthBit, hbirthCarry]
    cases hid : l.id <;>
      simp
        [emptyBirthNextValue,
          emptyBirthMkToken,
          emptyBirthBitToFin,
          hid]
  have hl0tok' :
      tokenAt kind (sourceClear kind l) = none := by
    simpa only [l0] using hl0tok
  have hr0tok' :
      tokenAt kind (sourceClear kind r) = none := by
    simpa only [r0] using hr0tok
  have hl0last' :
      (sourceClear kind l).last = false := by
    simpa only [l0] using hl0last
  have hr0last' :
      (sourceClear kind r).last = false := by
    simpa only [r0] using hr0last
  have hl0dist' :
      (sourceClear kind l).dist.val =
        tokenD' psi kind := by
    simpa only [l0] using hl0dist
  have hbornEq' := hbornEq
  rw [hclearId] at hbornEq'
  rw [← emptyBirthPhysicalMoveToken_eq
    hpsi kind l r]
  constructor
  · simp only [emptyBirthPhysicalMoveToken]
    simp
      [hl0tok', hr0tok',
        hl0last', hr0last', hl0dist',
        hclearId, hbornEq, hbornEq', hbornCode,
        hnotOne, hgeTwo,
        emptyBirthSourceSet_token]
  · simp only [emptyBirthPhysicalMoveToken]
    simp
      [hl0tok', hr0tok',
        hl0last', hr0last', hl0dist',
        hclearId, hbornEq, hbornEq', hbornCode,
        hnotOne, hgeTwo,
        emptyBirthSourceSet_token,
        hnextPayload]


/-! ## Cyclic window geometry -/


private theorem emptyBirthShiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) :
    shiftRight ring k 0 = k := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt k.isLt]


private theorem emptyBirthRightNeighbor_eq_shiftOne
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) :
    ring.rightNeighbor k =
      shiftRight ring k 1 := by
  rfl


private theorem emptyBirthCd_window_fits
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


private theorem emptyBirthCyclicOffset_shiftRight
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


private theorem emptyBirthWindowSites_ne
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
    emptyBirthCyclicOffset_shiftRight
      ring k x.val hxlt,
    emptyBirthCyclicOffset_shiftRight
      ring k y.val hylt
  ] at hc
  exact hxy hc


/-! ## The exact empty-birth selected row -/


private theorem emptyBirthSelectedRow
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (hCd : Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G k).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hempty :
      ¬ ∃ i : Fin n, ∃ z : GhostToken n psi,
        Lemma4InWindow ring k psi i ∧
          ghostTokenAt kind G i = some z) :
    let pair :=
      ghostStepSelectedPair
        hpsi ring step G k kind
    ∃ z : GhostToken n psi,
      pair.left = none ∧
        pair.right = some z ∧
        FreshAt kind k z.lmeta ∧
        ValidToken kind
          (ghostStep hpsi ring step G k).phys
          (ring.rightNeighbor k) := by
  have hfit :=
    emptyBirthCd_window_fits
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor k ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp only [DirectedRing.rightNeighbor] at hv
    by_cases hlt : k.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq : k.val + 1 = n := by
        omega
      rw [heq, Nat.mod_self] at hv
      omega


  let x0 : Fin (2 * psi) :=
    ⟨0, by omega⟩
  let x1 : Fin (2 * psi) :=
    ⟨1, by omega⟩
  have hwinK :
      Lemma4InWindow ring k psi k := by
    refine ⟨x0, ?_⟩
    dsimp only [x0]
    exact (emptyBirthShiftRight_zero ring k).symm
  have hwinR :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor k) := by
    refine ⟨x1, ?_⟩
    dsimp only [x1]
    exact emptyBirthRightNeighbor_eq_shiftOne ring k


  let p :=
    emptyBirthSelectedInput hpsi kind
      (G.phys k)
      (G.phys (ring.rightNeighbor k))


  have htok :=
    emptyBirthSelectedInput_token
      hpsi kind
      (G.phys k)
      (G.phys (ring.rightNeighbor k))
  have hstatic :=
    emptyBirthSelectedInput_static_pre
      hpsi ring k kind step G k hne
      hCd hCd' hwinK hwinR
  dsimp only [p] at htok hstatic


  have hlive :
      emptyBirthLiveValue kind p.1 = none :=
    emptyBirthLiveValue_none
      ring k kind G k p.1
      hwinK htok.1 hstatic.1
      hcovered hempty
  have hrive :
      emptyBirthLiveValue kind p.2 = none :=
    emptyBirthLiveValue_none
      ring k kind G (ring.rightNeighbor k) p.2
      hwinR htok.2 hstatic.2.2.1
      hcovered hempty


  have hleftLast :
      p.1.last = false := by
    have hrow := (hCd x0).2
    dsimp only [x0] at hrow
    rw [emptyBirthShiftRight_zero] at hrow
    exact hstatic.2.1.trans hrow
  have hrightLast :
      p.2.last = false := by
    have hrow := (hCd x1).2
    dsimp only [x1] at hrow
    rw [← emptyBirthRightNeighbor_eq_shiftOne] at hrow
    exact hstatic.2.2.2.trans hrow
  have hleftDist :
      p.1.dist.val =
        tokenD' psi kind := by
    have hrow := (hCd x0).1
    dsimp only [x0] at hrow
    rw [emptyBirthShiftRight_zero] at hrow
    have h0 :
        (0 + tokenD' psi kind) % (2 * psi) =
          tokenD' psi kind := by
      cases kind with
      | black =>
          simp [tokenD']
      | white =>
          simp only [tokenD', Nat.zero_add]
          rw [Nat.mod_eq_of_lt
            (by omega : psi < 2 * psi)]
    calc
      p.1.dist.val =
          (G.phys k).dist.val :=
        congrArg Fin.val hstatic.1
      _ =
          (0 + tokenD' psi kind) % (2 * psi) :=
        hrow
      _ = tokenD' psi kind := h0
  have hrightDist :
      p.2.dist.val =
        (1 + tokenD' psi kind) % (2 * psi) := by
    have hrow := (hCd x1).1
    dsimp only [x1] at hrow
    rw [← emptyBirthRightNeighbor_eq_shiftOne] at hrow
    calc
      p.2.dist.val =
          (G.phys (ring.rightNeighbor k)).dist.val :=
        congrArg Fin.val hstatic.2.2.1
      _ =
          (1 + tokenD' psi kind) % (2 * psi) :=
        hrow


  have hpreL :
      ghostTokenAt kind G k = none :=
    emptyBirthNoOwnerAt
      ring k kind G k hwinK hempty
  have hpreR :
      ghostTokenAt kind G
          (ring.rightNeighbor k) = none :=
    emptyBirthNoOwnerAt
      ring k kind G
      (ring.rightNeighbor k) hwinR hempty


  let z :=
    emptyBirthMovedGhost
      hpsi kind step k p.1.id


  have hghost :=
    emptyBirthGhostMove_birth
      hpsi kind step k p.1 p.2
      ⟨hleftLast, hrightLast⟩
      hleftDist hrightDist
      hlive hrive
  have hpairLocal :
      (emptyBirthSelectedPair
          hpsi ring step G k kind).left = none ∧
        (emptyBirthSelectedPair
          hpsi ring step G k kind).right = some z := by
    unfold emptyBirthSelectedPair
    dsimp only [p, z]
    rw [hpreL, hpreR]
    exact hghost
  have hpair :
      (ghostStepSelectedPair
          hpsi ring step G k kind).left = none ∧
        (ghostStepSelectedPair
          hpsi ring step G k kind).right = some z := by
    rw [← emptyBirthSelectedPair_eq
      hpsi ring step G k kind]
    exact hpairLocal


  have hphysMove :=
    emptyBirthPhysicalMove_birth
      hpsi kind p.1 p.2
      ⟨hleftLast, hrightLast⟩
      hleftDist hrightDist
      hlive hrive


  have hsuffix :=
    emptyBirthPplSelected_frame
      hpsi kind
      (G.phys k)
      (G.phys (ring.rightNeighbor k))
  have hstep :=
    emptyBirthStep_endpoints
      hpsi ring step G k hne
  dsimp only at hsuffix


  have hpostTok :
      tokenAt kind
          ((ghostStep hpsi ring step G k).phys
            (ring.rightNeighbor k)) =
        some z.value := by
    calc
      tokenAt kind
          ((ghostStep hpsi ring step G k).phys
            (ring.rightNeighbor k)) =
          tokenAt kind
            (ppl hpsi
              (G.phys k)
              (G.phys
                (ring.rightNeighbor k))).2 := by
        rw [hstep.2]
      _ =
          tokenAt kind
            (emptyBirthSelectedOutput hpsi kind
              (G.phys k)
              (G.phys
                (ring.rightNeighbor k))).2 :=
        hsuffix.rightToken
      _ =
          some (emptyBirthNextValue hpsi p.1.id) := by
        dsimp only [emptyBirthSelectedOutput, p]
        exact hphysMove.2
      _ = some z.value := by
        rfl


  have hpostDist :
      ((ghostStep hpsi ring step G k).phys
        (ring.rightNeighbor k)).dist =
        p.2.dist := by
    calc
      ((ghostStep hpsi ring step G k).phys
          (ring.rightNeighbor k)).dist =
          (ppl hpsi
            (G.phys k)
            (G.phys (ring.rightNeighbor k))).2.dist := by
        rw [hstep.2]
      _ =
          (emptyBirthSelectedOutput hpsi kind
            (G.phys k)
            (G.phys (ring.rightNeighbor k))).2.dist :=
        hsuffix.rightDist
      _ = p.2.dist :=
        (emptyBirthMove_static
          hpsi kind p.1 p.2).rightDist


  have hlocal :
      emptyBirthLocalValid kind
        ((ghostStep hpsi ring step G k).phys
          (ring.rightNeighbor k))
        z.value := by
    have hv :=
      emptyBirthNext_valid
        hpsi kind p.2 p.1.id hrightDist
    unfold emptyBirthLocalValid at hv ⊢
    unfold tokenTargetCoordinate at hv ⊢
    rw [hpostDist]
    exact hv


  have hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G k).phys
        (ring.rightNeighbor k) := by
    unfold ValidToken
    rw [hpostTok]
    exact hlocal


  refine ⟨z, hpair.1, hpair.2, ?_, hvalid⟩
  dsimp only [z]
  exact
    emptyBirthMovedGhost_fresh
      hpsi kind step k p.1.id


/-! ## Headline row -/


theorem lemma4SweepEmptyBirthLiteralCases_proved :
    Lemma4SweepEmptyBirthLiteralCases := by
  intro n psi kappa hpsi ring k kind step G e
  intro hCd hCd' hcovered _hsound _huniq _hkin
  intro hempty he
  subst e


  have hfit :=
    emptyBirthCd_window_fits
      hpsi ring k kind G.phys hCd
  have hne :
      ring.rightNeighbor k ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp only [DirectedRing.rightNeighbor] at hv
    by_cases hlt : k.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq : k.val + 1 = n := by
        omega
      rw [heq, Nat.mod_self] at hv
      omega


  have hrow :=
    emptyBirthSelectedRow
      hpsi ring k kind step G
      hCd hCd' hcovered hempty
  dsimp only at hrow
  rcases hrow with
    ⟨z, hleft, hright, hfresh, hvalid⟩


  have hsourceNone :
      ghostTokenAt kind
          (ghostStep hpsi ring step G k) k =
        none := by
    rw [
      ghostTokenAt_ghostStep_initiator
        hpsi ring step G k kind]
    exact hleft


  have hrespOwner :
      ghostTokenAt kind
          (ghostStep hpsi ring step G k)
          (ring.rightNeighbor k) =
        some z := by
    rw [
      ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G k kind hne]
    exact hright


  let x1 : Fin (2 * psi) :=
    ⟨1, by omega⟩
  right
  refine ⟨x1, z, ?_, hfresh⟩
  unfold Lemma4RightmostAt
  dsimp only [x1]
  rw [← emptyBirthRightNeighbor_eq_shiftOne]
  refine ⟨hrespOwner, hvalid, ?_⟩


  intro y hy
  let j := shiftRight ring k y.val
  change
    ghostTokenAt kind
        (ghostStep hpsi ring step G k) j =
      none
  by_cases hjk : j = k
  · rw [hjk]
    exact hsourceNone


  by_cases hjr : j = ring.rightNeighbor k
  · have hsite :
        shiftRight ring k y.val =
          shiftRight ring k 1 := by
      rw [← emptyBirthRightNeighbor_eq_shiftOne]
      exact hjr
    have hneSite :=
      emptyBirthWindowSites_ne
        ring k hfit y x1 (by
          dsimp only [x1]
          omega)
    exact False.elim (hneSite hsite)


  have hframe :=
    ghostTokenAt_ghostStep_frame
      hpsi ring step G k j kind
      hjk hjr
  rw [hframe]
  apply
    emptyBirthNoOwnerAt
      ring k kind G j
      (by
        exact ⟨y, rfl⟩)
      hempty


end PPL


#print axioms PPL.lemma4SweepEmptyBirthLiteralCases_proved
