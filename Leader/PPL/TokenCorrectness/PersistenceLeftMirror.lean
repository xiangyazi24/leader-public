import Leader.PPL.TokenCorrectness.PersistenceLeftShape
import Lean


namespace PPL


set_option autoImplicit false
set_option Elab.async false


/-!
# Remark 2 left selected mirror row


This repair keeps the original residual statements unchanged, but removes the
old metaprogrammed access to inaccessible implementation names.  The local
definitions below are literal, definitionally equal mirrors of the selected
ghost row and of Algorithm 3.  All bridges out of this file use public
declarations.
-/


/-! ## Local literal mirrors -/


private def leftMirrorBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def leftMirrorMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def leftMirrorLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))


private instance instDecidableLeftMirrorLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (leftMirrorLocalValid kind q t) := by
  unfold leftMirrorLocalValid
  infer_instance


private def leftMirrorSetToken {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def leftMirrorClearInvalid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if leftMirrorLocalValid kind q t then
        q
      else
        leftMirrorSetToken kind q none


private def leftMirrorLeaderBirth {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


private theorem leftMirrorSourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : Option (TokenData psi)) :
    sourceSet kind q t =
      leftMirrorSetToken kind q t := by
  cases kind <;> rfl


private theorem leftMirrorSourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    sourceClear kind q =
      leftMirrorClearInvalid kind q := by
  cases kind <;> rfl


private theorem leftMirrorSourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    sourceBirth q = leftMirrorLeaderBirth q := by
  rfl


private def leftMirrorNegTurnNext {psi : Nat}
    (hpsi : 2 <= psi) (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    leftMirrorMkToken
      (offsetPsiCode psi hpsi)
      (leftMirrorBitToFin (!sourceBit))
      (leftMirrorBitToFin sourceBit)
  else
    leftMirrorMkToken
      (offsetPsiCode psi hpsi)
      (leftMirrorBitToFin sourceBit)
      (0 : Fin 2)


private theorem leftMirrorNegTurnNext_eq_value
    {psi : Nat}
    (hpsi : 2 <= psi) (sourceBit : Bool)
    (t : TokenData psi) :
    leftMirrorNegTurnNext hpsi sourceBit t =
      remark2NegTurnValue hpsi sourceBit t := by
  rw [remark2NegTurnValue_eq_next]
  rfl


private def leftMirrorLiveShadow
    {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if And
              (z.value = t)
              (leftMirrorLocalValid kind q t) then
            some z
          else
            none


private def leftMirrorLiveValue
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if leftMirrorLocalValid kind q t then
        some t
      else
        none


private def leftMirrorBirthGhost
    {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      leftMirrorMkToken
        (offsetPsiCode psi hpsi)
        (leftMirrorBitToFin (!idBit))
        (leftMirrorBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }


private def leftMirrorBumpTo
    {n psi kappa : Nat}
    (kind : TokenKind) (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' : LineageMeta n :=
        { z.lmeta with
          moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if leftMirrorLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩


private def leftMirrorGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := leftMirrorLiveValue kind l
  let rv0 := leftMirrorLiveValue kind r
  let gl0 := leftMirrorLiveShadow kind l gl
  let gr0 := leftMirrorLiveShadow kind r gr
  if hlast : And
      (l.last = false)
      (r.last = false) then
    let born :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (leftMirrorBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And
          (l.dist.val = tokenD' psi kind)
          (lv0 = none) then
        some
          (leftMirrorBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide :=
      And (lv1 ≠ none) (rv0 ≠ none)
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if h1 : c = 1 then
          let next :=
            leftMirrorMkToken
              (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b :=
            leftMirrorBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            leftMirrorMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          let b :=
            leftMirrorBumpTo
              kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none =>
              ⟨gl2, gr0, []⟩
          | some t =>
              let c :=
                decodeOffset psi (tokenCode t)
              if hm1 : c = -1 then
                let next :=
                  leftMirrorNegTurnNext
                    hpsi l.id t
                let b :=
                  leftMirrorBumpTo
                    kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid
                    psi (by omega) (tokenCode t)
                let next :=
                  leftMirrorMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                    t.1.2 t.2
                let b :=
                  leftMirrorBumpTo
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
            if hm1 : c = -1 then
              let next :=
                leftMirrorNegTurnNext
                  hpsi l.id t
              let b :=
                leftMirrorBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                leftMirrorMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                leftMirrorBumpTo
                  kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩


/-- Literal Algorithm 3, expressed only through public aliases for the three
implementation helpers that are not public declarations themselves. -/
private def leftMirrorMoveToken
    {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
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
            (leftMirrorMkToken
              (offsetPsiCode psi hpsi)
              (leftMirrorBitToFin (!l.id))
              (leftMirrorBitToFin l.id)))
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
            let c :=
              decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                leftMirrorNegTurnNext
                  hpsi l.id t
              let l :=
                sourceSet kind l (some next)
              let r :=
                sourceSet kind r none
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
                    (leftMirrorMkToken
                      nextOffset t.1.2 t.2))
              let r :=
                sourceSet kind r none
              (l, r)
            else
              (l, r)
    match tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c :=
          decodeOffset psi (tokenCode t)
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
                (leftMirrorMkToken
                  (offsetNegPsiPlusOneCode psi hpsi)
                  t.1.2 t.2))
          let l :=
            sourceSet kind l none
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
                (leftMirrorMkToken
                  nextOffset t.1.2 t.2))
          let l :=
            sourceSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)


private theorem leftMirrorMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa) :
    leftMirrorMoveToken hpsi kind l r =
      moveToken hpsi kind l r := by
  cases kind <;> rfl


/-! ## Cyclic geometry for the ordinary negative move -/


private theorem leftMirrorAddOneValid
    {psi : Nat} {c : Int}
    (hc : ValidOffset psi c)
    (hm2 : c <= -2) :
    ValidOffset psi (c + 1) := by
  rcases hc with hn | hp
  · left
    omega
  · exfalso
    omega


private theorem leftMirrorNatAbsAddOne
    (c : Int)
    (hc : c <= -2) :
    (c + 1).natAbs + 1 = c.natAbs := by
  cases c with
  | ofNat m =>
      omega
  | negSucc m =>
      cases m with
      | zero =>
          omega
      | succ m =>
          rfl


/-- Moving one edge left while increasing a negative offset by one preserves
the physical target.  This is the only cyclic-position calculation needed by
the responder ordinary-move row. -/
private theorem leftMirrorShiftLeftRightNeighborSucc
    {n : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (d : Nat) :
    shiftLeft ring e d =
      shiftLeft ring (ring.rightNeighbor e) (d + 1) := by
  apply Fin.ext
  simp only [shiftLeft, DirectedRing.rightNeighbor]
  have hn : 0 < n := ring.hn
  by_cases hn1 : n = 1
  · subst n
    simp
  have h1n : 1 < n := by
    omega
  have hd : d % n < n :=
    Nat.mod_lt _ hn
  have he : e.val < n :=
    e.isLt
  have hdSucc :
      (d + 1) % n =
        (d % n + 1) % n := by
    rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt h1n]
  rw [hdSucc]
  by_cases hd1 : d % n + 1 < n
  · rw [Nat.mod_eq_of_lt hd1]
    by_cases he1 : e.val + 1 < n
    · rw [Nat.mod_eq_of_lt he1]
      congr 1
      omega
    · have heq : e.val + 1 = n := by
        omega
      rw [heq, Nat.mod_self]
      have hA :
          e.val + n - d % n =
            n + (n - d % n - 1) := by
        omega
      have hB :
          n - (d % n + 1) =
            n - d % n - 1 := by
        omega
      have hk :
          n - d % n - 1 < n := by
        omega
      rw [hA]
      simp only [Nat.zero_add]
      rw [hB]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
  · have hdEq : d % n + 1 = n := by
      omega
    rw [hdEq, Nat.mod_self]
    have hdVal : d % n = n - 1 := by
      omega
    rw [hdVal]
    have hA :
        e.val + n - (n - 1) =
          e.val + 1 := by
      omega
    rw [hA]
    simp [Nat.add_mod]


private theorem leftMirrorNegativeTarget
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hm2 :
      decodeOffset psi (tokenCode t) <= -2) :
    tokenTargetSite ring e
        ((encodeOffset psi
              (decodeOffset psi (tokenCode t) + 1)
              (leftMirrorAddOneValid
                (decodeOffset_valid
                  psi (by omega) (tokenCode t))
                hm2),
            t.1.2),
          t.2) =
      tokenTargetSite ring
        (ring.rightNeighbor e) t := by
  let c : Int :=
    decodeOffset psi (tokenCode t)
  have hc : c <= -2 := by
    simpa [c] using hm2
  have hv : ValidOffset psi c :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  have hv1 : ValidOffset psi (c + 1) :=
    leftMirrorAddOneValid hv hc
  change
    tokenTargetSite ring e
        ((encodeOffset psi (c + 1) hv1,
            t.1.2),
          t.2) =
      tokenTargetSite ring
        (ring.rightNeighbor e) t
  have hneg : Not (0 < c) := by
    omega
  have hneg1 : Not (0 < c + 1) := by
    omega
  have habs :
      (c + 1).natAbs + 1 = c.natAbs :=
    leftMirrorNatAbsAddOne c hc
  have hneg' :
      Not (0 < decodeOffset psi (tokenCode t)) := by
    simpa [c] using hneg
  have hde :
      decodeOffset psi (encodeOffset psi (c + 1) hv1) = c + 1 :=
    decode_encode psi (c + 1) hv1
  simp only [tokenTargetSite]
  have hcode :
      tokenCode ((encodeOffset psi (c + 1) hv1, t.1.2), t.2) =
        encodeOffset psi (c + 1) hv1 :=
    rfl
  simp only [hcode, hde, if_neg hneg1, if_neg hneg']
  have hs :=
    leftMirrorShiftLeftRightNeighborSucc
      ring e (c + 1).natAbs
  rw [habs] at hs
  simpa [c] using hs


/-! ## The finite selected-colour row -/


private def LeftMirrorSelectedMirrorRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi),
    (forall (zl : GhostToken n psi),
      gl = some zl ->
      zl.lmeta.id ≠ z.lmeta.id) ->
    z.lmeta.id ≠ .born kind step ->
    forall (z' : GhostToken n psi),
      And
        ((leftMirrorGhostMoveToken
              hpsi kind step e
              l r gl (some z)).right =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).2 =
              some z.value))
        ((leftMirrorGhostMoveToken
              hpsi kind step e
              l r gl (some z)).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          Or
            (And
              (tokenAt kind
                  (moveToken hpsi kind l r).1 =
                some z'.value)
              (And
                (decodeOffset psi
                    (tokenCode z.value) < 0)
                (And
                  (decodeOffset psi
                      (tokenCode z'.value) < 0)
                  (And
                    (tokenTargetSite ring e
                        z'.value =
                      tokenTargetSite ring
                        (ring.rightNeighbor e)
                        z.value)
                    (And
                      (tokenBitBool z'.value =
                        tokenBitBool z.value)
                      (tokenCarryBool z'.value =
                        tokenCarryBool z.value))))))
            (And
              (decodeOffset psi
                  (tokenCode z.value) = -1)
              (And
                (tokenAt kind
                    (moveToken hpsi kind l r).1 =
                  some z'.value)
                (z'.value =
                  remark2NegTurnValue
                    hpsi l.id z.value))))


private theorem leftMirrorSelectedMirrorRow_defeq :
    Remark2LeftSelectedMirrorRow =
      LeftMirrorSelectedMirrorRow := by
  rfl

/-! ## Small lineage classifiers -/

private def LeftMirrorNoId
    {n psi : Nat}
    (z : GhostToken n psi)
    (g : Option (GhostToken n psi)) : Prop :=
  forall u : GhostToken n psi,
    g = some u ->
    u.lmeta.id = z.lmeta.id ->
    False

private def LeftMirrorTrackedSource
    {n psi : Nat}
    (z : GhostToken n psi)
    (v : Option (TokenData psi))
    (g : Option (GhostToken n psi)) : Prop :=
  forall u : GhostToken n psi,
    g = some u ->
    u.lmeta.id = z.lmeta.id ->
    And
      (u = z)
      (v = some z.value)

private theorem leftMirrorSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi)) :
    tokenAt kind (sourceSet kind q v) = v := by
  rw [leftMirrorSourceSet_eq]
  cases kind <;> rfl

private theorem leftMirrorSourceSet_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : Option (TokenData psi)) :
    let q' := sourceSet kind q v
    And
      (q'.dist = q.dist)
      (And
        (q'.last = q.last)
        (q'.id = q.id)) := by
  dsimp only
  rw [leftMirrorSourceSet_eq]
  cases kind <;>
    exact And.intro rfl (And.intro rfl rfl)

private theorem leftMirrorSourceClear_token_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (ht : tokenAt kind q = some t) :
    tokenAt kind (sourceClear kind q) =
      leftMirrorLiveValue kind q := by
  rw [leftMirrorSourceClear_eq]
  unfold leftMirrorClearInvalid
    leftMirrorLiveValue
  simp only [ht]
  by_cases hv :
      leftMirrorLocalValid kind q t
  · simp only [if_pos hv, ht]
  · simp only [if_neg hv]
    rw [← leftMirrorSourceSet_eq]
    exact leftMirrorSourceSet_token kind q none

private theorem leftMirrorSourceClear_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    tokenAt kind (sourceClear kind q) =
      leftMirrorLiveValue kind q := by
  cases ht : tokenAt kind q with
  | none =>
      rw [leftMirrorSourceClear_eq]
      unfold leftMirrorClearInvalid
        leftMirrorLiveValue
      simp only [ht]
  | some t =>
      exact
        leftMirrorSourceClear_token_some
          kind q t ht

private theorem leftMirrorSourceClear_fields_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (ht : tokenAt kind q = some t) :
    let q0 := sourceClear kind q
    And
      (q0.dist = q.dist)
      (And
        (q0.last = q.last)
        (q0.id = q.id)) := by
  dsimp only
  rw [leftMirrorSourceClear_eq]
  unfold leftMirrorClearInvalid
  simp only [ht]
  by_cases hv :
      leftMirrorLocalValid kind q t
  · simp only [if_pos hv]
    exact And.intro (by first | rfl | trivial) (And.intro (by first | rfl | trivial) (by first | rfl | trivial))
  · simp only [if_neg hv]
    rw [← leftMirrorSourceSet_eq]
    exact leftMirrorSourceSet_fields kind q none

private theorem leftMirrorSourceClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    let q0 := sourceClear kind q
    And
      (q0.dist = q.dist)
      (And
        (q0.last = q.last)
        (q0.id = q.id)) := by
  cases ht : tokenAt kind q with
  | none =>
      dsimp only
      rw [leftMirrorSourceClear_eq]
      unfold leftMirrorClearInvalid
      simp only [ht]
      exact And.intro (by first | rfl | trivial) (And.intro (by first | rfl | trivial) (by first | rfl | trivial))
  | some t =>
      exact
        leftMirrorSourceClear_fields_some
          kind q t ht

private theorem leftMirrorLiveShadow_origin_token
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g u : GhostToken n psi)
    (t : TokenData psi)
    (ht : tokenAt kind q = some t)
    (hpost :
      leftMirrorLiveShadow kind q (some g) =
        some u) :
    And
      (g = u)
      (leftMirrorLiveValue kind q =
        some u.value) := by
  by_cases hkeep :
      And
        (g.value = t)
        (leftMirrorLocalValid kind q t)
  · simp only
      [leftMirrorLiveShadow, ht,
        if_pos hkeep, Option.some.injEq] at hpost
    have hgu : g = u := hpost
    subst u
    refine And.intro rfl ?_
    unfold leftMirrorLiveValue
    simp only [ht, if_pos hkeep.2]
    rw [hkeep.1]
  · simp only
      [leftMirrorLiveShadow, ht,
        if_neg hkeep] at hpost
    cases hpost

private theorem leftMirrorLiveShadow_origin_some
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g u : GhostToken n psi)
    (hpost :
      leftMirrorLiveShadow kind q (some g) =
        some u) :
    And
      (g = u)
      (leftMirrorLiveValue kind q =
        some u.value) := by
  cases ht : tokenAt kind q with
  | none =>
      simp only
        [leftMirrorLiveShadow, ht] at hpost
      cases hpost
  | some t =>
      exact
        leftMirrorLiveShadow_origin_token
          kind q g u t ht hpost

private theorem leftMirrorLiveShadow_origin
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (u : GhostToken n psi)
    (hpost :
      leftMirrorLiveShadow kind q g =
        some u) :
    And
      (g = some u)
      (leftMirrorLiveValue kind q =
        some u.value) := by
  cases g with
  | none =>
      simp only [leftMirrorLiveShadow] at hpost
      cases hpost
  | some g0 =>
      have hs :=
        leftMirrorLiveShadow_origin_some
          kind q g0 u hpost
      refine And.intro ?_ hs.2
      rw [hs.1]

private theorem leftMirrorLiveShadow_noId
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNo : LeftMirrorNoId z g) :
    LeftMirrorNoId z
      (leftMirrorLiveShadow kind q g) := by
  intro u hpost hid
  have hs :=
    leftMirrorLiveShadow_origin
      kind q g u hpost
  exact hNo u hs.1 hid

private theorem leftMirrorLiveShadow_tracked
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (z : GhostToken n psi) :
    LeftMirrorTrackedSource
      z
      (leftMirrorLiveValue kind q)
      (leftMirrorLiveShadow kind q (some z)) := by
  intro u hpost _hid
  have hs :=
    leftMirrorLiveShadow_origin
      kind q (some z) u hpost
  have hzu : z = u :=
    Option.some.inj hs.1
  have huz : u = z := hzu.symm
  subst u
  exact And.intro rfl hs.2

private theorem leftMirrorBirth_noId
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (z : GhostToken n psi)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step) :
    LeftMirrorNoId z
      (some
        (leftMirrorBirthGhost
          hpsi kind step site idBit)) := by
  intro u hu hid
  have hbu :
      leftMirrorBirthGhost
          hpsi kind step site idBit = u :=
    Option.some.inj hu
  have hub : u =
      leftMirrorBirthGhost
        hpsi kind step site idBit :=
    hbu.symm
  subst u
  change
    LineageId.born kind step =
      z.lmeta.id at hid
  exact hNotFresh hid.symm

private theorem leftMirrorBumpNoId_some
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (g z u : GhostToken n psi)
    (hNo :
      LeftMirrorNoId z (some g))
    (hpost :
      (leftMirrorBumpTo kind q v (some g)).live =
        some u)
    (hid : u.lmeta.id = z.lmeta.id) :
    False := by
  by_cases hv :
      leftMirrorLocalValid kind q v
  · simp only
      [leftMirrorBumpTo, if_pos hv,
        Option.some.injEq] at hpost
    cases hpost
    change g.lmeta.id = z.lmeta.id at hid
    exact hNo g rfl hid
  · simp only
      [leftMirrorBumpTo, if_neg hv] at hpost
    cases hpost

private theorem leftMirrorBumpNoId
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (g : Option (GhostToken n psi))
    (z u : GhostToken n psi)
    (hNo : LeftMirrorNoId z g)
    (hpost :
      (leftMirrorBumpTo kind q v g).live =
        some u)
    (hid : u.lmeta.id = z.lmeta.id) :
    False := by
  cases g with
  | none =>
      simp only [leftMirrorBumpTo] at hpost
      cases hpost
  | some g0 =>
      exact
        leftMirrorBumpNoId_some
          kind q v g0 z u
          hNo hpost hid

private theorem leftMirrorBumpTracked_some
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (rv : Option (TokenData psi))
    (g z u : GhostToken n psi)
    (hTracked :
      LeftMirrorTrackedSource z rv (some g))
    (hpost :
      (leftMirrorBumpTo kind q v (some g)).live =
        some u)
    (hid : u.lmeta.id = z.lmeta.id) :
    And
      (u.value = v)
      (rv = some z.value) := by
  by_cases hv :
      leftMirrorLocalValid kind q v
  · simp only
      [leftMirrorBumpTo, if_pos hv,
        Option.some.injEq] at hpost
    cases hpost
    change g.lmeta.id = z.lmeta.id at hid
    have hs :=
      hTracked g rfl hid
    exact And.intro rfl hs.2
  · simp only
      [leftMirrorBumpTo, if_neg hv] at hpost
    cases hpost

private theorem leftMirrorBumpTracked
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (rv : Option (TokenData psi))
    (g : Option (GhostToken n psi))
    (z u : GhostToken n psi)
    (hTracked :
      LeftMirrorTrackedSource z rv g)
    (hpost :
      (leftMirrorBumpTo kind q v g).live =
        some u)
    (hid : u.lmeta.id = z.lmeta.id) :
    And
      (u.value = v)
      (rv = some z.value) := by
  cases g with
  | none =>
      simp only [leftMirrorBumpTo] at hpost
      cases hpost
  | some g0 =>
      exact
        leftMirrorBumpTracked_some
          kind q v rv g0 z u
          hTracked hpost hid

/-! ## Explicit physical and ghost suffixes -/

private theorem leftMirrorSubOneValid
    {psi : Nat} {c : Int}
    (hc : ValidOffset psi c)
    (h2 : 2 <= c) :
    ValidOffset psi (c - 1) := by
  rcases hc with hn | hp
  · exfalso
    omega
  · right
    omega

private def leftMirrorRightTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi) :
    TokenData psi :=
  leftMirrorMkToken
    (offsetNegPsiPlusOneCode psi hpsi)
    t.1.2 t.2

private def leftMirrorPositiveNext
    {psi : Nat}
    (t : TokenData psi)
    (h2 :
      2 <= decodeOffset psi (tokenCode t)) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hc : ValidOffset psi c :=
    decodeOffset_valid
      psi (by have := (tokenCode t).isLt; omega) (tokenCode t)
  leftMirrorMkToken
    (encodeOffset psi (c - 1)
      (leftMirrorSubOneValid hc h2))
    t.1.2 t.2

private def leftMirrorNegativeNext
    {psi : Nat}
    (t : TokenData psi)
    (hm2 :
      decodeOffset psi (tokenCode t) <= -2) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hc : ValidOffset psi c :=
    decodeOffset_valid
      psi (by have := (tokenCode t).isLt; omega) (tokenCode t)
  leftMirrorMkToken
    (encodeOffset psi (c + 1)
      (leftMirrorAddOneValid hc hm2))
    t.1.2 t.2

private def leftMirrorOneResponder
    {psi kappa : Nat}
    (r : State psi kappa)
    (bit : Bool) :
    State psi kappa :=
  if r.mode = true ∧ bit ≠ r.id then
    sourceBirth r
  else if r.mode = false then
    { r with id := bit }
  else
    r

private def leftMirrorPhysicalFinish
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
      | some tr =>
          let cr :=
            decodeOffset psi (tokenCode tr)
          if hm1 : cr = -1 then
            let next :=
              leftMirrorNegTurnNext
                hpsi l.id tr
            (sourceSet kind l (some next),
              sourceSet kind r none)
          else if hm2 : cr <= -2 then
            let next :=
              leftMirrorNegativeNext tr hm2
            (sourceSet kind l (some next),
              sourceSet kind r none)
          else
            (l, r)
  match tokenAt kind l with
  | none =>
      moveLeft l r
  | some t =>
      let c :=
        decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let bit := tokenBitBool t
        let r1 :=
          leftMirrorOneResponder r bit
        (sourceSet kind l none,
          sourceSet kind r1
            (some
              (leftMirrorRightTurnNext
                hpsi t)))
      else if h2 : 2 <= c then
        (sourceSet kind l none,
          sourceSet kind r
            (some
              (leftMirrorPositiveNext t h2)))
      else
        moveLeft l r

private def leftMirrorGhostFinish
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (baseL baseR : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match lv with
  | some t =>
      let c :=
        decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let b :=
          leftMirrorBumpTo
            kind baseR
            (leftMirrorRightTurnNext hpsi t)
            gl
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        let b :=
          leftMirrorBumpTo
            kind baseR
            (leftMirrorPositiveNext t h2)
            gl
        ⟨none, b.live, b.done⟩
      else
        match rv with
        | none =>
            ⟨gl, gr, []⟩
        | some tr =>
            let cr :=
              decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let b :=
                leftMirrorBumpTo
                  kind baseL
                  (leftMirrorNegTurnNext
                    hpsi baseL.id tr)
                  gr
              ⟨b.live, none, b.done⟩
            else if hm2 : cr <= -2 then
              let b :=
                leftMirrorBumpTo
                  kind baseL
                  (leftMirrorNegativeNext tr hm2)
                  gr
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
          if hm1 : cr = -1 then
            let b :=
              leftMirrorBumpTo
                kind baseL
                (leftMirrorNegTurnNext
                  hpsi baseL.id tr)
                gr
            ⟨b.live, none, b.done⟩
          else if hm2 : cr <= -2 then
            let b :=
              leftMirrorBumpTo
                kind baseL
                (leftMirrorNegativeNext tr hm2)
                gr
            ⟨b.live, none, b.done⟩
          else
            ⟨gl, gr, []⟩

private def LeftMirrorRightFinishConclusion
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (z z' : GhostToken n psi) : Prop :=
  And
    (z' = z)
    (tokenAt kind q = some z.value)

private def LeftMirrorLeftFinishConclusion
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL q : State psi kappa)
    (z z' : GhostToken n psi) : Prop :=
  Or
    (And
      (tokenAt kind q = some z'.value)
      (And
        (decodeOffset psi
            (tokenCode z.value) < 0)
        (And
          (decodeOffset psi
              (tokenCode z'.value) < 0)
          (And
            (tokenTargetSite ring e z'.value =
              tokenTargetSite ring
                (ring.rightNeighbor e)
                z.value)
            (And
              (tokenBitBool z'.value =
                tokenBitBool z.value)
              (tokenCarryBool z'.value =
                tokenCarryBool z.value))))))
    (And
      (decodeOffset psi
          (tokenCode z.value) = -1)
      (And
        (tokenAt kind q = some z'.value)
        (z'.value =
          remark2NegTurnValue
            hpsi baseL.id z.value)))

private def LeftMirrorFinishClaims
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi) : Prop :=
  forall z' : GhostToken n psi,
    And
      ((leftMirrorGhostFinish
            hpsi kind baseL baseR
            lv rv gl gr).right =
          some z' ->
        z'.lmeta.id = z.lmeta.id ->
        LeftMirrorRightFinishConclusion
          kind
          (leftMirrorPhysicalFinish
            hpsi kind l r).2
          z z')
      ((leftMirrorGhostFinish
            hpsi kind baseL baseR
            lv rv gl gr).left =
          some z' ->
        z'.lmeta.id = z.lmeta.id ->
        LeftMirrorLeftFinishConclusion
          hpsi ring e kind baseL
          (leftMirrorPhysicalFinish
            hpsi kind l r).1
          z z')

/-! ## One lemma per suffix branch -/

private theorem leftMirrorFinish_some_one
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked : LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) = 1) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) rv gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost hid
    have hb :
        (leftMirrorBumpTo
            kind baseR
            (leftMirrorRightTurnNext hpsi t)
            gl).live =
          some z' := by
      simpa only
        [leftMirrorGhostFinish, dif_pos h1]
        using hpost
    exact
      False.elim
        (leftMirrorBumpNoId
          kind baseR
          (leftMirrorRightTurnNext hpsi t)
          gl z z'
          hNoLeft hb hid)
  · intro hpost _hid
    simp only
      [leftMirrorGhostFinish, dif_pos h1] at hpost
    cases hpost

private theorem leftMirrorFinish_some_geTwo
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked : LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      2 <= decodeOffset psi (tokenCode t)) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) rv gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost hid
    have hb :
        (leftMirrorBumpTo
            kind baseR
            (leftMirrorPositiveNext t h2)
            gl).live =
          some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_pos h2]
        using hpost
    exact
      False.elim
        (leftMirrorBumpNoId
          kind baseR
          (leftMirrorPositiveNext t h2)
          gl z z'
          hNoLeft hb hid)
  · intro hpost _hid
    simp only
      [leftMirrorGhostFinish,
        dif_neg h1, dif_pos h2] at hpost
    cases hpost

private theorem leftMirrorFinish_some_stay_none
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = none)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z none gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t)) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) none gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost hid
    have hgr : gr = some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_neg h2]
        using hpost
    have hs :=
      hTracked z' hgr hid
    cases hs.2
  · intro hpost hid
    have hgl : gl = some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_neg h2]
        using hpost
    exact False.elim (hNoLeft z' hgl hid)

private theorem leftMirrorFinish_some_stay_some_turn
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t))
    (hm1 :
      decodeOffset psi (tokenCode tr) = -1) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) (some tr) gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost _hid
    simp only
      [leftMirrorGhostFinish,
        dif_neg h1, dif_neg h2,
        dif_pos hm1] at hpost
    cases hpost
  · intro hpost hid
    have hb :
        (leftMirrorBumpTo
            kind baseL
            (leftMirrorNegTurnNext
              hpsi baseL.id tr)
            gr).live =
          some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_neg h2,
          dif_pos hm1]
        using hpost
    have hs :=
      leftMirrorBumpTracked
        kind baseL
        (leftMirrorNegTurnNext
          hpsi baseL.id tr)
        (some tr) gr z z'
        hTracked hb hid
    have htr : tr = z.value :=
      Option.some.inj hs.2
    have hphys :
        tokenAt kind
            (leftMirrorPhysicalFinish
              hpsi kind l r).1 =
          some
            (leftMirrorNegTurnNext
              hpsi baseL.id tr) := by
      unfold leftMirrorPhysicalFinish
      simp only
        [hL, hR,
          dif_neg h1, dif_neg h2,
          dif_pos hm1]
      rw [hLid]
      exact
        leftMirrorSourceSet_token
          kind l
          (some
            (leftMirrorNegTurnNext
              hpsi baseL.id tr))
    unfold LeftMirrorLeftFinishConclusion
    right
    refine And.intro ?_ (And.intro ?_ ?_)
    · simpa only [htr] using hm1
    · rw [hs.1]
      exact hphys
    · calc
        z'.value =
            leftMirrorNegTurnNext
              hpsi baseL.id tr := hs.1
        _ =
            leftMirrorNegTurnNext
              hpsi baseL.id z.value := by
              rw [htr]
        _ =
            remark2NegTurnValue
              hpsi baseL.id z.value :=
          leftMirrorNegTurnNext_eq_value
            hpsi baseL.id z.value

private theorem leftMirrorFinish_some_stay_some_move
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t))
    (hm1 :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hm2 :
      decodeOffset psi (tokenCode tr) <= -2) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) (some tr) gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost _hid
    simp only
      [leftMirrorGhostFinish,
        dif_neg h1, dif_neg h2,
        dif_neg hm1, dif_pos hm2] at hpost
    cases hpost
  · intro hpost hid
    have hb :
        (leftMirrorBumpTo
            kind baseL
            (leftMirrorNegativeNext tr hm2)
            gr).live =
          some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_neg h2,
          dif_neg hm1, dif_pos hm2]
        using hpost
    have hs :=
      leftMirrorBumpTracked
        kind baseL
        (leftMirrorNegativeNext tr hm2)
        (some tr) gr z z'
        hTracked hb hid
    have htr : tr = z.value :=
      Option.some.inj hs.2
    have hphys :
        tokenAt kind
            (leftMirrorPhysicalFinish
              hpsi kind l r).1 =
          some (leftMirrorNegativeNext tr hm2) := by
      unfold leftMirrorPhysicalFinish
      simp only
        [hL, hR,
          dif_neg h1, dif_neg h2,
          dif_neg hm1, dif_pos hm2]
      exact
        leftMirrorSourceSet_token
          kind l
          (some (leftMirrorNegativeNext tr hm2))
    have hnew :
        decodeOffset psi
            (tokenCode
              (leftMirrorNegativeNext tr hm2)) =
          decodeOffset psi (tokenCode tr) + 1 := by
      unfold leftMirrorNegativeNext
      dsimp only
      unfold leftMirrorMkToken
      simp only [tokenCode, decode_encode]
    unfold LeftMirrorLeftFinishConclusion
    left
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
    · rw [hs.1]
      exact hphys
    · rw [← htr]
      omega
    · rw [hs.1, hnew]
      omega
    · rw [hs.1, ← htr]
      exact
        leftMirrorNegativeTarget
          hpsi ring e tr hm2
    · rw [hs.1, ← htr]
      unfold leftMirrorNegativeNext
      rfl
    · rw [hs.1, ← htr]
      unfold leftMirrorNegativeNext
      rfl

private theorem leftMirrorFinish_some_stay_some_stay
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t))
    (hm1 :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hm2 :
      ¬ decodeOffset psi (tokenCode tr) <= -2) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) (some tr) gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost hid
    have hgr : gr = some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_neg h2,
          dif_neg hm1, dif_neg hm2]
        using hpost
    have hs :=
      hTracked z' hgr hid
    have htr : tr = z.value :=
      Option.some.inj hs.2
    have hphys :
        tokenAt kind
            (leftMirrorPhysicalFinish
              hpsi kind l r).2 =
          some tr := by
      unfold leftMirrorPhysicalFinish
      simp only
        [hL, hR,
          dif_neg h1, dif_neg h2,
          dif_neg hm1, dif_neg hm2]
      try exact hR
    unfold LeftMirrorRightFinishConclusion
    refine And.intro hs.1 ?_
    rw [← htr]
    exact hphys
  · intro hpost hid
    have hgl : gl = some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg h1, dif_neg h2,
          dif_neg hm1, dif_neg hm2]
        using hpost
    exact False.elim (hNoLeft z' hgl hid)

private theorem leftMirrorFinish_none_none
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = none)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z none gr)
    (hLid : l.id = baseL.id) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none none gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost hid
    have hgr : gr = some z' := by
      simpa only [leftMirrorGhostFinish]
        using hpost
    have hs :=
      hTracked z' hgr hid
    cases hs.2
  · intro hpost hid
    have hgl : gl = some z' := by
      simpa only [leftMirrorGhostFinish]
        using hpost
    exact False.elim (hNoLeft z' hgl hid)

private theorem leftMirrorFinish_none_some_turn
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (hm1 :
      decodeOffset psi (tokenCode tr) = -1) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none (some tr) gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost _hid
    simp only
      [leftMirrorGhostFinish,
        dif_pos hm1] at hpost
    cases hpost
  · intro hpost hid
    have hb :
        (leftMirrorBumpTo
            kind baseL
            (leftMirrorNegTurnNext
              hpsi baseL.id tr)
            gr).live =
          some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_pos hm1]
        using hpost
    have hs :=
      leftMirrorBumpTracked
        kind baseL
        (leftMirrorNegTurnNext
          hpsi baseL.id tr)
        (some tr) gr z z'
        hTracked hb hid
    have htr : tr = z.value :=
      Option.some.inj hs.2
    have hphys :
        tokenAt kind
            (leftMirrorPhysicalFinish
              hpsi kind l r).1 =
          some
            (leftMirrorNegTurnNext
              hpsi baseL.id tr) := by
      unfold leftMirrorPhysicalFinish
      simp only [hL, hR, dif_pos hm1]
      rw [hLid]
      exact
        leftMirrorSourceSet_token
          kind l
          (some
            (leftMirrorNegTurnNext
              hpsi baseL.id tr))
    unfold LeftMirrorLeftFinishConclusion
    right
    refine And.intro ?_ (And.intro ?_ ?_)
    · simpa only [htr] using hm1
    · rw [hs.1]
      exact hphys
    · calc
        z'.value =
            leftMirrorNegTurnNext
              hpsi baseL.id tr := hs.1
        _ =
            leftMirrorNegTurnNext
              hpsi baseL.id z.value := by
              rw [htr]
        _ =
            remark2NegTurnValue
              hpsi baseL.id z.value :=
          leftMirrorNegTurnNext_eq_value
            hpsi baseL.id z.value

private theorem leftMirrorFinish_none_some_move
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (hm1 :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hm2 :
      decodeOffset psi (tokenCode tr) <= -2) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none (some tr) gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost _hid
    simp only
      [leftMirrorGhostFinish,
        dif_neg hm1, dif_pos hm2] at hpost
    cases hpost
  · intro hpost hid
    have hb :
        (leftMirrorBumpTo
            kind baseL
            (leftMirrorNegativeNext tr hm2)
            gr).live =
          some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg hm1, dif_pos hm2]
        using hpost
    have hs :=
      leftMirrorBumpTracked
        kind baseL
        (leftMirrorNegativeNext tr hm2)
        (some tr) gr z z'
        hTracked hb hid
    have htr : tr = z.value :=
      Option.some.inj hs.2
    have hphys :
        tokenAt kind
            (leftMirrorPhysicalFinish
              hpsi kind l r).1 =
          some (leftMirrorNegativeNext tr hm2) := by
      unfold leftMirrorPhysicalFinish
      simp only
        [hL, hR,
          dif_neg hm1, dif_pos hm2]
      exact
        leftMirrorSourceSet_token
          kind l
          (some (leftMirrorNegativeNext tr hm2))
    have hnew :
        decodeOffset psi
            (tokenCode
              (leftMirrorNegativeNext tr hm2)) =
          decodeOffset psi (tokenCode tr) + 1 := by
      unfold leftMirrorNegativeNext
      dsimp only
      unfold leftMirrorMkToken
      simp only [tokenCode, decode_encode]
    unfold LeftMirrorLeftFinishConclusion
    left
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
    · rw [hs.1]
      exact hphys
    · rw [← htr]
      omega
    · rw [hs.1, hnew]
      omega
    · rw [hs.1, ← htr]
      exact
        leftMirrorNegativeTarget
          hpsi ring e tr hm2
    · rw [hs.1, ← htr]
      unfold leftMirrorNegativeNext
      rfl
    · rw [hs.1, ← htr]
      unfold leftMirrorNegativeNext
      rfl

private theorem leftMirrorFinish_none_some_stay
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (hm1 :
      decodeOffset psi (tokenCode tr) ≠ -1)
    (hm2 :
      ¬ decodeOffset psi (tokenCode tr) <= -2) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none (some tr) gl gr z := by
  unfold LeftMirrorFinishClaims
  intro z'
  constructor
  · intro hpost hid
    have hgr : gr = some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg hm1, dif_neg hm2]
        using hpost
    have hs :=
      hTracked z' hgr hid
    have htr : tr = z.value :=
      Option.some.inj hs.2
    have hphys :
        tokenAt kind
            (leftMirrorPhysicalFinish
              hpsi kind l r).2 =
          some tr := by
      unfold leftMirrorPhysicalFinish
      simp only
        [hL, hR,
          dif_neg hm1, dif_neg hm2]
      try exact hR
    unfold LeftMirrorRightFinishConclusion
    refine And.intro hs.1 ?_
    rw [← htr]
    exact hphys
  · intro hpost hid
    have hgl : gl = some z' := by
      simpa only
        [leftMirrorGhostFinish,
          dif_neg hm1, dif_neg hm2]
        using hpost
    exact False.elim (hNoLeft z' hgl hid)

/-! ## One-level dispatchers -/

private theorem leftMirrorFinish_dispatch_some_stay_some_after_m1
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t))
    (hm1 :
      decodeOffset psi (tokenCode tr) ≠ -1) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) (some tr) gl gr z := by
  by_cases hm2 :
      decodeOffset psi (tokenCode tr) <= -2
  · exact
      leftMirrorFinish_some_stay_some_move
        hpsi ring e kind
        baseL baseR l r t tr gl gr z
        hL hR hNoLeft hTracked hLid
        h1 h2 hm1 hm2
  · exact
      leftMirrorFinish_some_stay_some_stay
        hpsi ring e kind
        baseL baseR l r t tr gl gr z
        hL hR hNoLeft hTracked hLid
        h1 h2 hm1 hm2

private theorem leftMirrorFinish_dispatch_some_stay_some
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t)) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) (some tr) gl gr z := by
  by_cases hm1 :
      decodeOffset psi (tokenCode tr) = -1
  · exact
      leftMirrorFinish_some_stay_some_turn
        hpsi ring e kind
        baseL baseR l r t tr gl gr z
        hL hR hNoLeft hTracked hLid
        h1 h2 hm1
  · exact
      leftMirrorFinish_dispatch_some_stay_some_after_m1
        hpsi ring e kind
        baseL baseR l r t tr gl gr z
        hL hR hNoLeft hTracked hLid
        h1 h2 hm1

private theorem leftMirrorFinish_dispatch_some_stay
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1)
    (h2 :
      ¬ 2 <= decodeOffset psi (tokenCode t)) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) rv gl gr z := by
  cases rv with
  | none =>
      exact
        leftMirrorFinish_some_stay_none
          hpsi ring e kind
          baseL baseR l r t gl gr z
          hL hR hNoLeft hTracked hLid
          h1 h2
  | some tr =>
      exact
        leftMirrorFinish_dispatch_some_stay_some
          hpsi ring e kind
          baseL baseR l r t tr gl gr z
          hL hR hNoLeft hTracked hLid
          h1 h2

private theorem leftMirrorFinish_dispatch_some_after_one
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id)
    (h1 :
      decodeOffset psi (tokenCode t) ≠ 1) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) rv gl gr z := by
  by_cases h2 :
      2 <= decodeOffset psi (tokenCode t)
  · exact
      leftMirrorFinish_some_geTwo
        hpsi ring e kind
        baseL baseR l r t rv gl gr z
        hL hR hNoLeft hTracked hLid
        h1 h2
  · exact
      leftMirrorFinish_dispatch_some_stay
        hpsi ring e kind
        baseL baseR l r t rv gl gr z
        hL hR hNoLeft hTracked hLid
        h1 h2

private theorem leftMirrorFinish_dispatch_some
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (t : TokenData psi)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = some t)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      (some t) rv gl gr z := by
  by_cases h1 :
      decodeOffset psi (tokenCode t) = 1
  · exact
      leftMirrorFinish_some_one
        hpsi ring e kind
        baseL baseR l r t rv gl gr z
        hL hR hNoLeft hTracked hLid
        h1
  · exact
      leftMirrorFinish_dispatch_some_after_one
        hpsi ring e kind
        baseL baseR l r t rv gl gr z
        hL hR hNoLeft hTracked hLid
        h1

private theorem leftMirrorFinish_dispatch_none_some_after_m1
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id)
    (hm1 :
      decodeOffset psi (tokenCode tr) ≠ -1) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none (some tr) gl gr z := by
  by_cases hm2 :
      decodeOffset psi (tokenCode tr) <= -2
  · exact
      leftMirrorFinish_none_some_move
        hpsi ring e kind
        baseL baseR l r tr gl gr z
        hL hR hNoLeft hTracked hLid
        hm1 hm2
  · exact
      leftMirrorFinish_none_some_stay
        hpsi ring e kind
        baseL baseR l r tr gl gr z
        hL hR hNoLeft hTracked hLid
        hm1 hm2

private theorem leftMirrorFinish_dispatch_none_some
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (tr : TokenData psi)
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = some tr)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z (some tr) gr)
    (hLid : l.id = baseL.id) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none (some tr) gl gr z := by
  by_cases hm1 :
      decodeOffset psi (tokenCode tr) = -1
  · exact
      leftMirrorFinish_none_some_turn
        hpsi ring e kind
        baseL baseR l r tr gl gr z
        hL hR hNoLeft hTracked hLid
        hm1
  · exact
      leftMirrorFinish_dispatch_none_some_after_m1
        hpsi ring e kind
        baseL baseR l r tr gl gr z
        hL hR hNoLeft hTracked hLid
        hm1

private theorem leftMirrorFinish_dispatch_none
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = none)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      none rv gl gr z := by
  cases rv with
  | none =>
      exact
        leftMirrorFinish_none_none
          hpsi ring e kind
          baseL baseR l r gl gr z
          hL hR hNoLeft hTracked hLid
  | some tr =>
      exact
        leftMirrorFinish_dispatch_none_some
          hpsi ring e kind
          baseL baseR l r tr gl gr z
          hL hR hNoLeft hTracked hLid

private theorem leftMirrorFinish_dispatch
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (kind : TokenKind)
    (baseL baseR l r : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hL : tokenAt kind l = lv)
    (hR : tokenAt kind r = rv)
    (hNoLeft : LeftMirrorNoId z gl)
    (hTracked :
      LeftMirrorTrackedSource z rv gr)
    (hLid : l.id = baseL.id) :
    LeftMirrorFinishClaims
      hpsi ring e kind
      baseL baseR l r
      lv rv gl gr z := by
  cases lv with
  | none =>
      exact
        leftMirrorFinish_dispatch_none
          hpsi ring e kind
          baseL baseR l r rv gl gr z
          hL hR hNoLeft hTracked hLid
  | some t =>
      exact
        leftMirrorFinish_dispatch_some
          hpsi ring e kind
          baseL baseR l r t rv gl gr z
          hL hR hNoLeft hTracked hLid

/-! ## Prefix synchronization, one guard at a time -/

private theorem leftMirrorSelectedMirrorRow_open
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft :
      forall zl : GhostToken n psi,
        gl = some zl ->
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hgate :
      l.last = false ∧ r.last = false) :
    forall z' : GhostToken n psi,
      And
        ((leftMirrorGhostMoveToken
              hpsi kind step e
              l r gl (some z)).right =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).2 =
              some z.value))
        ((leftMirrorGhostMoveToken
              hpsi kind step e
              l r gl (some z)).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          Or
            (And
              (tokenAt kind
                  (moveToken hpsi kind l r).1 =
                some z'.value)
              (And
                (decodeOffset psi
                    (tokenCode z.value) < 0)
                (And
                  (decodeOffset psi
                      (tokenCode z'.value) < 0)
                  (And
                    (tokenTargetSite ring e
                        z'.value =
                      tokenTargetSite ring
                        (ring.rightNeighbor e)
                        z.value)
                    (And
                      (tokenBitBool z'.value =
                        tokenBitBool z.value)
                      (tokenCarryBool z'.value =
                        tokenCarryBool z.value)))))) 
            (And
              (decodeOffset psi
                  (tokenCode z.value) = -1)
              (And
                (tokenAt kind
                    (moveToken hpsi kind l r).1 =
                  some z'.value)
                (z'.value =
                  remark2NegTurnValue
                    hpsi l.id z.value)))) := by
  classical

  let l0 := sourceClear kind l
  let r0 := sourceClear kind r
  let lv0 := leftMirrorLiveValue kind l
  let rv0 := leftMirrorLiveValue kind r
  let gl0 := leftMirrorLiveShadow kind l gl
  let gr0 := leftMirrorLiveShadow kind r (some z)

  have hL0 :
      tokenAt kind l0 = lv0 := by
    simpa only [l0, lv0]
      using leftMirrorSourceClear_token kind l
  have hR0 :
      tokenAt kind r0 = rv0 := by
    simpa only [r0, rv0]
      using leftMirrorSourceClear_token kind r

  have hL0fields :=
    leftMirrorSourceClear_fields kind l
  have hR0fields :=
    leftMirrorSourceClear_fields kind r

  have hL0dist : l0.dist = l.dist := by
    simpa only [l0] using hL0fields.1
  have hL0last : l0.last = l.last := by
    simpa only [l0] using hL0fields.2.1
  have hL0id : l0.id = l.id := by
    simpa only [l0] using hL0fields.2.2
  have hR0last : r0.last = r.last := by
    simpa only [r0] using hR0fields.2.1

  have hgate0 :
      l0.last = false ∧ r0.last = false := by
    exact
      And.intro
        (hL0last.trans hgate.1)
        (hR0last.trans hgate.2)

  have hNoInput : LeftMirrorNoId z gl := by
    intro u hu hid
    exact hNoLeft u hu hid

  have hgl0 : LeftMirrorNoId z gl0 := by
    simpa only [gl0]
      using
        leftMirrorLiveShadow_noId
          kind l gl z hNoInput

  have hgr0 :
      LeftMirrorTrackedSource z rv0 gr0 := by
    simpa only [rv0, gr0]
      using
        leftMirrorLiveShadow_tracked
          kind r z

  let hb : Prop :=
    l.dist.val = tokenD' psi kind ∧
      lv0 = none
  let birth :=
    leftMirrorBirthGhost
      hpsi kind step e l.id
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
      tokenAt kind l1 = lv1 := by
    by_cases hbirth : hb
    · simp only
        [l1, lv1, if_pos hbirth]
      exact
        leftMirrorSourceSet_token
          kind l0 (some birth.value)
    · simpa only
        [l1, lv1, if_neg hbirth]
        using hL0

  have hL1id : l1.id = l.id := by
    by_cases hbirth : hb
    · simp only [l1, if_pos hbirth]
      exact
        (leftMirrorSourceSet_fields
          kind l0 (some birth.value)).2.2.trans
          hL0id
    · simpa only [l1, if_neg hbirth]
        using hL0id

  have hgl1 : LeftMirrorNoId z gl1 := by
    by_cases hbirth : hb
    · simp only [gl1, if_pos hbirth]
      simpa only [birth]
        using
          leftMirrorBirth_noId
            hpsi kind step e l.id z
            hNotFresh
    · simpa only [gl1, if_neg hbirth]
        using hgl0

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
      tokenAt kind l2 = lv2 := by
    by_cases hcol : collide
    · simp only
        [l2, lv2, if_pos hcol]
      exact
        leftMirrorSourceSet_token
          kind l1 none
    · simpa only
        [l2, lv2, if_neg hcol]
        using hL1

  have hL2id : l2.id = l.id := by
    by_cases hcol : collide
    · simp only [l2, if_pos hcol]
      exact
        (leftMirrorSourceSet_fields
          kind l1 none).2.2.trans
          hL1id
    · simpa only [l2, if_neg hcol]
        using hL1id

  have hgl2 : LeftMirrorNoId z gl2 := by
    by_cases hcol : collide
    · simp only [gl2, if_pos hcol]
      intro u hu _hid
      cases hu
    · simpa only [gl2, if_neg hcol]
        using hgl1

  have hBirthPhysIff :
      (l0.dist.val = tokenD' psi kind ∧
        tokenAt kind l0 = none) ↔ hb := by
    dsimp only [hb]
    have hdistVal :=
      congrArg Fin.val hL0dist
    constructor
    · intro h
      exact
        And.intro
          (hdistVal.symm.trans h.1)
          (hL0.symm.trans h.2)
    · intro h
      exact
        And.intro
          (hdistVal.trans h.1)
          (hL0.trans h.2)

  have hCollPhysIff :
      (tokenAt kind l1 ≠ none ∧
        tokenAt kind r0 ≠ none) ↔ collide := by
    dsimp only [collide]
    constructor
    · intro h
      constructor
      · intro hv
        apply h.1
        exact hL1.trans hv
      · intro hv
        apply h.2
        exact hR0.trans hv
    · intro h
      constructor
      · intro hv
        apply h.1
        exact hL1.symm.trans hv
      · intro hv
        apply h.2
        exact hR0.symm.trans hv

  have hphysBirth :
      hb ->
      leftMirrorMoveToken hpsi kind l r =
        leftMirrorPhysicalFinish
          hpsi kind l2 r0 := by
    intro hbirth
    have hbirth0 :=
      hBirthPhysIff.mpr hbirth
    by_cases hcol : collide
    · have hcol0 :=
        hCollPhysIff.mpr hcol
      simp only
        [l1, l0, r0, birth,
          leftMirrorBirthGhost,
          if_pos hbirth] at hcol0
      unfold leftMirrorMoveToken
        leftMirrorPhysicalFinish
        leftMirrorOneResponder
      rw [dif_pos hgate0, if_pos hbirth0]
      rw [hL0id]
      simp only [if_pos hcol0]
      simp only
        [l2, l1,
          if_pos hcol, if_pos hbirth]
      rfl
    · have hcol0 :
          ¬ (tokenAt kind l1 ≠ none ∧
            tokenAt kind r0 ≠ none) := by
        intro h
        exact hcol (hCollPhysIff.mp h)
      simp only
        [l1, l0, r0, birth,
          leftMirrorBirthGhost,
          if_pos hbirth] at hcol0
      unfold leftMirrorMoveToken
        leftMirrorPhysicalFinish
        leftMirrorOneResponder
      rw [dif_pos hgate0, if_pos hbirth0]
      rw [hL0id]
      simp only [if_neg hcol0]
      simp only
        [l2, l1,
          if_neg hcol, if_pos hbirth]
      rfl

  have hphysNoBirth :
      ¬ hb ->
      leftMirrorMoveToken hpsi kind l r =
        leftMirrorPhysicalFinish
          hpsi kind l2 r0 := by
    intro hbirth
    have hbirth0 :
        ¬ (l0.dist.val = tokenD' psi kind ∧
          tokenAt kind l0 = none) := by
      intro h
      exact hbirth (hBirthPhysIff.mp h)
    by_cases hcol : collide
    · have hcol0 :=
        hCollPhysIff.mpr hcol
      simp only
        [l1, l0, r0,
          if_neg hbirth] at hcol0
      unfold leftMirrorMoveToken
        leftMirrorPhysicalFinish
        leftMirrorOneResponder
      rw [dif_pos hgate0, if_neg hbirth0]
      simp only [if_pos hcol0]
      simp only
        [l2, l1,
          if_pos hcol, if_neg hbirth]
      rfl
    · have hcol0 :
          ¬ (tokenAt kind l1 ≠ none ∧
            tokenAt kind r0 ≠ none) := by
        intro h
        exact hcol (hCollPhysIff.mp h)
      simp only
        [l1, l0, r0,
          if_neg hbirth] at hcol0
      unfold leftMirrorMoveToken
        leftMirrorPhysicalFinish
        leftMirrorOneResponder
      rw [dif_pos hgate0, if_neg hbirth0]
      simp only [if_neg hcol0]
      simp only
        [l2, l1,
          if_neg hcol, if_neg hbirth]
      rfl

  have hphys :
      leftMirrorMoveToken hpsi kind l r =
        leftMirrorPhysicalFinish
          hpsi kind l2 r0 := by
    by_cases hbirth : hb
    · exact hphysBirth hbirth
    · exact hphysNoBirth hbirth

  have hmove :
      moveToken hpsi kind l r =
        leftMirrorPhysicalFinish
          hpsi kind l2 r0 := by
    exact
      (leftMirrorMoveToken_eq
        hpsi kind l r).symm.trans hphys

  have hghost :
      leftMirrorGhostMoveToken
          hpsi kind step e
          l r gl (some z) =
        leftMirrorGhostFinish
          hpsi kind l r
          lv2 rv0 gl2 gr0 := by
    unfold leftMirrorGhostMoveToken
      leftMirrorGhostFinish
    rw [dif_pos hgate]
    rfl

  have hfinish :=
    leftMirrorFinish_dispatch
      hpsi ring e kind
      l r l2 r0
      lv2 rv0 gl2 gr0 z
      hL2 hR0 hgl2 hgr0 hL2id

  intro z'
  have hf := hfinish z'
  constructor
  · intro hpost hid
    rw [hghost] at hpost
    have hs := hf.1 hpost hid
    unfold LeftMirrorRightFinishConclusion at hs
    refine And.intro hs.1 ?_
    rw [hmove]
    exact hs.2
  · intro hpost hid
    rw [hghost] at hpost
    have hs := hf.2 hpost hid
    unfold LeftMirrorLeftFinishConclusion at hs
    rw [hmove]
    exact hs

private theorem leftMirrorSelectedMirrorRow_closed
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft :
      forall zl : GhostToken n psi,
        gl = some zl ->
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (hgate :
      ¬ (l.last = false ∧ r.last = false)) :
    forall z' : GhostToken n psi,
      And
        ((leftMirrorGhostMoveToken
              hpsi kind step e
              l r gl (some z)).right =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          And
            (z' = z)
            (tokenAt kind
                (moveToken hpsi kind l r).2 =
              some z.value))
        ((leftMirrorGhostMoveToken
              hpsi kind step e
              l r gl (some z)).left =
            some z' ->
          z'.lmeta.id = z.lmeta.id ->
          Or
            (And
              (tokenAt kind
                  (moveToken hpsi kind l r).1 =
                some z'.value)
              (And
                (decodeOffset psi
                    (tokenCode z.value) < 0)
                (And
                  (decodeOffset psi
                      (tokenCode z'.value) < 0)
                  (And
                    (tokenTargetSite ring e
                        z'.value =
                      tokenTargetSite ring
                        (ring.rightNeighbor e)
                        z.value)
                    (And
                      (tokenBitBool z'.value =
                        tokenBitBool z.value)
                      (tokenCarryBool z'.value =
                        tokenCarryBool z.value)))))) 
            (And
              (decodeOffset psi
                  (tokenCode z.value) = -1)
              (And
                (tokenAt kind
                    (moveToken hpsi kind l r).1 =
                  some z'.value)
                (z'.value =
                  remark2NegTurnValue
                    hpsi l.id z.value)))) := by
  classical

  let l0 := sourceClear kind l
  let r0 := sourceClear kind r
  let lv0 := leftMirrorLiveValue kind l
  let rv0 := leftMirrorLiveValue kind r
  let gl0 := leftMirrorLiveShadow kind l gl
  let gr0 := leftMirrorLiveShadow kind r (some z)

  have hL0 :
      tokenAt kind l0 = lv0 := by
    simpa only [l0, lv0]
      using leftMirrorSourceClear_token kind l
  have hR0 :
      tokenAt kind r0 = rv0 := by
    simpa only [r0, rv0]
      using leftMirrorSourceClear_token kind r

  have hL0fields :=
    leftMirrorSourceClear_fields kind l
  have hR0fields :=
    leftMirrorSourceClear_fields kind r

  have hL0last : l0.last = l.last := by
    simpa only [l0] using hL0fields.2.1
  have hR0last : r0.last = r.last := by
    simpa only [r0] using hR0fields.2.1

  have hgate0 :
      ¬ (l0.last = false ∧
        r0.last = false) := by
    intro h
    apply hgate
    exact
      And.intro
        (hL0last.symm.trans h.1)
        (hR0last.symm.trans h.2)

  have hNoInput : LeftMirrorNoId z gl := by
    intro u hu hid
    exact hNoLeft u hu hid

  have hgl0 : LeftMirrorNoId z gl0 := by
    simpa only [gl0]
      using
        leftMirrorLiveShadow_noId
          kind l gl z hNoInput

  have hgr0 :
      LeftMirrorTrackedSource z rv0 gr0 := by
    simpa only [rv0, gr0]
      using
        leftMirrorLiveShadow_tracked
          kind r z

  have hmoveLocal :
      leftMirrorMoveToken hpsi kind l r =
        (l0, r0) := by
    unfold leftMirrorMoveToken
    rw [dif_neg hgate0]
    try rfl

  have hmove :
      moveToken hpsi kind l r =
        (l0, r0) := by
    exact
      (leftMirrorMoveToken_eq
        hpsi kind l r).symm.trans hmoveLocal

  have hghost :
      leftMirrorGhostMoveToken
          hpsi kind step e
          l r gl (some z) =
        ⟨gl0, gr0, []⟩ := by
    unfold leftMirrorGhostMoveToken
    rw [dif_neg hgate]
    try rfl

  intro z'
  constructor
  · intro hpost hid
    rw [hghost] at hpost
    change gr0 = some z' at hpost
    have hs :=
      hgr0 z' hpost hid
    refine And.intro hs.1 ?_
    rw [hmove]
    exact hR0.trans hs.2
  · intro hpost hid
    rw [hghost] at hpost
    change gl0 = some z' at hpost
    exact False.elim (hgl0 z' hpost hid)

private theorem leftMirrorSelectedMirrorRow_pair_local
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft :
      forall zl : GhostToken n psi,
        gl = some zl ->
        zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh :
      z.lmeta.id ≠ .born kind step)
    (z' : GhostToken n psi) :
    And
      ((leftMirrorGhostMoveToken
            hpsi kind step e
            l r gl (some z)).right =
          some z' ->
        z'.lmeta.id = z.lmeta.id ->
        And
          (z' = z)
          (tokenAt kind
              (moveToken hpsi kind l r).2 =
            some z.value))
      ((leftMirrorGhostMoveToken
            hpsi kind step e
            l r gl (some z)).left =
          some z' ->
        z'.lmeta.id = z.lmeta.id ->
        Or
          (And
            (tokenAt kind
                (moveToken hpsi kind l r).1 =
              some z'.value)
            (And
              (decodeOffset psi
                  (tokenCode z.value) < 0)
              (And
                (decodeOffset psi
                    (tokenCode z'.value) < 0)
                (And
                  (tokenTargetSite ring e
                      z'.value =
                    tokenTargetSite ring
                      (ring.rightNeighbor e)
                      z.value)
                  (And
                    (tokenBitBool z'.value =
                      tokenBitBool z.value)
                    (tokenCarryBool z'.value =
                      tokenCarryBool z.value)))))) 
          (And
            (decodeOffset psi
                (tokenCode z.value) = -1)
            (And
              (tokenAt kind
                  (moveToken hpsi kind l r).1 =
                some z'.value)
              (z'.value =
                remark2NegTurnValue
                  hpsi l.id z.value)))) := by
  by_cases hgate :
      l.last = false ∧ r.last = false
  · exact
      leftMirrorSelectedMirrorRow_open
        hpsi ring step e kind
        l r gl z hNoLeft hNotFresh
        hgate z'
  · exact
      leftMirrorSelectedMirrorRow_closed
        hpsi ring step e kind
        l r gl z hNoLeft hNotFresh
        hgate z'

private theorem leftMirrorSelectedMirrorRow_right_local
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft : forall (zl : GhostToken n psi),
      gl = some zl -> zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh : z.lmeta.id ≠ .born kind step)
    (z' : GhostToken n psi)
    (hpost : (leftMirrorGhostMoveToken
      hpsi kind step e l r gl (some z)).right = some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    And
      (z' = z)
      (tokenAt kind
        (moveToken hpsi kind l r).2 =
          some z.value) := by
  exact
    (leftMirrorSelectedMirrorRow_pair_local
      hpsi ring step e kind
      l r gl z hNoLeft hNotFresh z').1
      hpost hid

private theorem leftMirrorSelectedMirrorRow_left_local
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (e : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (gl : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hNoLeft : forall (zl : GhostToken n psi),
      gl = some zl -> zl.lmeta.id ≠ z.lmeta.id)
    (hNotFresh : z.lmeta.id ≠ .born kind step)
    (z' : GhostToken n psi)
    (hpost : (leftMirrorGhostMoveToken
      hpsi kind step e l r gl (some z)).left = some z')
    (hid : z'.lmeta.id = z.lmeta.id) :
    Or
      (And
        (tokenAt kind
            (moveToken hpsi kind l r).1 =
          some z'.value)
        (And
          (decodeOffset psi (tokenCode z.value) < 0)
          (And
            (decodeOffset psi (tokenCode z'.value) < 0)
            (And
              (tokenTargetSite ring e z'.value =
                tokenTargetSite ring
                  (ring.rightNeighbor e) z.value)
              (And
                (tokenBitBool z'.value =
                  tokenBitBool z.value)
                (tokenCarryBool z'.value =
                  tokenCarryBool z.value)))))) 
      (And
        (decodeOffset psi (tokenCode z.value) = -1)
        (And
          (tokenAt kind
              (moveToken hpsi kind l r).1 =
            some z'.value)
          (z'.value =
            remark2NegTurnValue
              hpsi l.id z.value))) := by
  exact
    (leftMirrorSelectedMirrorRow_pair_local
      hpsi ring step e kind
      l r gl z hNoLeft hNotFresh z').2
      hpost hid

private theorem leftMirrorSelectedMirrorRow_local :
    LeftMirrorSelectedMirrorRow := by
  classical
  unfold LeftMirrorSelectedMirrorRow
  intro n psi kappa hpsi ring step e kind l r gl z
  intro hNoLeft hNotFresh z'
  constructor
  · intro hpost hid
    exact
      leftMirrorSelectedMirrorRow_right_local
        hpsi ring step e kind
        l r gl z hNoLeft hNotFresh z'
        hpost hid
  · intro hpost hid
    exact
      leftMirrorSelectedMirrorRow_left_local
        hpsi ring step e kind
        l r gl z hNoLeft hNotFresh z'
        hpost hid

theorem remark2LeftSelectedMirrorRow_proved :
    Remark2LeftSelectedMirrorRow := by
  rw [leftMirrorSelectedMirrorRow_defeq]
  exact leftMirrorSelectedMirrorRow_local

theorem remark2LeftSelectedShape_proved :
    Remark2LeftSelectedShape := by
  exact
    remark2LeftSelectedShape_of_mirror
      remark2LeftSelectedMirrorRow_proved

end PPL

#print axioms PPL.remark2LeftSelectedMirrorRow_proved
#print axioms PPL.remark2LeftSelectedShape_proved
