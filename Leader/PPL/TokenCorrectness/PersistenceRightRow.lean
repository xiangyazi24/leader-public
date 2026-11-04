import Leader.PPL.TokenCorrectness.PersistencePairRow

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Remark 2: right selected-colour row

Truth audit at main 5c9651ff:

`Remark2RightSelectedRow` is TRUE as written.

For a tracked owner initially at the initiator `e`, the literal selected-
colour Algorithm-3 row has only three relevant survivor shapes.

* If the selected row does not move the tracked occurrence, the same value
  remains at `e`.
* If the old decoded offset is at least two, the tracked occurrence moves to
  `rightNeighbor e`, keeps its bit/carry, and keeps the same target.
* If the old decoded offset is one, the tracked occurrence moves to
  `rightNeighbor e`, turns left, keeps its bit/carry, and its new negative
  target has source-relative coordinate
  `oldRel - psi + 1`.

A same-colour collision deletes the left/tracked occurrence.  A same-step
fresh birth cannot alias the tracked lineage because `GhostIdsBefore step G`
is the second component of `GhostIdsUniqueAt step G`.  A pre-existing owner
at the responder cannot alias it either, by `GhostIdsUnique G`.

The paper-level part of the proof is closed below: source-Iota transport,
same-occurrence correctness, and both right-move coordinate cases.  The sole
bounded-round residual is `Remark2RightOwnerRow`: the literal one-interaction
selected-colour ghost/physical row must expose exactly one of the three shapes
above.  It contains no ValidToken, WorkingFor, CorrectToken, or CDLAt premise.
Thus the remaining fact is strictly the Algorithm-3 selected-token row, not
the Remark-2 statement again.
-/

/-! ## Source-Iota transport -/

theorem remark2Right_sourceIota_bit
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa) (seg : Nat)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg)
    (x : Fin psi) :
    (C
        (shiftRight ring
          (sourceStart psi ring root seg) x.val)).id =
      (C'
        (shiftRight ring
          (sourceStart psi ring root seg) x.val)).id := by
  exact congrFun hsrc x

theorem remark2Right_firstZeroAux_source_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa)
    (seg fuel j : Nat)
    (hbound : j + fuel <= psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    firstZeroAux ring C
        (sourceStart psi ring root seg) fuel j =
      firstZeroAux ring C'
        (sourceStart psi ring root seg) fuel j := by
  induction fuel generalizing j with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold firstZeroAux
      have hj : j < psi := by
        omega
      let x : Fin psi := ⟨j, hj⟩
      have hb :=
        remark2Right_sourceIota_bit
          ring root C C' seg hsrc x
      change
        (C
            (shiftRight ring
              (sourceStart psi ring root seg) j)).id =
          (C'
            (shiftRight ring
              (sourceStart psi ring root seg) j)).id
        at hb
      rw [hb]
      split
      · rfl
      · exact
          ih (j := j + 1)
            (by omega)

theorem remark2Right_firstZero_source_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa) (seg : Nat)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    firstZeroBit ring C
        (sourceStart psi ring root seg) =
      firstZeroBit ring C'
        (sourceStart psi ring root seg) := by
  unfold firstZeroBit
  exact
    remark2Right_firstZeroAux_source_congr
      ring root C C' seg psi 0
      (by omega) hsrc

theorem remark2Right_payloadCorrect_source_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa)
    (seg x : Nat) (hx : x < psi)
    (t : TokenData psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    Iff
      (payloadCorrect ring C
        (sourceStart psi ring root seg) x t)
      (payloadCorrect ring C'
        (sourceStart psi ring root seg) x t) := by
  unfold payloadCorrect
  have hj :=
    remark2Right_firstZero_source_congr
      ring root C C' seg hsrc
  let ix : Fin psi := ⟨x, hx⟩
  have hb :=
    remark2Right_sourceIota_bit
      ring root C C' seg hsrc ix
  change
    (C
        (shiftRight ring
          (sourceStart psi ring root seg) x)).id =
      (C'
        (shiftRight ring
          (sourceStart psi ring root seg) x)).id
    at hb
  rw [hj, hb]

theorem remark2Right_payloadCorrect_transport
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa)
    (seg x : Nat) (hx : x < psi)
    (t t' : TokenData psi)
    (hbit :
      tokenBitBool t' = tokenBitBool t)
    (hcarry :
      tokenCarryBool t' = tokenCarryBool t)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg)
    (hpay :
      payloadCorrect ring C
        (sourceStart psi ring root seg) x t) :
    payloadCorrect ring C'
      (sourceStart psi ring root seg) x t' := by
  have hpay' :=
    (remark2Right_payloadCorrect_source_congr
      ring root C C' seg x hx t hsrc).mp hpay
  unfold payloadCorrect at hpay' ⊢
  dsimp only at hpay' ⊢
  rw [hbit, hcarry]
  exact hpay'

/-! ## Correctness from the three right-row survivor shapes -/

theorem remark2Right_correct_same_occurrence
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (i : Fin n) (kind : TokenKind)
    (t : TokenData psi)
    (ht : tokenAt kind (C i) = some t)
    (ht' : tokenAt kind (C' i) = some t)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val) :
    CorrectToken ring root C' i kind seg.val := by
  unfold CorrectToken at hcorr ⊢
  rw [ht] at hcorr
  rw [ht']
  dsimp only at hcorr ⊢
  rcases hcorr with ⟨hparity, hrest⟩
  refine And.intro hparity ?_
  by_cases hpos :
      0 < decodeOffset psi (tokenCode t)
  · rw [if_pos hpos] at hrest ⊢
    rcases hrest with
      ⟨hrel, hx, hpay⟩
    exact
      And.intro hrel
        (And.intro hx
          ((remark2Right_payloadCorrect_source_congr
            ring root C C' seg.val
            _ hx t hsrc).mp hpay))
  · rw [if_neg hpos] at hrest ⊢
    rcases hrest with
      ⟨hneg, hrel, hx, hpay⟩
    exact
      And.intro hneg
        (And.intro hrel
          (And.intro hx
            ((remark2Right_payloadCorrect_source_congr
              ring root C C' seg.val
              _ hx t hsrc).mp hpay)))

/--
Data needed after a genuine initiator-to-responder survivor.

The first two fields say Algorithm 3 kept token bit and carry.  The last field
is either an ordinary positive move with unchanged target, or the c=1 turn
with the exact source-relative target shift.
-/
def Remark2RightMotionData
    {n psi : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (seg : Nat) (e j : Fin n)
    (t t' : TokenData psi) : Prop :=
  And
    (tokenBitBool t' = tokenBitBool t)
    (And
      (tokenCarryBool t' = tokenCarryBool t)
      (Or
        (And
          (0 < decodeOffset psi (tokenCode t))
          (And
            (0 < decodeOffset psi (tokenCode t'))
            (cyclicOffset ring
                (sourceStart psi ring root seg)
                (tokenTargetSite ring j t') =
              cyclicOffset ring
                (sourceStart psi ring root seg)
                (tokenTargetSite ring e t))))
        (And
          (decodeOffset psi (tokenCode t) = (1 : Int))
          (And
            (decodeOffset psi (tokenCode t') < 0)
            (cyclicOffset ring
                (sourceStart psi ring root seg)
                (tokenTargetSite ring j t') =
              cyclicOffset ring
                  (sourceStart psi ring root seg)
                  (tokenTargetSite ring e t) -
                psi + 1)))))

theorem remark2Right_motion_preserves_correct
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (e j : Fin n) (kind : TokenKind)
    (t t' : TokenData psi)
    (ht : tokenAt kind (C e) = some t)
    (ht' : tokenAt kind (C' j) = some t')
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hcorr :
      CorrectToken ring root C e kind seg.val)
    (hdata :
      Remark2RightMotionData
        ring root seg.val e j t t') :
    CorrectToken ring root C' j kind seg.val := by
  rcases hdata with
    ⟨hbit, hcarry, hordinary | hturn⟩
  · rcases hordinary with
      ⟨holdPos, hnewPos, hrelEq⟩
    unfold CorrectToken at hcorr ⊢
    rw [ht] at hcorr
    rw [ht']
    dsimp only at hcorr ⊢
    rcases hcorr with ⟨hparity, hrest⟩
    refine And.intro hparity ?_
    rw [if_pos holdPos] at hrest
    rw [if_pos hnewPos]
    rcases hrest with
      ⟨hrel, hx, hpay⟩
    unfold sourceStart at hrelEq
    rw [hrelEq]
    exact
      And.intro hrel
        (And.intro hx
          (remark2Right_payloadCorrect_transport
            ring root C C' seg.val
            (cyclicOffset ring
                (sourceStart psi ring root seg.val)
                (tokenTargetSite ring e t) - psi)
            hx t t' hbit hcarry hsrc hpay))
  · rcases hturn with
      ⟨holdOne, hnewNeg, hrelEq⟩
    have holdPos :
        0 < decodeOffset psi (tokenCode t) := by
      rw [holdOne]
      omega
    have hnewNotPos :
        ¬ 0 < decodeOffset psi (tokenCode t') := by
      omega
    unfold CorrectToken at hcorr ⊢
    rw [ht] at hcorr
    rw [ht']
    dsimp only at hcorr ⊢
    rcases hcorr with ⟨hparity, hrest⟩
    refine And.intro hparity ?_
    rw [if_pos holdPos] at hrest
    rw [if_neg hnewNotPos]
    rcases hrest with
      ⟨hrel, hx, hpay⟩
    refine And.intro hnewNeg ?_
    have hnewRel :
        1 <=
          cyclicOffset ring
            (sourceStart psi ring root seg.val)
            (tokenTargetSite ring j t') := by
      omega
    refine And.intro hnewRel ?_
    have hy :
        cyclicOffset ring
              (sourceStart psi ring root seg.val)
              (tokenTargetSite ring j t') -
            1 =
          cyclicOffset ring
              (sourceStart psi ring root seg.val)
              (tokenTargetSite ring e t) -
            psi := by
      omega
    unfold sourceStart at hy
    refine And.intro ?_ ?_
    · rw [hy]
      exact hx
    · rw [hy]
      exact
        remark2Right_payloadCorrect_transport
          ring root C C' seg.val
          (cyclicOffset ring
              (sourceStart psi ring root seg.val)
              (tokenTargetSite ring e t) - psi)
          hx t t' hbit hcarry hsrc hpay

/-! ## Two lineage facts used by the literal row audit -/

theorem remark2Right_rightNeighbor_ne_self
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) :
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

theorem remark2Right_tracked_ne_sameStepBirth
    {n psi kappa : Nat}
    (step : Nat) (G : GhostConfig n psi kappa)
    (kind : TokenKind) (e : Fin n)
    (z : GhostToken n psi)
    (huniq : GhostIdsUniqueAt step G)
    (howner :
      ghostTokenAt kind G e = some z) :
    z.lmeta.id ≠ .born kind step := by
  intro hid
  have hs :=
    huniq.2 kind e z kind step howner hid
  omega

theorem remark2Right_no_responder_alias
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa)
    (kind : TokenKind) (e : Fin n)
    (z zr : GhostToken n psi)
    (huniq : GhostIdsUniqueAt step G)
    (howner :
      ghostTokenAt kind G e = some z)
    (hright :
      ghostTokenAt kind G
        (ring.rightNeighbor e) = some zr) :
    zr.lmeta.id ≠ z.lmeta.id := by
  intro hid
  have heq :=
    huniq.1 kind e (ring.rightNeighbor e)
      z zr howner hright hid.symm
  have hne :=
    remark2Right_rightNeighbor_ne_self
      hn3 ring e
  exact hne heq.symm

theorem remark2Right_ghostSound_token
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi)
    (hphys : G.phys = C)
    (hG : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    tokenAt kind (C i) = some z.value := by
  cases kind with
  | black =>
      have hs := hG.1 i z howner
      rw [hphys] at hs
      exact hs.1
  | white =>
      have hs := hG.2 i z howner
      rw [hphys] at hs
      exact hs.1

/-! ## Sole remaining literal selected-colour row -/

/--
The only fact not closed in this bounded round.

It is deliberately below the Remark-2 semantic level.  Its premises contain
only the physical/ghost identification, ghost soundness, lineage uniqueness,
the tracked initiator owner, and a same-ID post owner on the interacted pair.
There is no ValidToken, WorkingFor, CorrectToken, or CDLAt premise.

The conclusion is the literal Algorithm-3 classification:
* stay at e with the identical token value; or
* move to the responder with a live physical token and the target/bit/carry
  relation recorded by Remark2RightMotionData.

The truth audit above shows why collision, responder alias, and same-step birth
cannot add a fourth same-ID survivor shape.
-/
def Remark2RightOwnerRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G e = some z ->
    forall (j : Fin n) (z' : GhostToken n psi),
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z' ->
      z'.lmeta.id = z.lmeta.id ->
      Or (j = e) (j = ring.rightNeighbor e) ->
      Or
        (And (j = e)
          (And (z'.value = z.value)
            (tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa) ring C e) j) =
              some z'.value)))
        (And (j = ring.rightNeighbor e)
          (And
            (tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa) ring C e) j) =
              some z'.value)
            (Remark2RightMotionData
              ring root seg.val e j
              z.value z'.value)))

/-! ## Assembly -/

theorem remark2RightSelectedRow
    (hrow : Remark2RightOwnerRow) :
    Remark2RightSelectedRow := by
  unfold Remark2RightSelectedRow
  intro n psi kappa hpsi hn3
  intro ring root seg step C e G kind z
  intro hphys hG huniq howner
  intro _hvalid _hwork hcorr _hC _hC'
  intro j z' hsrc hpost hid hj

  have htok0 :
      tokenAt kind (C e) = some z.value :=
    remark2Right_ghostSound_token
      C G kind e z hphys hG howner

  have hout :=
    hrow hpsi hn3 ring root seg
      step C e G kind z
      hphys hG huniq howner
      j z' hpost hid hj

  rcases hout with hstay | hmove
  · rcases hstay with
      ⟨hje, hvalue, htok1⟩
    subst j
    rw [hvalue] at htok1
    exact
      remark2Right_correct_same_occurrence
        ring root seg
        C
        (PopulationProtocol.step
          (protocol psi kappa) ring C e)
        e kind z.value
        htok0 htok1 hsrc hcorr
  · rcases hmove with
      ⟨hjr, htok1, hdata⟩
    subst j
    exact
      remark2Right_motion_preserves_correct
        ring root seg
        C
        (PopulationProtocol.step
          (protocol psi kappa) ring C e)
        e (ring.rightNeighbor e)
        kind z.value z'.value
        htok0 htok1 hsrc hcorr hdata

/-- The residual is compatible with the four-placement assembler:
after the left directional row is supplied, no statement needs to change. -/
theorem remark2InteractedPairRow_of_rightOwnerRow
    (hrow : Remark2RightOwnerRow)
    (hLeft : Remark2LeftSelectedRow) :
    Remark2InteractedPairRow := by
  exact
    remark2InteractedPairRow
      (remark2RightSelectedRow hrow) hLeft

end PPL

#print axioms PPL.remark2Right_sourceIota_bit
#print axioms PPL.remark2Right_firstZeroAux_source_congr
#print axioms PPL.remark2Right_firstZero_source_congr
#print axioms PPL.remark2Right_payloadCorrect_source_congr
#print axioms PPL.remark2Right_payloadCorrect_transport
#print axioms PPL.remark2Right_correct_same_occurrence
#print axioms PPL.remark2Right_motion_preserves_correct
#print axioms PPL.remark2Right_rightNeighbor_ne_self
#print axioms PPL.remark2Right_tracked_ne_sameStepBirth
#print axioms PPL.remark2Right_no_responder_alias
#print axioms PPL.remark2Right_ghostSound_token
#print axioms PPL.remark2RightSelectedRow
#print axioms PPL.remark2InteractedPairRow_of_rightOwnerRow
