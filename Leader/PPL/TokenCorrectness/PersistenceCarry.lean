import Leader.PPL.TokenCorrectness.Persistence
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-! ## Literal line-29 payload -/

private def remark2BitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

/-- Exactly Algorithm-3 line 29 for a responder token whose decoded offset
is -1.  The source bit is the initiator identifier read by the literal
moveToken branch. -/
def remark2NegTurnNext {psi : Nat} (hpsi : 2 <= psi)
    (sourceBit : Bool) (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    ((offsetPsiCode psi hpsi, remark2BitToFin (!sourceBit)),
      remark2BitToFin sourceBit)
  else
    ((offsetPsiCode psi hpsi, remark2BitToFin sourceBit),
      (0 : Fin 2))

/-- Exact branch certificate used by the microlemma.  The first conjunct pins
C' to the literal full interaction.  The remaining conjuncts say that the
tracked token is the responder's c=-1 token and that the post-state selected
token at the initiator is exactly the line-29 value. -/
def Remark2NegTurnPerformed
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C C' : Config n psi kappa)
    (e i : Fin n) (kind : TokenKind)
    (t : TokenData psi) : Prop :=
  C' =
      PopulationProtocol.step (protocol psi kappa) ring C e ∧
    i = ring.rightNeighbor e ∧
    tokenAt kind (C i) = some t ∧
    decodeOffset psi (tokenCode t) = (-1 : Int) ∧
    tokenAt kind (C' e) =
      some (remark2NegTurnNext hpsi (C e).id t)

/-! ## TransitionFacts frames used by the Remark-2 branch audit -/

private theorem remark2_moveToken_initiator_id_frame
    {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.id = l.id := by
  have h :=
    congrArg (fun q : State psi kappa => q.id)
      (moveToken_initiator_fields hpsi kind l r)
  cases kind <;>
    simpa [eraseKindToken] using h

private theorem remark2_moveToken_responder_dist_last_frame
    {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) :
    ((moveToken hpsi kind l r).2.dist,
        (moveToken hpsi kind l r).2.last) =
      (r.dist, r.last) := by
  rcases moveToken_responder_fields hpsi kind l r with h | h
  · have h' :=
      congrArg
        (fun q : State psi kappa => (q.dist, q.last)) h
    cases kind <;>
      simpa [eraseKindTokenId, eraseKindToken] using h'
  · have h' :=
      congrArg
        (fun q : State psi kappa => (q.dist, q.last)) h
    cases kind <;>
      simpa [eraseKindTokenId, eraseKindToken, birthFields] using h'

private theorem remark2_moveToken_view4_frame
    {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) :
    PPL.Elim.view4 (moveToken hpsi kind l r).1 =
        PPL.Elim.view4 l ∧
      (PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          PPL.Elim.view4 r ∨
        PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          (⟨true, (2 : Fin 3), true, false⟩ :
            PPL.Elim.Cell4)) := by
  exact moveToken_view4_cases hpsi kind l r

/-! ## Source-Iota transport -/

private theorem carry_sourceIota_bit
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

private theorem carry_firstZeroAux_source_congr
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
        carry_sourceIota_bit
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

private theorem carry_firstZero_source_congr
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
    carry_firstZeroAux_source_congr
      ring root C C' seg psi 0
      (by omega) hsrc

private theorem carry_payloadCorrect_source_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa)
    (seg x : Nat) (hx : x < psi)
    (t : TokenData psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    payloadCorrect ring C
        (sourceStart psi ring root seg) x t ↔
      payloadCorrect ring C'
        (sourceStart psi ring root seg) x t := by
  unfold payloadCorrect
  have hj :=
    carry_firstZero_source_congr
      ring root C C' seg hsrc
  let ix : Fin psi := ⟨x, hx⟩
  have hb :=
    carry_sourceIota_bit
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

/-! ## Cyclic geometry -/

private theorem carry_shiftRight_add
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (a b : Nat) :
    shiftRight ring (shiftRight ring i a) b =
      shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem carry_cyclicOffset_shiftRight_of_lt
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) :
    cyclicOffset ring i (shiftRight ring i d) = d := by
  unfold cyclicOffset
  change
    (((i.val + d) % n + n - i.val) % n) = d
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - i.val = n + d := by
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - i.val = d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]

private theorem carry_shiftRight_cyclicOffset
    {n : Nat} (ring : DirectedRing n)
    (a b : Fin n) :
    shiftRight ring a (cyclicOffset ring a b) = b := by
  apply Fin.ext
  change
    (a.val + ((b.val + n - a.val) % n)) % n = b.val
  by_cases hab : a.val <= b.val
  · have heq :
        b.val + n - a.val =
          n + (b.val - a.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : b.val - a.val < n)]
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

private theorem carry_shiftLeft_one_eq_leftNeighbor
    {n : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n) (i : Fin n) :
    shiftLeft ring i 1 = ring.leftNeighbor i := by
  apply Fin.ext
  simp only [shiftLeft, DirectedRing.leftNeighbor]
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]

private theorem carry_leftNeighbor_rightNeighbor
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq :
        i.val + 1 + n - 1 = n + i.val := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem carry_tokenTargetSite_neg_one
    {n psi : Nat} (ring : DirectedRing n)
    (i : Fin n) (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) = (-1 : Int)) :
    tokenTargetSite ring i t =
      shiftLeft ring i 1 := by
  unfold tokenTargetSite
  rw [hc]
  simp

private theorem carry_sourceRelative_lt_of_inSegment
    {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (psi seg : Nat)
    (i : Fin n)
    (hin : InSegment ring root psi seg i) :
    cyclicOffset ring
        (sourceStart psi ring root seg) i < psi := by
  unfold InSegment at hin
  dsimp only at hin
  let off := cyclicOffset ring root i
  have hoffGe : seg * psi <= off := by
    simpa [off] using hin.1
  have hminLe :
      Nat.min ((seg + 1) * psi) n <=
        (seg + 1) * psi := by
    exact Nat.min_le_left _ _
  have hoffSeg :
      off < (seg + 1) * psi := by
    have hmin :
        off < Nat.min ((seg + 1) * psi) n := by
      simpa [off] using hin.2
    exact Nat.lt_of_lt_of_le hmin hminLe
  have hoffN : off < n := by
    exact
      Nat.lt_of_lt_of_le
        (by simpa [off] using hin.2)
        (Nat.min_le_right _ _)
  have hsegStep :
      (seg + 1) * psi = seg * psi + psi := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hsegStep] at hoffSeg
  let d := off - seg * psi
  have hdPsi : d < psi := by
    dsimp [d]
    omega
  have hdN : d < n := by
    dsimp [d]
    omega
  have hroot :
      shiftRight ring root off = i := by
    simpa [off] using
      carry_shiftRight_cyclicOffset ring root i
  have hadd :
      seg * psi + d = off := by
    dsimp [d]
    omega
  have hsite :
      shiftRight ring
          (sourceStart psi ring root seg) d = i := by
    calc
      shiftRight ring
          (sourceStart psi ring root seg) d =
          shiftRight ring root (seg * psi + d) := by
        simpa [sourceStart] using
          carry_shiftRight_add
            ring root (seg * psi) d
      _ = shiftRight ring root off := by
        rw [hadd]
      _ = i := hroot
  rw [← hsite]
  rw [carry_cyclicOffset_shiftRight_of_lt
    ring (sourceStart psi ring root seg) d hdN]
  exact hdPsi

private theorem carry_interior_pair_fits
    {n psi : Nat} (hpsi : 0 < psi)
    (seg : Fin (segmentCount n psi - 2)) :
    2 * psi < n := by
  have hz : 3 <= segmentCount n psi := by
    have hs := seg.isLt
    omega
  unfold segmentCount at hz
  have hmul :
      3 * psi <= n + psi - 1 :=
    (Nat.le_div_iff_mul_le hpsi).mp hz
  omega

/-! ## firstZeroBit recurrence -/

private theorem carry_firstZeroAux_before_true
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (fuel j x : Nat)
    (hjx : j <= x)
    (hxf : x < j + fuel)
    (hlt :
      x < firstZeroAux ring C start fuel j) :
    (C (shiftRight ring start x)).id = true := by
  induction fuel generalizing j with
  | zero =>
      omega
  | succ fuel ih =>
      cases hb :
          (C (shiftRight ring start j)).id with
      | false =>
          simp [firstZeroAux, hb] at hlt
          omega
      | true =>
          by_cases hxj : x = j
          · subst x
            exact hb
          · have hjx' : j + 1 <= x := by
              omega
            have hxf' :
                x < (j + 1) + fuel := by
              omega
            have hlt' :
                x <
                  firstZeroAux ring C start
                    fuel (j + 1) := by
              simpa [firstZeroAux, hb] using hlt
            exact
              ih (j := j + 1)
                hjx' hxf' hlt'

private theorem carry_firstZeroAux_hit_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (fuel j : Nat)
    (hlt :
      firstZeroAux ring C start fuel j <
        j + fuel) :
    (C
        (shiftRight ring start
          (firstZeroAux ring C start fuel j))).id =
      false := by
  induction fuel generalizing j with
  | zero =>
      simp [firstZeroAux] at hlt
  | succ fuel ih =>
      cases hb :
          (C (shiftRight ring start j)).id with
      | false =>
          have hfirst :
              firstZeroAux ring C start
                  (Nat.succ fuel) j = j := by
            simp [firstZeroAux, hb]
          rw [hfirst]
          exact hb
      | true =>
          have htmp :
              firstZeroAux ring C start
                  fuel (j + 1) <
                j + Nat.succ fuel := by
            simpa [firstZeroAux, hb] using hlt
          have hlt' :
              firstZeroAux ring C start
                  fuel (j + 1) <
                (j + 1) + fuel := by
            omega
          have hih :=
            ih (j := j + 1) hlt'
          simpa [firstZeroAux, hb] using hih

private theorem carry_firstZeroBit_before_true
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) (x : Nat)
    (hxPsi : x < psi)
    (hx :
      x < firstZeroBit ring C start) :
    (C (shiftRight ring start x)).id = true := by
  unfold firstZeroBit at hx
  exact
    carry_firstZeroAux_before_true
      ring C start psi 0 x
      (by omega) (by omega) hx

private theorem carry_firstZeroBit_hit_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (hj :
      firstZeroBit ring C start < psi) :
    (C
        (shiftRight ring start
          (firstZeroBit ring C start))).id =
      false := by
  unfold firstZeroBit at hj ⊢
  exact
    carry_firstZeroAux_hit_false
      ring C start psi 0
      (by omega)

/-! ## Boolean payload recurrence -/

private theorem carry_fin2_eq_one_iff
    (b : Fin 2) :
    b = (1 : Fin 2) ↔ (b.val == 1) = true := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | v
  · simp
  · rcases v with _ | v
    · simp
    · omega

private theorem carry_tokenCarry_eq_one_iff
    {psi : Nat} (t : TokenData psi) :
    t.2 = (1 : Fin 2) ↔
      tokenCarryBool t = true := by
  simpa [tokenCarryBool] using
    carry_fin2_eq_one_iff t.2

private theorem remark2NegTurnNext_bits_of_one
    {psi : Nat} (hpsi : 2 <= psi)
    (sourceBit : Bool) (t : TokenData psi)
    (h : t.2 = (1 : Fin 2)) :
    tokenBitBool
        (remark2NegTurnNext hpsi sourceBit t) =
          !sourceBit ∧
      tokenCarryBool
        (remark2NegTurnNext hpsi sourceBit t) =
          sourceBit := by
  cases sourceBit <;>
    simp [remark2NegTurnNext, h,
      remark2BitToFin, tokenBitBool,
      tokenCarryBool]

private theorem remark2NegTurnNext_bits_of_zero
    {psi : Nat} (hpsi : 2 <= psi)
    (sourceBit : Bool) (t : TokenData psi)
    (h : t.2 ≠ (1 : Fin 2)) :
    tokenBitBool
        (remark2NegTurnNext hpsi sourceBit t) =
          sourceBit ∧
      tokenCarryBool
        (remark2NegTurnNext hpsi sourceBit t) =
          false := by
  cases sourceBit <;>
    simp [remark2NegTurnNext, h,
      remark2BitToFin, tokenBitBool,
      tokenCarryBool]

private theorem remark2_negTurn_payload_step
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (x : Nat) (t : TokenData psi)
    (hxNext : x + 1 < psi)
    (hpay :
      payloadCorrect ring C start x t) :
    payloadCorrect ring C start (x + 1)
      (remark2NegTurnNext hpsi
        (C (shiftRight ring start (x + 1))).id t) := by
  unfold payloadCorrect at hpay ⊢
  dsimp only at hpay ⊢
  have hcarry :
      tokenCarryBool t =
        (if x < firstZeroBit ring C start then
          true else false) :=
    hpay.2
  by_cases hxj : x < firstZeroBit ring C start
  · have hcarryTrue :
        tokenCarryBool t = true := by
      simpa [hxj] using hcarry
    have ht1 : t.2 = (1 : Fin 2) := by
      exact
        (carry_tokenCarry_eq_one_iff t).2
          hcarryTrue
    have hbits :=
      remark2NegTurnNext_bits_of_one
        hpsi
        (C (shiftRight ring start (x + 1))).id
        t ht1
    rw [hbits.1, hbits.2]
    have hxle :
        x + 1 <= firstZeroBit ring C start := by
      omega
    constructor
    · simp [hxle]
    · by_cases hx1j :
        x + 1 < firstZeroBit ring C start
      · have hb :
            (C
              (shiftRight ring start (x + 1))).id =
                true := by
          exact
            carry_firstZeroBit_before_true
              ring C start (x + 1)
              hxNext hx1j
        simp [hx1j, hb]
      · have heq :
            x + 1 = firstZeroBit ring C start := by
          omega
        have hjPsi :
            firstZeroBit ring C start < psi := by
          omega
        have hb0 :=
          carry_firstZeroBit_hit_false
            ring C start hjPsi
        have hb :
            (C
              (shiftRight ring start (x + 1))).id =
                false := by
          simpa [heq] using hb0
        simp [hx1j, hb]
  · have hcarryFalse :
        tokenCarryBool t = false := by
      simpa [hxj] using hcarry
    have htne : t.2 ≠ (1 : Fin 2) := by
      intro ht1
      have htrue :
          tokenCarryBool t = true :=
        (carry_tokenCarry_eq_one_iff t).1 ht1
      rw [hcarryFalse] at htrue
      cases htrue
    have hbits :=
      remark2NegTurnNext_bits_of_zero
        hpsi
        (C (shiftRight ring start (x + 1))).id
        t htne
    rw [hbits.1, hbits.2]
    have hnle :
        ¬ x + 1 <= firstZeroBit ring C start := by
      omega
    have hnlt :
        ¬ x + 1 < firstZeroBit ring C start := by
      omega
    simp [hnle, hnlt]

private theorem remark2NegTurnNext_decode
    {psi : Nat} (hpsi : 2 <= psi)
    (sourceBit : Bool) (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (remark2NegTurnNext hpsi sourceBit t)) =
      ((psi : Nat) : Int) := by
  unfold remark2NegTurnNext tokenCode
  split <;>
    exact decodeOffset_psi psi hpsi

private theorem remark2NegTurnNext_target
    {n psi : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (i : Fin n)
    (sourceBit : Bool) (t : TokenData psi) :
    tokenTargetSite ring i
        (remark2NegTurnNext hpsi sourceBit t) =
      shiftRight ring i psi := by
  unfold tokenTargetSite
  rw [remark2NegTurnNext_decode
    hpsi sourceBit t]
  rw [if_pos (by omega)]
  simp

/-! ## c = -1 turn preserves CorrectToken -/

theorem remark2_negTurn_preserves_correct
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (e i : Fin n) (kind : TokenKind)
    (t : TokenData psi)
    (_hvalid : ValidToken kind C i)
    (hwork :
      WorkingFor ring root C i kind seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val)
    (_hC : CDLAt ring root C)
    (_hC' : CDLAt ring root C')
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hturn :
      Remark2NegTurnPerformed
        hpsi ring C C' e i kind t) :
    CorrectToken ring root C' e kind seg.val := by
  rcases hturn with
    ⟨_hstep, hi, ht, hc, hpost⟩

  have hn2 : 2 <= n := by
    omega

  let source :=
    sourceStart psi ring root seg.val
  let target :=
    tokenTargetSite ring i t
  let rel :=
    cyclicOffset ring source target
  let x := rel - 1

  have htarget : target = e := by
    calc
      target =
          shiftLeft ring i 1 := by
        dsimp [target]
        exact
          carry_tokenTargetSite_neg_one
            ring i t hc
      _ = ring.leftNeighbor i :=
        carry_shiftLeft_one_eq_leftNeighbor
          hn2 ring i
      _ = ring.leftNeighbor
          (ring.rightNeighbor e) := by
        rw [hi]
      _ = e :=
        carry_leftNeighbor_rightNeighbor
          ring e

  have hwork0 :
      0 < segmentCount n psi ∧
        InSegment ring root psi seg.val target := by
    simpa [WorkingFor, ht, hc, target] using hwork
  have hseg :
      InSegment ring root psi seg.val target :=
    hwork0.2

  have hcorr0 := hcorr
  unfold CorrectToken at hcorr0
  rw [ht] at hcorr0
  dsimp only at hcorr0
  rw [hc, if_neg (by omega)] at hcorr0
  obtain ⟨hparity, _, h1, h2, h3⟩ := hcorr0
  have hrelPos : 1 <= rel := by
    simpa only [source, target, rel, x, sourceStart] using h1
  have hxOld : x < psi := by
    simpa only [source, target, rel, x, sourceStart] using h2
  have hpayOld : payloadCorrect ring C source x t := by
    simpa only [source, target, rel, x, sourceStart] using h3

  have hrelLt : rel < psi := by
    have h :=
      carry_sourceRelative_lt_of_inSegment
        ring root psi seg.val target hseg
    simpa [rel, source] using h

  have hxRel : x + 1 = rel := by
    dsimp [x]
    omega
  have hxNext : x + 1 < psi := by
    omega

  have heSource :
      e = shiftRight ring source (x + 1) := by
    have hs :=
      carry_shiftRight_cyclicOffset
        ring source e
    have hre :
        cyclicOffset ring source e = rel := by
      dsimp [rel]
      rw [htarget]
    rw [hre, ← hxRel] at hs
    exact hs.symm

  let next :=
    remark2NegTurnNext hpsi (C e).id t

  have hpayNextC :
      payloadCorrect ring C source (x + 1) next := by
    have hp :=
      remark2_negTurn_payload_step
        hpsi ring C source x t
        hxNext hpayOld
    simpa [next, heSource] using hp

  have hpayNextC' :
      payloadCorrect ring C' source
        (x + 1) next := by
    have hp :=
      (carry_payloadCorrect_source_congr
        ring root C C' seg.val (x + 1)
        hxNext next hsrc).mp
        (by simpa [source] using hpayNextC)
    simpa [source] using hp

  have hfit :
      2 * psi < n :=
    carry_interior_pair_fits
      (by omega) seg

  have htargetNew :
      tokenTargetSite ring e next =
        shiftRight ring source ((x + 1) + psi) := by
    calc
      tokenTargetSite ring e next =
          shiftRight ring e psi := by
        simpa [next] using
          remark2NegTurnNext_target
            hpsi ring e (C e).id t
      _ =
          shiftRight ring
            (shiftRight ring source (x + 1))
            psi := by
        rw [← heSource]
      _ =
          shiftRight ring source
            ((x + 1) + psi) :=
        carry_shiftRight_add
          ring source (x + 1) psi

  have hdlt :
      (x + 1) + psi < n := by
    omega

  have hrelNew :
      cyclicOffset ring source
          (tokenTargetSite ring e next) =
        (x + 1) + psi := by
    rw [htargetNew]
    exact
      carry_cyclicOffset_shiftRight_of_lt
        ring source ((x + 1) + psi) hdlt

  have hcNew :
      decodeOffset psi (tokenCode next) =
        ((psi : Nat) : Int) := by
    simpa [next] using
      remark2NegTurnNext_decode
        hpsi (C e).id t

  have hpostNext :
      tokenAt kind (C' e) = some next := by
    simpa [next] using hpost

  unfold CorrectToken
  rw [hpostNext]
  dsimp only
  rw [hcNew, if_pos (by omega)]
  constructor
  · exact hparity
  · have hrelNew' :
        cyclicOffset ring
            (shiftRight ring root (seg.val * psi))
            (tokenTargetSite ring e next) =
          (x + 1) + psi := by
      simpa only [source, sourceStart] using hrelNew
    rw [hrelNew']
    constructor
    · omega
    · have hy :
          (x + 1 + psi) - psi = x + 1 := by
        omega
      rw [hy]
      exact
        ⟨hxNext, by
          simpa only [source, sourceStart]
            using hpayNextC'⟩

end PPL

#print axioms PPL.remark2_negTurn_preserves_correct

