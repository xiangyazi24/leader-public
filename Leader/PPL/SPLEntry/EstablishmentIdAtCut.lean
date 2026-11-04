import Leader.PPL.SPLEntry.BuiltPairIds
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

@[simp] private theorem q20303SourceSetId
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    (PPL.sourceSet kind q x).id = q.id := by
  rw [l18Risk2SourceSet_eq]
  unfold l18Risk2SetToken
  cases kind <;> rfl

private theorem q20303SourceClearMode
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).mode = q.mode := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv :
          l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

/--
Literal forced-Construct c=1 write.

The hypotheses are exactly the service branch after sourceClear:
the line-13 gate is open, the live initiator occurrence is t, the
same-colour responder slot is empty, and t has decoded offset 1.

Because pprimeMoveToken calls moveToken with responder.mode=false,
Algorithm 3 lines 21--22 assign responder.id := tokenBitBool t.
The subsequent token bounce and restoration of the saved mode do not
change id.
-/
theorem l18PrimePPrimeMoveTokenC1Write
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate :
      And
        ((PPL.sourceClear kind l).last = false)
        ((PPL.sourceClear kind
          { r with mode := false }).last = false))
    (hleft :
      PPL.tokenAt kind
          (PPL.sourceClear kind l) =
        some t)
    (hright :
      PPL.tokenAt kind
          (PPL.sourceClear kind
            { r with mode := false }) =
        none)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int)) :
    (pprimeMoveToken hpsi kind l r).2.id =
      PPL.tokenBitBool t := by
  unfold pprimeMoveToken
  dsimp only
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi kind l { r with mode := false }]
  unfold l18Risk2MoveTokenMirror
  have hrMode :
      (PPL.sourceClear kind
          { r with mode := false }).mode =
        false := by
    rw [q20303SourceClearMode]
  simp
    [hgate, hleft, hright, hc1,
      hrMode, q20303SourceSetId]

/--
At a correct c=1 occurrence for pair b, CorrectToken already contains
the desired add-one payload bit.

This theorem deliberately does NOT assume that the target segment is
already the binary successor.  It is therefore usable for first
establishment, unlike q20256CorrectC1TargetBit, whose final step uses
the already-established successor-ID equation to prove idempotence.
-/
theorem l18PrimeCorrectC1DesiredBit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (b : Nat)
    (kind : TokenKind)
    (t : TokenData psi)
    (ht :
      PPL.tokenAt kind (C e) = some t)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int))
    (hcorr :
      PPL.CorrectToken ring root C e kind b) :
    let source :=
      PPL.shiftRight ring root (b * psi)
    let targetStart :=
      PPL.shiftRight ring root ((b + 1) * psi)
    let rel :=
      PPL.cyclicOffset ring source
        (ring.rightNeighbor e)
    let x := rel - psi
    And
      (x < psi)
      (And
        (ring.rightNeighbor e =
          PPL.shiftRight ring targetStart x)
        (PPL.tokenBitBool t =
          if x <=
              PPL.firstZeroBit ring C source then
            !(C
              (PPL.shiftRight ring source x)).id
          else
            (C
              (PPL.shiftRight ring source x)).id)) := by
  let source :=
    PPL.shiftRight ring root (b * psi)
  let targetStart :=
    PPL.shiftRight ring root ((b + 1) * psi)
  let rel :=
    PPL.cyclicOffset ring source
      (ring.rightNeighbor e)
  let x := rel - psi

  have htarget :
      PPL.tokenTargetSite ring e t =
        ring.rightNeighbor e := by
    unfold PPL.tokenTargetSite
    rw [hc1]
    try simp
    rfl

  have hc := hcorr
  unfold PPL.CorrectToken at hc
  rw [ht] at hc
  dsimp only at hc
  rw [hc1, if_pos (by omega)] at hc
  rcases hc with
    ⟨_hparity, hrel0, hx0, hpay0⟩

  have hrelLower :
      psi <= rel := by
    simpa [source, rel, htarget]
      using hrel0

  have hxLt :
      x < psi := by
    simpa [source, rel, x, htarget]
      using hx0

  have hpay :
      PPL.payloadCorrect ring C source x t := by
    simpa [source, rel, x, htarget]
      using hpay0

  have hmul :
      (b + 1) * psi =
        b * psi + psi := by
    rw [Nat.add_mul, Nat.one_mul]

  have hstart :
      targetStart =
        PPL.shiftRight ring source psi := by
    dsimp only [targetStart, source]
    rw [hmul]
    exact
      (l18Risk2ShiftRight_add
        ring root (b * psi) psi).symm

  have hrelEq :
      psi + x = rel := by
    dsimp only [x]
    omega

  have hsite :
      ring.rightNeighbor e =
        PPL.shiftRight ring targetStart x := by
    calc
      ring.rightNeighbor e =
          PPL.shiftRight ring source rel :=
        (l18Risk2ShiftRight_cyclicOffset
          ring source
          (ring.rightNeighbor e)).symm
      _ =
          PPL.shiftRight ring source
            (psi + x) := by
        rw [hrelEq]
      _ =
          PPL.shiftRight ring
            (PPL.shiftRight ring source psi) x :=
        (l18Risk2ShiftRight_add
          ring source psi x).symm
      _ =
          PPL.shiftRight ring targetStart x := by
        rw [hstart]

  unfold PPL.payloadCorrect at hpay
  dsimp only at hpay

  exact
    And.intro hxLt
      (And.intro hsite hpay.1)

/--
Per-bit service lemma.

Combining the literal prime c=1 branch with CorrectToken says that the
immediate prime responder ID is exactly the x-th binary-add-one bit of
the source word.  No successor-ID hypothesis is used.
-/
theorem l18PrimeCorrectC1ServiceWritesSuccessorBit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (b : Nat)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (ht :
      PPL.tokenAt kind (C e) = some t)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int))
    (hcorr :
      PPL.CorrectToken ring root C e kind b)
    (hgate :
      And
        ((PPL.sourceClear kind l).last = false)
        ((PPL.sourceClear kind
          { r with mode := false }).last = false))
    (hleft :
      PPL.tokenAt kind
          (PPL.sourceClear kind l) =
        some t)
    (hright :
      PPL.tokenAt kind
          (PPL.sourceClear kind
            { r with mode := false }) =
        none) :
    let source :=
      PPL.shiftRight ring root (b * psi)
    let targetStart :=
      PPL.shiftRight ring root ((b + 1) * psi)
    let rel :=
      PPL.cyclicOffset ring source
        (ring.rightNeighbor e)
    let x := rel - psi
    And
      (x < psi)
      (And
        (ring.rightNeighbor e =
          PPL.shiftRight ring targetStart x)
        ((pprimeMoveToken hpsi kind l r).2.id =
          if x <=
              PPL.firstZeroBit ring C source then
            !(C
              (PPL.shiftRight ring source x)).id
          else
            (C
              (PPL.shiftRight ring source x)).id)) := by
  have hsem :=
    l18PrimeCorrectC1DesiredBit
      hpsi ring root C e b kind t
      ht hc1 hcorr

  have hwrite :=
    l18PrimePPrimeMoveTokenC1Write
      hpsi kind l r t
      hgate hleft hright hc1

  dsimp only at hsem ⊢

  exact
    And.intro hsem.1
      (And.intro hsem.2.1
        (hwrite.trans hsem.2.2))

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18PrimePPrimeMoveTokenC1Write
#print axioms
  PPL.Convergence.L18.l18PrimeCorrectC1DesiredBit
#print axioms
  PPL.Convergence.L18.l18PrimeCorrectC1ServiceWritesSuccessorBit
