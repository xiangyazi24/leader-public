import Leader.PPL.SPLEntry.CompletionFrameAdapter
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.TokenCorrectness.PersistenceRightRow

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/--
Off the interacted pair, the physical state is literally unchanged.
For an already-built pair, ValidToken and WorkingFor therefore pull back
to the pre-state.  CorrectToken then transports forward using the protected
source-Iota equality.
-/
private theorem q20252_offPairCorrect
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e i : Fin n)
    (seg : Fin (l18BlockCount n psi))
    (kind : TokenKind)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root (pprimeStep ring C e) seg.val)
    (hpre :
      (ValidToken kind C i ∧
          WorkingFor ring root C i kind seg.val) →
        CorrectToken ring root C i kind seg.val) :
    (ValidToken kind (pprimeStep ring C e) i ∧
        WorkingFor ring root (pprimeStep ring C e)
          i kind seg.val) →
      CorrectToken ring root (pprimeStep ring C e)
        i kind seg.val := by
  intro hVW
  rcases hVW with ⟨hvalidPost, hworkPost⟩

  have hstate :
      pprimeStep ring C e i = C i :=
    l18Risk2UntouchedFrame ring C e i hie hir

  have hvalidPre :
      ValidToken kind C i := by
    unfold ValidToken at hvalidPost ⊢
    rw [hstate] at hvalidPost
    exact hvalidPost

  have hworkPre :
      WorkingFor ring root C i kind seg.val := by
    unfold WorkingFor at hworkPost ⊢
    rw [hstate] at hworkPost
    exact hworkPost

  have hcorrPre :
      CorrectToken ring root C i kind seg.val :=
    hpre ⟨hvalidPre, hworkPre⟩

  let seg' : Fin (segmentCount n psi - 2) :=
    ⟨seg.val, by simpa [l18BlockCount] using seg.isLt⟩

  cases ht : tokenAt kind (C i) with
  | none =>
      unfold ValidToken at hvalidPre
      simp [ht] at hvalidPre
  | some t =>
      have ht' :
          tokenAt kind ((pprimeStep ring C e) i) =
            some t := by
        rw [hstate, ht]
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg'
          C (pprimeStep ring C e)
          i kind t ht ht'
          (by simpa [seg'] using hsrc)
          (by simpa [seg'] using hcorrPre)

/--
Complete assembly of the requested one-step leaf from exactly two
prime-specific local facts:

* protected established source/segment IDs are framed; and
* at either selected endpoint, every post valid token working for an
  already-built pair is correct.

Everything else, including all off-pair token cases, is discharged here.
-/
theorem l18PrimeStepPreservesBuiltPairPrefix_of_frames
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hIds :
      ∀ seg : Fin (l18BlockCount n psi), seg.val < b →
        sourceIota ring root C seg.val =
            sourceIota ring root (pprimeStep ring C e) seg.val ∧
          rootedSegmentId ring root (pprimeStep ring C e) seg.val =
            rootedSegmentId ring root C seg.val ∧
          rootedSegmentId ring root (pprimeStep ring C e) (seg.val + 1) =
            rootedSegmentId ring root C (seg.val + 1))
    (hSelected :
      ∀ seg : Fin (l18BlockCount n psi), seg.val < b →
        ∀ i : Fin n,
          (i = e ∨ i = ring.rightNeighbor e) →
            (((ValidToken .black (pprimeStep ring C e) i ∧
                  WorkingFor ring root (pprimeStep ring C e)
                    i .black seg.val) →
                CorrectToken ring root (pprimeStep ring C e)
                  i .black seg.val) ∧
              ((ValidToken .white (pprimeStep ring C e) i ∧
                  WorkingFor ring root (pprimeStep ring C e)
                    i .white seg.val) →
                CorrectToken ring root (pprimeStep ring C e)
                  i .white seg.val))) :
    ∀ seg : Fin (l18BlockCount n psi), seg.val < b →
      L18BuildPairOK ring root (pprimeStep ring C e) seg.val := by
  intro seg hseg

  have hpre :
      L18BuildPairOK ring root C seg.val :=
    hPrefix.2.2 seg hseg

  rcases hIds seg hseg with
    ⟨hsrc, hid0, hid1⟩

  refine And.intro ?_ ?_
  · rw [hid1, hid0]
    exact hpre.1
  · intro i
    by_cases hie : i = e
    · exact
        hSelected seg hseg i (Or.inl hie)
    · by_cases hir : i = ring.rightNeighbor e
      · exact
          hSelected seg hseg i (Or.inr hir)
      · refine And.intro ?_ ?_
        · exact
            q20252_offPairCorrect
              ring root C e i seg .black
              hie hir hsrc (hpre.2 i).1
        · exact
            q20252_offPairCorrect
              ring root C e i seg .white
              hie hir hsrc (hpre.2 i).2

/-
Exactly two remaining lemmas.

1. Protected ID/source frame.

theorem l18PrimeStepProtectedEstablishedIds
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    ∀ seg : Fin (l18BlockCount n psi), seg.val < b →
      sourceIota ring root C seg.val =
          sourceIota ring root (pprimeStep ring C e) seg.val ∧
        rootedSegmentId ring root (pprimeStep ring C e) seg.val =
          rootedSegmentId ring root C seg.val ∧
        rootedSegmentId ring root (pprimeStep ring C e) (seg.val + 1) =
          rootedSegmentId ring root C (seg.val + 1)

Why it holds:
the only prime ID write is the forced-Construct c=1 responder write.
A write into S0 is excluded by L18NoRiskyAt, with the wrap edge blocked
by canonical last=true.  A write into protected Sm, 1 ≤ m ≤ b, is made
by a valid token working for pair m-1 < b.  hPrefix supplies both its
CorrectToken fact and the predecessor successor-ID equation, so the payload
equals the current target ID bit and the write is idempotent.  This is the
protected-bit frame, specialized to the landed definitions.

2. Selected-pair established-token correctness.

theorem l18PrimeStepSelectedEstablishedTokens
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    ∀ seg : Fin (l18BlockCount n psi), seg.val < b →
      ∀ i : Fin n,
        (i = e ∨ i = ring.rightNeighbor e) →
          (((ValidToken .black (pprimeStep ring C e) i ∧
                WorkingFor ring root (pprimeStep ring C e)
                  i .black seg.val) →
              CorrectToken ring root (pprimeStep ring C e)
                i .black seg.val) ∧
            ((ValidToken .white (pprimeStep ring C e) i ∧
                WorkingFor ring root (pprimeStep ring C e)
                  i .white seg.val) →
              CorrectToken ring root (pprimeStep ring C e)
                i .white seg.val))

Why it holds:
after the protected source frame above, old same-occurrence survivors use
remark2Right_correct_same_occurrence; right-moving old initiators use the
landed Remark-2 motion transport; negative responder moves preserve target
and payload; the c=-1 turn uses the landed carry theorem; fresh border births
have the literal round-zero payload, exactly as in SPLBlackFreshBirth.
The newly landed L18GappedRiskyInsertedResponder Black/White facts already
supply the prime-specific responder output shapes for the S0/no-risky edge.
What is not exported at c79d5f8a is this general established-pair selected
semantic row.

Once those two lemmas land, the exact requested theorem is:

theorem l18PrimeStepPreservesBuiltPairPrefix_proved
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    ∀ seg : Fin (l18BlockCount n psi), seg.val < b →
      L18BuildPairOK ring root (pprimeStep ring C e) seg.val :=
  l18PrimeStepPreservesBuiltPairPrefix_of_frames
    hn3 hpsi ring root b C e hb hPrefix
    (l18PrimeStepProtectedEstablishedIds
      hn3 hpsi ring root b C e hb hPrefix)
    (l18PrimeStepSelectedEstablishedTokens
      hn3 hpsi ring root b C e hb hPrefix)

and then:

theorem l18PrimeLemma4FrameRow_proved : L18PrimeLemma4FrameRow :=
  l18PrimeLemma4FrameRow_of_builtPairStep
    (fun hn3 hpsi ring root b C e hb h =>
      l18PrimeStepPreservesBuiltPairPrefix_proved
        hn3 hpsi ring root b C e hb h)
-/

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18PrimeStepPreservesBuiltPairPrefix_of_frames
