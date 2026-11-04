import Leader.PPL.Elim.LiteralInterface
import Init.Data.Nat.Log2
import Init.Omega

/-!
# P_PL Lemma 17: C_PB to one leader

The proof is entirely finite-word Nat accounting.

1. LiteralElimExpected gives expected first-hit cost at most C17*n^2.
2. Nat Markov gives a half-miss block of length 2*C17*n^2.
3. Restart is performed on the closed PB subtype, retaining every actual
   block endpoint.
4. K = log2 n + 1 blocks give miss mass at most 2^(-K) < 1/n.
-/

namespace PPL.Convergence.L17

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

def K (n : Nat) : Nat :=
  Nat.log2 n + 1

def l17Block (C17 n : Nat) : Nat :=
  2 * (C17 * n * n)

/-- Frozen R10 horizon H17 = 2*C17*n^2*K. -/
def H17 (C17 n : Nat) : Nat :=
  2 * C17 * n * n * K n

theorem H17_eq_blocks (C17 n : Nat) :
    K n * l17Block C17 n = H17 C17 n := by
  simp only [l17Block, H17]
  simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/--
Exact raw scheduler failure numerator at H17.

Because PB is closed and one-leader is closed inside PB, endpoint miss is the
same event as never having hit one leader on any earlier prefix.
-/
noncomputable def l17FailureCount
    (C17 : Nat) {n : Nat}
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n) : Nat :=
  wordSum
    (PPL.literalElim ring)
    (miss PPL.LiteralL1)
    C
    (H17 C17 n)

/-- Denominator-cleared Lemma 17: failure probability is at most 1/n. -/
def Lemma17WordBound
    (C17 : Nat) {n : Nat}
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n) : Prop :=
  n * l17FailureCount C17 ring C <=
    n ^ H17 C17 n

/--
Frozen Lemma 17 from LiteralElimExpected.

No independent restart premise is used.  Blocks restart from the actual PB
subtype endpoint through repeat_half_block_miss.
-/
theorem lemma17_wordBound
    {C17 : Nat}
    (hExpected : PPL.LiteralElimExpected C17)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (_hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C) :
    Lemma17WordBound C17 ring C := by
  have hn2 : 2 <= n := by
    omega
  by_cases hzero : C17 = 0
  · subst C17
    have hL1 :
        PPL.LiteralL1 C :=
      @PPL.literalElimExpected_zero_implies_L1
        (@hExpected) n psi hn2 ring C hPB
    have hlc : PPL.Elim.leaderCount C = 1 := hL1
    unfold Lemma17WordBound
    simp [
      l17FailureCount,
      H17,
      PPL.LiteralL1,
      hlc,
      K2ArbitraryElimination.FiniteAccounting.miss
    ]
  · have hC17 : 0 < C17 := by
      omega
    let B := l17Block C17 n
    have hblock :
        forall x : PPL.PBState ring,
          True ->
          Not (PPL.literalPBTarget ring x) ->
          2 *
              wordSum
                (PPL.literalPBStep ring)
                (miss (PPL.literalPBTarget ring))
                x B <=
            n ^ B := by
      intro x _ _
      simpa [B, l17Block] using
        (@PPL.literalPB_half_block_of_expected C17
          (@hExpected) hC17 n psi hn2 ring x)
    have hrepeat :=
      PPL.Probability.repeat_half_block_miss
        (PPL.literalPBStep ring)
        (PPL.literalPBTarget ring)
        (fun _ : PPL.PBState ring => True)
        (PPL.literalPBTarget_closed ring)
        (fun _ _ _ => True.intro)
        B hblock
        (⟨C, hPB⟩ : PPL.PBState ring)
        True.intro
        (K n)
    have hmissEq :=
      PPL.literalPB_missWordSum_eq
        ring C hPB (K n * B)
    rw [hmissEq] at hrepeat
    have hH :
        K n * B = H17 C17 n := by
      simpa [B] using
        (H17_eq_blocks C17 n)
    rw [hH] at hrepeat
    have hrepeat' :
        2 ^ K n *
            l17FailureCount C17 ring C <=
          n ^ H17 C17 n := by
      unfold l17FailureCount
      exact hrepeat
    have hn0 : n ≠ 0 := by
      omega
    have hlt :
        n < 2 ^ K n := by
      unfold K
      exact
        (Nat.log2_lt hn0).1 (by omega)
    have hnK :
        n <= 2 ^ K n :=
      Nat.le_of_lt hlt
    unfold Lemma17WordBound
    calc
      n * l17FailureCount C17 ring C <=
          2 ^ K n *
            l17FailureCount C17 ring C :=
        Nat.mul_le_mul_right
          (l17FailureCount C17 ring C) hnK
      _ <= n ^ H17 C17 n :=
        hrepeat'

/--
The proved YSM21 repair specializes Lemma 17 to C17=862592, conditional
only on the two remaining physical producer interfaces.
-/
theorem lemma17_wordBound_of_producers
    (hAttempt :
      PPL.Convergence.LDLocal.ModerateAttemptProducerSpec)
    (hPhysical :
      PPL.Convergence.LDLocal.LongBoundaryPhysicalSpec)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring C) :
    Lemma17WordBound 862592 ring C := by
  exact
    @lemma17_wordBound 862592
      (@PPL.literalElimExpected_of_producers hAttempt hPhysical)
      n psi hn3 hpsi ring C hPB

end PPL.Convergence.L17

#print axioms PPL.Convergence.L17.H17_eq_blocks
#print axioms PPL.Convergence.L17.lemma17_wordBound
#print axioms PPL.Convergence.L17.lemma17_wordBound_of_producers
