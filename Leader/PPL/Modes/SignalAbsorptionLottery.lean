import Leader.PPL.Modes.SignalAbsorptionSplit
import Leader.PPL.Probability.MarkedWordTransfer
import Leader.PPL.Probability.LotteryMoment

/-!
# Stopped lottery counting for Lemma 9

The upper event observes exactly the first `E` marks while the stop has not
occurred, so it uses the exact marked-word transfer. The lower event uses its
corresponding exact at-most transfer. The arbitrary initial head offset is
then reduced to a fresh lottery before applying the Lemma 8 binary tail.
-/

namespace PPL.Modes.Lemma9

open PPL.Probability

set_option autoImplicit false
set_option Elab.async false

/-- Both stopped lottery counts transfer to literal binary words. The upper
failure count is an exact-`E` event; no extension property is assumed. -/
theorem modeStoppedTreeTransfer : ModeStoppedTreeTransfer := by
  unfold ModeStoppedTreeTransfer
  constructor
  · intro n k h T E M hn3 _ _ ring host stop
    have ht := stoppedMarkedWordTransfer hn3 ring host stop T E
      (fun bits =>
        decide (M ≤ (lotteryRun k (lotteryOffset h) bits).wins))
    simpa [stoppedLotteryUpperFailureCount, stoppedMarkedExactCount,
      lotteryAtLeastWordCount, lotteryPredWordCount,
      decide_eq_true_eq] using ht
  · intro n k h T E M hn3 _ _ ring host stop
    exact stoppedEncounterLotteryAtMost_transfer
      hn3 k h ring host stop T E M

/-- The stopped lower lottery failure count has probability at most `1/n²`
at Lemma 9's horizon, for every legal initial head offset. -/
theorem lemma9LotteryLowerTail : Lemma9LotteryLowerTail := by
  intro n psi c hn3 hpsi hc hnpow ring host stop h hh
    htransfer hoffset hcount
  let E : Nat := lemma9E psi c
  let T : Nat := lemma9T n psi c
  let M : Nat := lotteryTarget psi c
  let A : Nat :=
    stoppedLotteryLowerFailureCount psi h ring host stop T E M
  let B : Nat := lotteryAtMostWordCount psi h E M
  let B0 : Nat := lotteryAtMostWordCount psi 0 E M
  change n * n * A ≤ n ^ T

  have hbinary : A * 2 ^ E ≤ n ^ T * B := by
    dsimp [A, B]
    exact htransfer.2 hn3 (by omega) hh ring host stop
  have hhead : B ≤ B0 := by
    dsimp [B, B0]
    exact (hoffset psi h E M (by omega) hh).1
  have hL8 : 2 ^ (c * psi) * B0 ≤ 2 ^ E := by
    dsimp [B0, E, M, lemma9E]
    exact (hcount psi c (by omega) (by omega)).2

  have hn2 : n * n ≤ 2 ^ (c * psi) := by
    have ha := Nat.mul_le_mul hnpow hnpow
    have hb : 2 ^ psi * 2 ^ psi = 2 ^ (2 * psi) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have he : 2 * psi ≤ c * psi :=
      Nat.mul_le_mul_right psi (by omega)
    calc
      n * n ≤ 2 ^ psi * 2 ^ psi := ha
      _ = 2 ^ (2 * psi) := hb
      _ ≤ 2 ^ (c * psi) :=
        Nat.pow_le_pow_right (by decide) he

  have hscaled : (2 ^ (c * psi) * A) * 2 ^ E ≤
      n ^ T * 2 ^ E := by
    calc
      (2 ^ (c * psi) * A) * 2 ^ E =
          2 ^ (c * psi) * (A * 2 ^ E) := by ac_rfl
      _ ≤ 2 ^ (c * psi) * (n ^ T * B) :=
        Nat.mul_le_mul_left _ hbinary
      _ = n ^ T * (2 ^ (c * psi) * B) := by ac_rfl
      _ ≤ n ^ T * (2 ^ (c * psi) * B0) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hhead)
      _ ≤ n ^ T * 2 ^ E :=
        Nat.mul_le_mul_left _ hL8
  have htail : 2 ^ (c * psi) * A ≤ n ^ T :=
    Nat.le_of_mul_le_mul_right hscaled
      (Nat.pow_pos (by decide : 0 < 2))
  exact Nat.le_trans (Nat.mul_le_mul_right A hn2) htail

/-- The three counting interfaces are discharged by their proved producers,
leaving only the physical stopped-word parameters as hypotheses. -/
theorem lemma9LotteryLowerTail_closed :
    ∀ {n psi c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 6 ≤ c)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (host : List (Fin n) → Fin n)
      (stop : List (Fin n) → Bool)
      (h : Nat),
      h ≤ psi →
      n * n *
        stoppedLotteryLowerFailureCount
          psi h ring host stop
          (lemma9T n psi c) (lemma9E psi c)
          (lotteryTarget psi c) ≤
        n ^ lemma9T n psi c := by
  intro n psi c hn3 hpsi hc hnpow ring host stop h hh
  exact lemma9LotteryLowerTail hn3 hpsi hc hnpow ring host stop h hh
    modeStoppedTreeTransfer wlgHeadOffsetBounds lotteryCountBounds

#print axioms modeStoppedTreeTransfer
#print axioms lemma9LotteryLowerTail
#print axioms lemma9LotteryLowerTail_closed

end PPL.Modes.Lemma9
