import Leader.Wu.Birth.AggregateReacquireTail

set_option autoImplicit false
set_option Elab.async false

namespace BirthB4AggregateTailFinish

open FiniteUniformStoppingTree
open BirthB4AggregateReacquireTail

variable {S : Type} {A : Nat}

private def runWord {X : Type} {m : Nat}
    (step : X -> Fin m -> X) : X -> List (Fin m) -> X
  | x, [] => x
  | x, e :: u => runWord step (step x e) u

private theorem wordSum_run {X : Type} {m : Nat}
    (step : X -> Fin m -> X) (w : X -> Nat) (x : X) (T : Nat) :
    FixedSpanRenewalPayload.wordSum m T
        (fun u => w (runWord step x u)) =
      LeaderCountDyadicTail.wordSum step w x T := by
  induction T generalizing x with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules, runWord]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ,
        LeaderCountDyadicTail.wordSum_succ]
      apply ofFn_sum_eq
      intro e
      simpa only [runWord] using ih (step x e)

private theorem wordSum_mono_length
    {m T : Nat} (f g : List (Fin m) -> Nat)
    (h : forall u : List (Fin m), u.length = T -> f u <= g u) :
    FixedSpanRenewalPayload.wordSum m T f <=
      FixedSpanRenewalPayload.wordSum m T g := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum m T f,
    <- FixedSpanRenewalPayload.rawWord_sum m T g]
  apply ofFn_sum_le
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length m T i)

private def trialHits
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool) :
    S -> List (Fin A) -> Nat
  | _, [] => 0
  | x, e :: u => hitBit hit x e + trialHits next hit (next x e) u

private def trialMisses
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool) :
    S -> List (Fin A) -> Nat
  | _, [] => 0
  | x, e :: u =>
      (if hit x e = true then 0 else 1) +
        trialMisses next hit (next x e) u

private theorem trial_partition
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (u : List (Fin A)) :
    trialHits next hit x u + trialMisses next hit x u = u.length := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
      have ht := ih (next x e)
      cases h : hit x e <;>
        simp [trialHits, trialMisses, hitBit, h] at * <;> omega

private theorem trialHits_run
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (u : List (Fin A)) (c : Nat) :
    (runWord (countStep next hit) (x, c) u).2 =
      c + trialHits next hit x u := by
  induction u generalizing x c with
  | nil => rfl
  | cons e u ih =>
      change
        (runWord (countStep next hit)
          (next x e, c + hitBit hit x e) u).2 =
        c + (hitBit hit x e + trialHits next hit (next x e) u)
      rw [ih]
      omega

private theorem trialMisses_run
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (u : List (Fin A)) (w : Nat) :
    (runWord (weightedStep next hit) (x, w) u).2 =
      2 ^ trialMisses next hit x u * w := by
  induction u generalizing x w with
  | nil => simp [runWord, trialMisses]
  | cons e u ih =>
      change
        (runWord (weightedStep next hit)
          (next x e, missFactor hit x e * w) u).2 =
        2 ^ ((if hit x e = true then 0 else 1) +
          trialMisses next hit (next x e) u) * w
      rw [ih]
      cases h : hit x e <;>
        simp [missFactor, h, Nat.pow_succ, Nat.mul_assoc] <;>
          first | ac_rfl | (rw [Nat.pow_add, Nat.pow_one]; ac_rfl)

/-- Wordwise bridge: fewer than `M+1` hits forces at least `T-M` misses. -/
theorem badWordMoment
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (M T : Nat) (u : List (Fin A)) (hlen : u.length = T) :
    2 ^ (T - M) * badWeight (M + 1)
        (runWord (countStep next hit) (x, 0) u) <=
      weightedWeight (runWord (weightedStep next hit) (x, 1) u) := by
  unfold badWeight weightedWeight
  rw [trialHits_run next hit x u 0, trialMisses_run next hit x u 1]
  simp only [Nat.zero_add, Nat.mul_one]
  have hp := trial_partition next hit x u
  rw [hlen] at hp
  by_cases hb : trialHits next hit x u < M + 1
  · rw [if_pos hb]
    have hm : trialHits next hit x u <= M := by omega
    have hmiss : T - M <= trialMisses next hit x u := by omega
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hmiss
  · rw [if_neg hb]
    simp

/-- Summed pathwise conversion on the exact macro-word alphabet. -/
theorem lowerTailMoment
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (M T : Nat) :
    2 ^ (T - M) * lowerTailNumerator next hit x (M + 1) T <=
      weightedNumerator next hit x T := by
  unfold lowerTailNumerator weightedNumerator
  let c := 2 ^ (T - M)
  change c * LeaderCountDyadicTail.wordSum
      (countStep next hit) (badWeight (M + 1)) (x, 0) T <= _
  calc
    _ = LeaderCountDyadicTail.wordSum (countStep next hit)
        (fun z => c * badWeight (M + 1) z) (x, 0) T := by
      symm
      exact LeaderCountDyadicTail.wordSum_mul
        (countStep next hit) c (badWeight (M + 1)) (x, 0) T
    _ = FixedSpanRenewalPayload.wordSum A T (fun u =>
        c * badWeight (M + 1)
          (runWord (countStep next hit) (x, 0) u)) :=
      (wordSum_run _ _ _ _).symm
    _ <= FixedSpanRenewalPayload.wordSum A T (fun u =>
        weightedWeight (runWord (weightedStep next hit) (x, 1) u)) := by
      apply wordSum_mono_length
      intro u hu
      simpa [c] using badWordMoment next hit x M T u hu
    _ = LeaderCountDyadicTail.wordSum
        (weightedStep next hit) weightedWeight (x, 1) T :=
      wordSum_run _ _ _ _

/-- At the chosen horizon the moment coefficient pays the requested `2^s`. -/
theorem aggregateCoefficient (M s : Nat) :
    2 ^ s * 15 ^ aggregateTrials M s <=
      8 ^ aggregateTrials M s * 2 ^ (aggregateTrials M s - M) := by
  let G := M + 1 + 8 * s
  have hT : aggregateTrials M s = 16 * G := by simp [aggregateTrials, G]
  rw [hT]
  have hMG : M + s <= G := by dsimp [G]; omega
  have hMT : M <= 16 * G := by dsimp [G]; omega
  have hp := Nat.pow_le_pow_left sixteenMomentGain G
  have hp' : 2 ^ G * 15 ^ (16 * G) <= 16 ^ (16 * G) := by
    simpa only [Nat.mul_pow, <- Nat.pow_mul] using hp
  have h2 : 2 ^ (M + s) <= 2 ^ G :=
    Nat.pow_le_pow_right (by decide) hMG
  have hs : 2 ^ (M + s) * 15 ^ (16 * G) <= 16 ^ (16 * G) :=
    Nat.le_trans (Nat.mul_le_mul_right _ h2) hp'
  have hmul :
      2 ^ M * (2 ^ s * 15 ^ (16 * G)) <=
        2 ^ M * (8 ^ (16 * G) * 2 ^ (16 * G - M)) := by
    calc
      _ = 2 ^ (M + s) * 15 ^ (16 * G) := by rw [Nat.pow_add]; ac_rfl
      _ <= 16 ^ (16 * G) := hs
      _ = 2 ^ M * (8 ^ (16 * G) * 2 ^ (16 * G - M)) := by
        symm
        calc
          _ = 8 ^ (16 * G) * (2 ^ (16 * G - M) * 2 ^ M) := by ac_rfl
          _ = 8 ^ (16 * G) * 2 ^ ((16 * G - M) + M) := by rw [Nat.pow_add]
          _ = 8 ^ (16 * G) * 2 ^ (16 * G) := by rw [Nat.sub_add_cancel hMT]
          _ = (8 * 2) ^ (16 * G) := by rw [Nat.mul_pow]
          _ = 16 ^ (16 * G) := by rfl
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by decide : 0 < 2))

/-- Explicit word-sum lower tail used by the Carrier renewal. -/
theorem aggregateLowerTailBound
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (M s : Nat) (hmass : forall x, A <= 8 * successMass hit x) (x : S) :
    2 ^ s * lowerTailNumerator next hit x (M + 1)
        (aggregateTrials M s) <= A ^ aggregateTrials M s := by
  let T := aggregateTrials M s
  change 2 ^ s * lowerTailNumerator next hit x (M + 1) T <= A ^ T
  have hp := lowerTailMoment next hit x M T
  have hm := adaptiveMomentBound next hit hmass x T
  have hc : 2 ^ s * 15 ^ T <= 8 ^ T * 2 ^ (T - M) := by
    simpa [T] using aggregateCoefficient M s
  have hcombo :
      8 ^ T * (2 ^ (T - M) * lowerTailNumerator next hit x (M + 1) T) <=
        15 ^ T * A ^ T :=
    Nat.le_trans (Nat.mul_le_mul_left (8 ^ T) hp) hm
  have hscaled :
      15 ^ T * (2 ^ s * lowerTailNumerator next hit x (M + 1) T) <=
        15 ^ T * A ^ T := by
    calc
      _ = (2 ^ s * 15 ^ T) * lowerTailNumerator next hit x (M + 1) T := by ac_rfl
      _ <= (8 ^ T * 2 ^ (T - M)) *
          lowerTailNumerator next hit x (M + 1) T :=
        Nat.mul_le_mul_right _ hc
      _ = 8 ^ T * (2 ^ (T - M) *
          lowerTailNumerator next hit x (M + 1) T) := by ac_rfl
      _ <= 15 ^ T * A ^ T := hcombo
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos (by decide : 0 < 15))

/-- The statement from `BirthB4AggregateReacquireTail` closes unchanged. -/
theorem aggregateLowerTail
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (M s : Nat) : AggregateLowerTailStatement next hit M s := by
  unfold AggregateLowerTailStatement
  intro hmass x
  exact aggregateLowerTailBound next hit M s hmass x

end BirthB4AggregateTailFinish

#print axioms BirthB4AggregateTailFinish.badWordMoment
#print axioms BirthB4AggregateTailFinish.lowerTailMoment
#print axioms BirthB4AggregateTailFinish.aggregateCoefficient
#print axioms BirthB4AggregateTailFinish.aggregateLowerTailBound
#print axioms BirthB4AggregateTailFinish.aggregateLowerTail
