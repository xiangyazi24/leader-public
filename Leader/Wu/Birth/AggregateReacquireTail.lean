import Leader.Wu.Birth.TwoPhaseReacquireHorizon

set_option autoImplicit false
set_option Elab.async false

namespace BirthB4AggregateReacquireTail

open FiniteUniformStoppingTree

variable {S : Type} {A n L : Nat}

/-- Unit indicator for one adaptive trial exit. -/
def hitBit (hit : S -> Fin A -> Bool) (x : S) (e : Fin A) : Nat :=
  if hit x e = true then 1 else 0

/-- Exponential-moment multiplier: one on exit, two on a miss. -/
def missFactor (hit : S -> Fin A -> Bool) (x : S) (e : Fin A) : Nat :=
  if hit x e = true then 1 else 2

/-- Exact one-trial success numerator. -/
def successMass (hit : S -> Fin A -> Bool) (x : S) : Nat :=
  (List.ofFn (fun e : Fin A => hitBit hit x e)).sum

/-- Exact one-trial exponential multiplier numerator. -/
def factorMass (hit : S -> Fin A -> Bool) (x : S) : Nat :=
  (List.ofFn (fun e : Fin A => missFactor hit x e)).sum

private theorem factor_partition
    (hit : S -> Fin A -> Bool) (x : S) :
    factorMass hit x + successMass hit x = 2 * A := by
  unfold factorMass successMass
  rw [<- ofFn_sum_add]
  calc
    (List.ofFn (fun e : Fin A =>
        missFactor hit x e + hitBit hit x e)).sum =
        (List.ofFn (fun _ : Fin A => 2)).sum := by
      apply ofFn_sum_eq
      intro e
      cases h : hit x e <;> simp [missFactor, hitBit, h]
    _ = A * 2 := ofFn_sum_const A 2
    _ = 2 * A := Nat.mul_comm _ _

/-- `1/8` success mass is exactly a `15/8` contraction of the doubled
miss-moment. -/
private theorem factor_eighth
    (hit : S -> Fin A -> Bool) (x : S)
    (hmass : A <= 8 * successMass hit x) :
    8 * factorMass hit x <= 15 * A := by
  have hp := factor_partition hit x
  omega

/-- Carry the current exponential weight as proof-side state. -/
def weightedStep
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (z : S × Nat) (e : Fin A) : S × Nat :=
  (next z.1 e, missFactor hit z.1 e * z.2)

def weightedWeight (z : S × Nat) : Nat := z.2

/-- Exact adaptive `T`-trial moment numerator. -/
def weightedNumerator
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (T : Nat) : Nat :=
  LeaderCountDyadicTail.wordSum
    (weightedStep next hit) weightedWeight (x, 1) T

/-- One-trial conditional mass iterated over an arbitrary adaptive process.
No independence hypothesis occurs: the next one-trial distribution may depend
on the complete current state. -/
private theorem weighted_bound
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (hmass : forall x, A <= 8 * successMass hit x) :
    forall (T : Nat) (z : S × Nat),
      8 ^ T *
          LeaderCountDyadicTail.wordSum
            (weightedStep next hit) weightedWeight z T <=
        15 ^ T * A ^ T * z.2 := by
  intro T
  induction T with
  | zero =>
      intro z
      simp [weightedWeight]
  | succ T ih =>
      intro z
      rw [LeaderCountDyadicTail.wordSum_succ]
      have hsum :
          8 ^ T *
              (List.ofFn (fun e : Fin A =>
                LeaderCountDyadicTail.wordSum
                  (weightedStep next hit) weightedWeight
                  (weightedStep next hit z e) T)).sum <=
            (15 ^ T * A ^ T) *
              (List.ofFn (fun e : Fin A =>
                weightedWeight (weightedStep next hit z e))).sum := by
        calc
          _ = (List.ofFn (fun e : Fin A =>
                8 ^ T * LeaderCountDyadicTail.wordSum
                  (weightedStep next hit) weightedWeight
                  (weightedStep next hit z e) T)).sum := by
              symm
              exact ofFn_sum_mul_left (8 ^ T) _
          _ <= (List.ofFn (fun e : Fin A =>
                (15 ^ T * A ^ T) *
                  weightedWeight (weightedStep next hit z e))).sum := by
              apply ofFn_sum_le
              intro e
              exact ih (weightedStep next hit z e)
          _ = (15 ^ T * A ^ T) *
              (List.ofFn (fun e : Fin A =>
                weightedWeight (weightedStep next hit z e))).sum :=
              ofFn_sum_mul_left (15 ^ T * A ^ T) _
      have hchild :
          (List.ofFn (fun e : Fin A =>
            weightedWeight (weightedStep next hit z e))).sum =
            factorMass hit z.1 * z.2 := by
        calc
          _ = (List.ofFn (fun e : Fin A =>
                missFactor hit z.1 e * z.2)).sum := by rfl
          _ = (List.ofFn (fun e : Fin A =>
                z.2 * missFactor hit z.1 e)).sum := by
              apply ofFn_sum_eq
              intro e
              exact Nat.mul_comm _ _
          _ = z.2 * factorMass hit z.1 := by
              unfold factorMass
              exact ofFn_sum_mul_left z.2 _
          _ = factorMass hit z.1 * z.2 := Nat.mul_comm _ _
      rw [hchild] at hsum
      have hf := factor_eighth hit z.1 (hmass z.1)
      calc
        8 ^ (T + 1) *
            (List.ofFn (fun e : Fin A =>
              LeaderCountDyadicTail.wordSum
                (weightedStep next hit) weightedWeight
                (weightedStep next hit z e) T)).sum =
            8 * (8 ^ T *
              (List.ofFn (fun e : Fin A =>
                LeaderCountDyadicTail.wordSum
                  (weightedStep next hit) weightedWeight
                  (weightedStep next hit z e) T)).sum) := by
              rw [Nat.pow_succ]
              ac_rfl
        _ <= 8 * ((15 ^ T * A ^ T) *
              (factorMass hit z.1 * z.2)) :=
            Nat.mul_le_mul_left 8 hsum
        _ = (15 ^ T * A ^ T * z.2) *
              (8 * factorMass hit z.1) := by ac_rfl
        _ <= (15 ^ T * A ^ T * z.2) * (15 * A) :=
            Nat.mul_le_mul_left (15 ^ T * A ^ T * z.2) hf
        _ = 15 ^ (T + 1) * A ^ (T + 1) * z.2 := by
            rw [Nat.pow_succ, Nat.pow_succ]
            ac_rfl

/-- Public one-trial-to-many induction theorem. -/
theorem adaptiveMomentBound
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (hmass : forall x, A <= 8 * successMass hit x)
    (x : S) (T : Nat) :
    8 ^ T * weightedNumerator next hit x T <=
      15 ^ T * A ^ T := by
  have h := weighted_bound next hit hmass T (x, 1)
  simpa [weightedNumerator] using h

/-- Turn one literal length-`L` raw scheduler word into one macro symbol. -/
def macroNext
    (next : S -> List (Fin n) -> S) (x : S) (i : Fin (n ^ L)) : S :=
  next x (FixedSpanRenewalPayload.rawWord n L i)

def macroHit
    (hit : S -> List (Fin n) -> Bool) (x : S) (i : Fin (n ^ L)) : Bool :=
  hit x (FixedSpanRenewalPayload.rawWord n L i)

theorem macroSuccessMass_eq_wordSum
    (hit : S -> List (Fin n) -> Bool) (x : S) :
    successMass (macroHit (n := n) (L := L) hit) x =
      FixedSpanRenewalPayload.wordSum n L
        (fun u => if hit x u = true then 1 else 0) := by
  unfold successMass hitBit macroHit
  exact FixedSpanRenewalPayload.rawWord_sum n L
    (fun u => if hit x u = true then 1 else 0)

/-- Exact literal-word form of the adaptive moment theorem. -/
theorem literalAdaptiveMomentBound
    (next : S -> List (Fin n) -> S)
    (hit : S -> List (Fin n) -> Bool)
    (hmass : forall x,
      n ^ L <= 8 * FixedSpanRenewalPayload.wordSum n L
        (fun u => if hit x u = true then 1 else 0))
    (x : S) (T : Nat) :
    8 ^ T * weightedNumerator
        (macroNext (n := n) (L := L) next)
        (macroHit (n := n) (L := L) hit) x T <=
      15 ^ T * (n ^ L) ^ T := by
  apply adaptiveMomentBound
  intro y
  rw [macroSuccessMass_eq_wordSum (n := n) (L := L) hit y]
  exact hmass y

/-- Count exits rather than exponential miss weight. -/
def countStep
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (z : S × Nat) (e : Fin A) : S × Nat :=
  (next z.1 e, z.2 + hitBit hit z.1 e)

def badWeight (need : Nat) (z : S × Nat) : Nat :=
  if z.2 < need then 1 else 0

def lowerTailNumerator
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (x : S) (need T : Nat) : Nat :=
  LeaderCountDyadicTail.wordSum
    (countStep next hit) (badWeight need) (x, 0) T

/-- Aggregate number of Reacquire trials. -/
def aggregateTrials (M s : Nat) : Nat :=
  16 * (M + 1 + 8 * s)

theorem aggregateTrials_matches (n kappa : Nat) :
    aggregateTrials
        (BirthB4TwoPhaseComplexity.carrierTrials n kappa)
        (BirthB4TwoPhaseComplexity.carrierLog n) =
      BirthB4TwoPhaseComplexity.aggregateReacquireBlocks n kappa := by
  rfl

theorem aggregateTrials_ge (M s : Nat) :
    M + s <= aggregateTrials M s := by
  unfold aggregateTrials
  omega

/-- One 16-trial group buys strictly more than one dyadic moment bit. -/
theorem sixteenMomentGain :
    2 * 15 ^ 16 <= 16 ^ 16 := by
  decide

/-- Exact remaining aggregate lower-tail theorem.  `lowerTailNumerator` counts
macro words with fewer than `M+1` exits. -/
def AggregateLowerTailStatement
    (next : S -> Fin A -> S) (hit : S -> Fin A -> Bool)
    (M s : Nat) : Prop :=
  (forall x, A <= 8 * successMass hit x) ->
  forall x,
    2 ^ s * lowerTailNumerator next hit x (M + 1)
        (aggregateTrials M s) <=
      A ^ aggregateTrials M s

end BirthB4AggregateReacquireTail

#print axioms BirthB4AggregateReacquireTail.adaptiveMomentBound
#print axioms BirthB4AggregateReacquireTail.macroSuccessMass_eq_wordSum
#print axioms BirthB4AggregateReacquireTail.literalAdaptiveMomentBound
#print axioms BirthB4AggregateReacquireTail.aggregateTrials_matches
#print axioms BirthB4AggregateReacquireTail.aggregateTrials_ge
#print axioms BirthB4AggregateReacquireTail.sixteenMomentGain
