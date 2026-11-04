import Leader.Wu.Birth.ResetFreeEntranceMass

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ResetDrainParallel

open FiniteUniformStoppingTree FixedSpanRenewalPayload
open BirthB1ResetFreeEntranceMass BirthB1ResetFreeControlled
  BirthB1ReacquireReentryMass

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- Exact raw-word sum / stopped-tree bridge. -/
private theorem stopped_word_sum {S : Type} {m : Nat}
    (next : S -> Fin m -> StopNode S) (w : StopNode S -> Nat)
    (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum m T
        (fun es => w (ControlledSchedulerMass.runWord next x es)) =
      treeWeight next w x T := by
  induction T generalizing x with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules,
        ControlledSchedulerMass.runWord, treeWeight]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode next x e))

/-- Conservative productive event: the desired fixed service port wins before
 two designated interfering ports.  It is a subset of merely seeing the port. -/
def protectedProductiveBit {n : Nat}
    (p : ThreePortSerialCount.Ports n) (u : List (Fin n)) : Nat :=
  successWeight
    (ControlledSchedulerMass.runWord
      (ThreePortSerialCount.stageStep p) (.active ()) u)

/-- Item 1, one block.  Thus one may take c = 1/4 uniformly. -/
theorem oneResetProductiveBlockMass {n : Nat}
    (p : ThreePortSerialCount.Ports n) (hn : 3 <= n) :
    n ^ (2 * n) <=
      4 * FixedSpanRenewalPayload.wordSum n (2 * n)
        (protectedProductiveBit p) := by
  have hs := stopped_word_sum (ThreePortSerialCount.stageStep p)
    successWeight (.active ()) (2 * n)
  have h := ThreePortSerialCount.single_stage_quarter p hn
  unfold protectedProductiveBit
  rw [hs]
  simpa [successCount] using h

/-- Treat one raw 2n-block as one macro scheduler symbol. -/
def protectedBlockStep {n : Nat} (p : ThreePortSerialCount.Ports n)
    (_ : Unit) (i : Fin (n ^ (2 * n))) : StopNode Unit :=
  if protectedProductiveBit p
      (FixedSpanRenewalPayload.rawWord n (2 * n) i) = 1
  then .success else .active ()

private theorem protectedProductiveBit_cases {n : Nat}
    (p : ThreePortSerialCount.Ports n) (u : List (Fin n)) :
    protectedProductiveBit p u = 0 \/ protectedProductiveBit p u = 1 := by
  unfold protectedProductiveBit
  cases h : ControlledSchedulerMass.runWord
      (ThreePortSerialCount.stageStep p) (.active ()) u <;>
    simp [h, successWeight]

private theorem protectedBlockWeight {n : Nat}
    (p : ThreePortSerialCount.Ports n) (i : Fin (n ^ (2 * n))) :
    successWeight (protectedBlockStep p () i) =
      protectedProductiveBit p
        (FixedSpanRenewalPayload.rawWord n (2 * n) i) := by
  rcases protectedProductiveBit_cases p
      (FixedSpanRenewalPayload.rawWord n (2 * n) i) with h | h <;>
    simp [protectedBlockStep, h, successWeight]

private theorem protectedBlockSuccessCount {n : Nat}
    (p : ThreePortSerialCount.Ports n) :
    successCount (protectedBlockStep p) (.active ()) 1 =
      FixedSpanRenewalPayload.wordSum n (2 * n)
        (protectedProductiveBit p) := by
  unfold successCount
  simp only [treeWeight, stepNode]
  rw [<- FixedSpanRenewalPayload.rawWord_sum n (2 * n)
    (protectedProductiveBit p)]
  exact ofFn_sum_eq _ _ (fun i => protectedBlockWeight p i)

private theorem protectedBlockNoFailure {n : Nat}
    (p : ThreePortSerialCount.Ports n) :
    forall s e, protectedBlockStep p s e ≠ (.failure : StopNode Unit) := by
  intro s e
  by_cases hb : protectedProductiveBit p (rawWord n (2 * n) e) = 1 <;>
    simp [protectedBlockStep, hb]

/-- Item 1, geometric renewal for the next productive stage.
`blocks` macro steps are exactly `blocks` consecutive raw blocks of length 2n. -/
theorem oneResetProductiveBlocksGeometric {n : Nat}
    (p : ThreePortSerialCount.Ports n) (hn : 3 <= n) (blocks : Nat) :
    4 ^ blocks *
        activeCount (protectedBlockStep p) (.active ()) blocks <=
      3 ^ blocks * n ^ ((2 * n) * blocks) := by
  have hblock : forall s : Unit,
      (n ^ (2 * n)) ^ (1 * 1) <=
        4 * successCount (protectedBlockStep p) (.active s) (1 * 1) := by
    intro s
    have hs : s = () := Subsingleton.elim _ _
    subst s
    simp only [Nat.one_mul, Nat.pow_one, protectedBlockSuccessCount]
    exact oneResetProductiveBlockMass p hn
  have ht := UniformBlockRenewal.block_tail
    (step := protectedBlockStep p) (n := n ^ (2 * n))
    (K := 1) (q := 1) (q' := 4) (by decide)
    (protectedBlockNoFailure p) hblock () blocks
  have ht' :
      4 ^ blocks * activeCount (protectedBlockStep p) (.active ()) blocks <=
        3 ^ blocks * (n ^ (2 * n)) ^ blocks := by
    simpa [UniformBlockRenewal.retry] using ht
  calc
    4 ^ blocks * activeCount (protectedBlockStep p) (.active ()) blocks <=
        3 ^ blocks * (n ^ (2 * n)) ^ blocks := ht'
    _ = 3 ^ blocks * n ^ ((2 * n) * blocks) := by
      rw [<- Nat.pow_mul]

/-- At most this many productive stages are charged to one reset. -/
abbrev oneResetProductiveStages (n : Nat) : Nat := 2 * n

/-- Stage/reset union terms: at most n resets, each with at most 2n stages. -/
abbrev resetDrainUnionTerms (n : Nat) : Nat := 2 * n * n

/-- Three quarter-tail blocks buy one dyadic bit of failure exponent. -/
abbrev resetDrainRounds (n power : Nat) : Nat :=
  (power + 3) * (Nat.log2 n + 1)

abbrev resetDrainBlocks (n power : Nat) : Nat :=
  3 * resetDrainRounds n power

/-- 2n stages, K blocks per stage, 2n original letters per block. -/
abbrev resetDrainParallelL (n power : Nat) : Nat :=
  (2 * n) * resetDrainBlocks n power * (2 * n)

/-- Failure means that no physical leader appeared and some reset remains. -/
noncomputable def ResetDrainFailureBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat := by
  classical
  let D := prefixEndpoint hpsi h2 ring C u
  exact if HasPhysicalLeader D \/ resetCount D = 0 then 0 else 1

/-- Item 2.  Exact desired parallel all-reset tail, division-free.
The semantic proof uses the deletion-open one-reset corridor bridge plus a
finite union over at most 2n^2 reset-stage obligations; no independence. -/
def ResetDrainParallelBound
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n) (power : Nat) : Prop :=
  4 <= n -> psi <= n -> forall C : FC n psi kappa tau,
    Leaderless C -> NoActiveDeletionAt C ->
      n ^ power *
          FixedSpanRenewalPayload.wordSum n (resetDrainParallelL n power)
            (ResetDrainFailureBit hpsi h2 ring C) <=
        n ^ resetDrainParallelL n power

/-- Constant-mass version for the controlled entrance: power=1 already gives
reset failure <= 1/n, then compose with the existing denominator 8. -/
abbrev resetFreeControlledParallelL (n : Nat) : Nat :=
  resetDrainParallelL n 1 + resetFreeControlledEntranceL n

abbrev resetFreeControlledParallelQ : Nat := 16

/-- Item 3.  This replaces the old `resetFreeEntranceDrainQ = n^(2n^2)`.
It is stated after deletion cleanup; a deletion-drain prefix is composed before
this Prop rather than charged to tau. -/
def ResetFreeControlledEntranceParallelMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C ->
    NoActiveDeletionAt C ->
      n ^ resetFreeControlledParallelL n <=
        resetFreeControlledParallelQ *
          FixedSpanRenewalPayload.wordSum n
            (resetFreeControlledParallelL n)
            (ResetFreeControlledEntranceSuccessBit
              hpsi h2 hn kappa tau ring anchor Controlled C)

end BirthB1ResetDrainParallel

#print axioms BirthB1ResetDrainParallel.oneResetProductiveBlockMass
#print axioms BirthB1ResetDrainParallel.oneResetProductiveBlocksGeometric
#print axioms BirthB1ResetDrainParallel.ResetDrainParallelBound
#print axioms BirthB1ResetDrainParallel.ResetFreeControlledEntranceParallelMass
