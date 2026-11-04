import Leader.Wu.Birth.ResetDrainParallel
import Leader.Wu.Birth.DeletionRenewalBlock


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB1DrainCoupling


open FiniteUniformStoppingTree FixedSpanRenewalPayload


private theorem stopped_word_sum {X : Type} {B : Nat}
    (step : X -> Fin B -> StopNode X) (w : StopNode X -> Nat)
    (x : StopNode X) (T : Nat) :
    wordSum B T (fun u => w (ControlledSchedulerMass.runWord step x u)) =
      treeWeight step w x T := by
  induction T generalizing x with
  | zero => simp [wordSum, allSchedules, ControlledSchedulerMass.runWord, treeWeight]
  | succ T ih =>
      rw [wordSum_succ]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))


def runBlocks {X : Type} {B : Nat} (next : X -> Fin B -> X) :
    X -> List (Fin B) -> X
  | x, [] => x
  | x, e :: u => runBlocks next (next x e) u


def hitStep {X : Type} {B : Nat}
    (next : X -> Fin B -> X) (hit : X -> Fin B -> Bool)
    (x : X) (e : Fin B) : StopNode X :=
  if hit x e then .success else .active (next x e)


private theorem hitStep_noFailure {X : Type} {B : Nat}
    (next : X -> Fin B -> X) (hit : X -> Fin B -> Bool) :
    forall x e, hitStep next hit x e ≠ (.failure : StopNode X) := by
  intro x e
  unfold hitStep
  split <;> simp


/-- One stage gets exactly `K` physical blocks.  Classification stops at the
first hit, but the payload is the actual endpoint after all `K` blocks. -/
def stageWindow {X : Type} {B : Nat}
    (next : X -> Fin B -> X) (hit : X -> Fin B -> Bool) (K : Nat)
    (x : X) (i : Fin (B ^ K)) : PayloadOutcome X :=
  let u := rawWord B K i
  let y := runBlocks next x u
  match ControlledSchedulerMass.runWord (hitStep next hit) (.active x) u with
  | .active _ => .retry y
  | .success => .success y
  | .failure => .success y


theorem stageWindow_retryMass {X : Type} {B : Nat}
    (next : X -> Fin B -> X) (hit : X -> Fin B -> Bool)
    (K : Nat) (x : X) :
    retryMass (stageWindow next hit K) x =
      activeCount (hitStep next hit) (.active x) K := by
  unfold retryMass activeCount
  rw [<- stopped_word_sum (hitStep next hit) activeWeight (.active x) K]
  rw [<- rawWord_sum]
  apply ofFn_sum_eq
  intro i
  unfold stageWindow
  cases h : ControlledSchedulerMass.runWord (hitStep next hit) (.active x)
      (rawWord B K i) <;>
    simp [retryBit, activeWeight, runBlocks, h]


/-- Conditional `K`-block miss bound; the productive test may depend on every
reached configuration. -/
theorem stageWindow_geometric {X : Type} {B : Nat}
    (next : X -> Fin B -> X) (hit : X -> Fin B -> Bool)
    (hquarter : forall x,
      B <= 4 * successCount (hitStep next hit) (.active x) 1)
    (K : Nat) (x : X) :
    4 ^ K * retryMass (stageWindow next hit K) x <= 3 ^ K * B ^ K := by
  rw [stageWindow_retryMass]
  have ht := UniformBlockRenewal.block_tail
    (step := hitStep next hit) (n := B) (K := 1) (q := 1) (q' := 4)
    (by decide) (hitStep_noFailure next hit)
    (fun y => by simpa using hquarter y) x K
  simpa [UniformBlockRenewal.retry] using ht


/-- Exact number of complete stage-window words whose first unfinished stage
occurs among the allotted stages.  A failed stage has arbitrary suffix words. -/
def badStageCount {X : Type} {M : Nat}
    (window : X -> Fin M -> PayloadOutcome X) : X -> Nat -> Nat
  | _, 0 => 0
  | x, s + 1 =>
      (List.ofFn (fun e : Fin M =>
        match window x e with
        | .success y => badStageCount window y s
        | .retry _ => M ^ s)).sum


/-- Shared adaptive union/coupling lemma.  No stage independence is used. -/
theorem adaptive_stage_union {X : Type} {M Q R : Nat}
    (window : X -> Fin M -> PayloadOutcome X)
    (hrow : forall x, Q * retryMass window x <= R * M)
    (x : X) (stages : Nat) :
    Q * badStageCount window x stages <= stages * R * M ^ stages := by
  induction stages generalizing x with
  | zero => simp [badStageCount]
  | succ s ih =>
      let tail : Fin M -> Nat := fun e =>
        match window x e with
        | .success y => badStageCount window y s
        | .retry _ => 0
      have hsplit : badStageCount window x (Nat.succ s) =
          M ^ s * retryMass window x + (List.ofFn tail).sum := by
        simp only [badStageCount]
        calc
          _ = (List.ofFn (fun e : Fin M =>
              M ^ s * retryBit (window x e) + tail e)).sum := by
            apply ofFn_sum_eq
            intro e
            cases h : window x e <;> simp [tail, h, retryBit]
          _ = _ := by
            unfold retryMass
            rw [ofFn_sum_add, ofFn_sum_mul_left]
      have htailPoint : forall e : Fin M,
          Q * tail e <= s * R * M ^ s := by
        intro e
        cases h : window x e with
        | success y => simpa [tail, h] using ih y
        | retry y => simp [tail, h]
      have htail : Q * (List.ofFn tail).sum <=
          M * (s * R * M ^ s) := by
        calc
          _ = (List.ofFn (fun e : Fin M => Q * tail e)).sum :=
            (ofFn_sum_mul_left Q tail).symm
          _ <= (List.ofFn (fun _ : Fin M => s * R * M ^ s)).sum :=
            ofFn_sum_le _ _ htailPoint
          _ = M * (s * R * M ^ s) := ofFn_sum_const M _
      have hr : Q * (M ^ s * retryMass window x) <= M ^ s * (R * M) := by
        calc
          _ = M ^ s * (Q * retryMass window x) := by ac_rfl
          _ <= M ^ s * (R * M) := Nat.mul_le_mul_left _ (hrow x)
      calc
        Q * badStageCount window x (Nat.succ s) =
            Q * (M ^ s * retryMass window x) + Q * (List.ofFn tail).sum := by
          rw [hsplit, Nat.mul_add]
        _ <= M ^ s * (R * M) + M * (s * R * M ^ s) :=
          Nat.add_le_add hr htail
        _ = Nat.succ s * R * M ^ Nat.succ s := by
          simp only [Nat.succ_eq_add_one, Nat.pow_succ, Nat.add_mul, Nat.one_mul]
          ac_rfl


/-- `S` adaptive stages, `K` blocks each, under a pointwise quarter bound. -/
theorem adaptive_quarter_coupling {X : Type} {B : Nat}
    (next : X -> Fin B -> X) (hit : X -> Fin B -> Bool)
    (hquarter : forall x,
      B <= 4 * successCount (hitStep next hit) (.active x) 1)
    (x : X) (stages K : Nat) :
    4 ^ K * badStageCount (stageWindow next hit K) x stages <=
      stages * 3 ^ K * (B ^ K) ^ stages := by
  exact adaptive_stage_union (stageWindow next hit K)
    (fun y => stageWindow_geometric next hit hquarter K y) x stages


/-- Semantic adapter from the existing three-port scheduler certificate to one
actual physical `2n`-block transition. -/
structure PortBlockAdapter (X : Type) (n : Nat) where
  next : X -> Fin (n ^ (2 * n)) -> X
  hit : X -> Fin (n ^ (2 * n)) -> Bool
  ports : X -> ThreePortSerialCount.Ports n
  protected_hit : forall x i,
    BirthB1ResetDrainParallel.protectedProductiveBit (ports x)
        (rawWord n (2 * n) i) = 1 -> hit x i = true


theorem portBlock_quarter {X : Type} {n : Nat}
    (A : PortBlockAdapter X n) (hn : 3 <= n) (x : X) :
    n ^ (2 * n) <=
      4 * successCount (hitStep A.next A.hit) (.active x) 1 := by
  have hm := BirthB1ResetDrainParallel.oneResetProductiveBlockMass
    (A.ports x) hn
  have hdom : wordSum n (2 * n)
        (BirthB1ResetDrainParallel.protectedProductiveBit (A.ports x)) <=
      successCount (hitStep A.next A.hit) (.active x) 1 := by
    rw [<- rawWord_sum]
    unfold successCount
    simp only [treeWeight, stepNode]
    apply ofFn_sum_le
    intro i
    unfold BirthB1ResetDrainParallel.protectedProductiveBit
    cases hr : ControlledSchedulerMass.runWord
        (ThreePortSerialCount.stageStep (A.ports x)) (.active ())
        (rawWord n (2 * n) i) with
    | active y => simp [hr, successWeight]
    | failure => simp [hr, successWeight]
    | success =>
        have hh : A.hit x i = true := A.protected_hit x i (by
          simp [BirthB1ResetDrainParallel.protectedProductiveBit,
            hr, successWeight])
        simp [hitStep, hh, hr, successWeight]
  exact Nat.le_trans hm (Nat.mul_le_mul_left 4 hdom)


/-- Requested raw-length form: denominator is exactly `n^(S*K*(2n))`. -/
theorem adaptive_productive_port_coupling {X : Type} {n : Nat}
    (A : PortBlockAdapter X n) (hn : 3 <= n)
    (x : X) (stages K : Nat) :
    4 ^ K * badStageCount (stageWindow A.next A.hit K) x stages <=
      stages * 3 ^ K * n ^ (stages * K * (2 * n)) := by
  have h := adaptive_quarter_coupling A.next A.hit
    (fun y => portBlock_quarter A hn y) x stages K
  have hp : ((n ^ (2 * n)) ^ K) ^ stages =
      n ^ (stages * K * (2 * n)) := by
    rw [<- Nat.pow_mul, <- Nat.pow_mul]
    apply congrArg (fun e : Nat => n ^ e)
    ac_rfl
  rw [hp] at h
  exact h


end BirthB1DrainCoupling


#print axioms BirthB1DrainCoupling.stageWindow_retryMass
#print axioms BirthB1DrainCoupling.stageWindow_geometric
#print axioms BirthB1DrainCoupling.adaptive_stage_union
#print axioms BirthB1DrainCoupling.adaptive_productive_port_coupling
