import Leader.L4.WindowA0Route
import Leader.L4.TripleRenewal

/-! Arithmetic and exact first-failure interface for A0. This
uses the already checked variable-duration restart, which improves
the paper's half-block constants without changing its raw labels. -/
namespace L4.WindowA0Restart
open TripleRenewal TaggedTail

def attempts (c : Nat) := 648^(2*c+1)
def attemptCost (c n H : Nat) := 16*(2*c+3)*n*(H+1)
def entryK (c : Nat) := 64+768*(2*c+3)*attempts c
def entryKSharp (c : Nat) := 64+32*(2*c+3)*attempts c

theorem drained_mean {α : Type} {n : Nat} (step : α→Fin n→α)
    (goal drained : α→Prop) (c H : Nat)
    (hTrial : ∀ z, drained z → ¬goal z →
      Nonempty (UniformAttempt step goal drained (attemptCost c n H) (attempts c) z))
    (z : α) (hz : drained z) :
    IIDExpectedHittingTimeAtMost step goal z (attempts c*attemptCost c n H) :=
  expected_of_uniform_attempts step goal drained _ _ (Nat.pow_pos (by decide)) hTrial z hz

theorem half_block_of_attempts {α : Type} {n : Nat} (step : α→Fin n→α)
    (goal drained : α→Prop) (hn : 0<n) (c H : Nat)
    (hTrial : ∀ z, drained z → ¬goal z →
      Nonempty (UniformAttempt step goal drained (attemptCost c n H) (attempts c) z))
    (z : α) (hz : drained z) :
    let B := 4*(3*attempts c)*attemptCost c n H
    2*survival step (fun y => ¬goal y) B z≤n^B := by
  let M := (3*attempts c)*attemptCost c n H
  have h0 : 0<attempts c := Nat.pow_pos (by decide)
  have hA : 0<attemptCost c n H := by unfold attemptCost; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hn) (by omega)
  have hM : 0<M := Nat.mul_pos (Nat.mul_pos (by decide) h0) hA
  have hm : attempts c*attemptCost c n H ≤ M :=
    Nat.mul_le_mul_right _ (by omega)
  have h := quarter_overrun M hM (expected_mono (drained_mean step goal drained c H hTrial z hz) hm)
  dsimp only
  rw [Nat.mul_assoc 4 (3*attempts c)]
  change 2*survival step (fun y => ¬goal y) (4*M) z≤n^(4*M)
  omega

theorem entry_mean {α : Type} {n : Nat} (step : α→Fin n→α)
    (goal drained : α→Prop) (c s H : Nat) (hH : H≤2*s)
    (x : α) (prep : Stage step x)
    (hPrep : IIDExpectedHittingTimeAtMost prep.next prep.ready prep.start (64*n*(s+1)))
    (hReady : ∀ y, prep.reachable y → prep.ready y → ¬goal (prep.project y) →
      drained (prep.project y))
    (hTrial : ∀ z, drained z → ¬goal z →
      Nonempty (UniformAttempt step goal drained (attemptCost c n H) (attempts c) z)) :
    IIDExpectedHittingTimeAtMost step goal x (entryK c*n*(s+1)) := by
  have h := expected_with_preparation prep goal (64*n*(s+1))
    (attempts c*attemptCost c n H) hPrep (fun y hy hr hn =>
      drained_mean step goal drained c H hTrial (prep.project y) (hReady y hy hr hn))
  apply expected_mono h
  calc
    _ ≤ 64*n*(s+1)+attempts c*(16*(2*c+3)*n*(2*(s+1))) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))) _
    _ = entryKSharp c*n*(s+1) := by
      unfold entryKSharp
      rw [Nat.add_mul,Nat.add_mul]
      congr 1
      show attempts c*(16*(2*c+3)*n*(2*(s+1)))=_
      rw [show (32:Nat)=16*2 by decide]
      ac_rfl
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_right
      unfold entryKSharp entryK
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (by decide))) _

#print axioms drained_mean
#print axioms half_block_of_attempts
#print axioms entry_mean
end L4.WindowA0Restart
