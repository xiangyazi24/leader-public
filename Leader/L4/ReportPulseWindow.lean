import Leader.L4.ReportPulseAdapter
import Leader.L4.Height.Trial

namespace L4.ReportPulseWait

/-- The two development namespaces use the same finite IID semantics. -/
theorem same_hit_cost {X : Type} {n : Nat} (step : X→Fin n→X)
    (hit : X→Prop) (t : Nat) (x : X) :
    Height.iidHitCost step hit t x=L4.iidHitCost step hit t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases T : hit x
    · simp [Height.iidHitCost,L4.iidHitCost,T]
    · simp only [Height.iidHitCost,L4.iidHitCost,if_neg T]
      congr 2
      apply congrArg List.ofFn
      funext e
      exact ih _

theorem mean_in_height {X : Type} {n : Nat} {step : X→Fin n→X}
    {hit : X→Prop} {x : X} {B : Nat}
    (H : L4.IIDExpectedHittingTimeAtMost step hit x B) :
    Height.IIDExpectedHittingTimeAtMost step hit x B := by
  intro t
  rw [same_hit_cost]
  exact H t

theorem monitor_true {X : Type} {n : Nat} (raw : X→Fin n→X)
    (paints : X→Fin n→Bool) (x : X×Bool) (e : Fin n) (H : x.2=true) :
    (monitor raw paints x e).2=true := by simp [monitor,H]

/-- Exact original finite-word count of pulse misses. On a word of
length t the sticky final flag remembers any earlier actual hit. -/
theorem miss_count {X : Type} {n : Nat} (raw : X→Fin n→X)
    (paints : X→Fin n→Bool) (x : X) (A t : Nat)
    (H : L4.IIDExpectedHittingTimeAtMost (monitor raw paints) (fun y=>y.2=true)
      (x,false) A) :
    t * Height.wordSum (fun w =>
      if (Height.runWord (monitor raw paints) (x,false) w).2=true then 0 else 1) t ≤
      A*n^t := by
  classical
  let next := monitor raw paints
  let hit := fun y : X×Bool=>y.2=true
  have V := Height.markov_survivors next hit (x,false) A t (mean_in_height H)
  have E : Height.wordSum
      (fun w=>@ite Nat (hit (Height.stoppedRun next hit (x,false) w)) (Classical.propDecidable _) 0 1) t =
      Height.wordSum (fun w=>if hit (Height.runWord next (x,false) w) then 0 else 1) t := by
    apply Height.wordSum_congr_fun
    intro w
    have Q := Height.stoppedRun_mem_iff_runWord_mem next hit (monitor_true raw paints)
      (x,false) w
    by_cases J : hit (Height.runWord next (x,false) w)
    · simp [J,Q.mpr J]
    · have K : ¬hit (Height.stoppedRun next hit (x,false) w) := fun P=>J (Q.mp P)
      simp [J,K]
  rw [E] at V
  have T : Height.wordSum (fun w => if (Height.runWord (monitor raw paints) (x,false) w).2=true then 0 else 1) t =
      Height.wordSum (fun w=>if hit (Height.runWord next (x,false) w) then 0 else 1) t := by
    apply Height.wordSum_congr_fun
    intro w
    by_cases U : hit (Height.runWord next (x,false) w)
    · have U' : (Height.runWord (monitor raw paints) (x,false) w).2=true := U
      simp only [if_pos U,if_pos U']
    · have U' : ¬(Height.runWord (monitor raw paints) (x,false) w).2=true := U
      simp only [if_neg U,if_neg U']
  rw [T]
  exact V

#print axioms miss_count
#print axioms mean_in_height
#print axioms monitor_true
end L4.ReportPulseWait
