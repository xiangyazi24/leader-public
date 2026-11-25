import Leader.L4.AllSizeComposition
import Leader.Core.FiniteUniformStoppingTree

namespace L4.ShortFiveRenewal
open TaggedTail TripleRenewal Classical

/-- Prepending any adapted preparation that cannot itself stop in failure
preserves the uniform failure bound of the marked attempt. -/
theorem failure_through_regeneration {Y : Type} {n : Nat}
    (next : Y → Fin n → Y) (reachable prep done bad : Y → Prop) (D : Nat)
    (closed : ∀ y e, reachable y → reachable (next y e))
    (noEarlyFailure : ∀ y, reachable y → done y → bad y → prep y)
    (after : ∀ y, reachable y → prep y → ∀ t,
      D * terminalMass next done bad t y ≤ (D-1)*n^t)
    (t : Nat) (y : Y) (hy : reachable y) :
    D * terminalMass next done bad t y ≤ (D-1)*n^t := by
  induction t generalizing y with
  | zero =>
    by_cases hp : prep y
    · exact after y hy hp 0
    have h : ¬(done y ∧ bad y) := fun e => hp (noEarlyFailure y hy e.1 e.2)
    simp [terminalMass,h]
  | succ t ih =>
    by_cases hp : prep y
    · exact after y hy hp (t+1)
    by_cases h : done y
    · have hb : ¬bad y := fun b => hp (noEarlyFailure y hy h b)
      simp [terminalMass,h,hb]
    · simp only [terminalMass,h,if_false,sumEdge,←FiniteUniformStoppingTree.ofFn_sum_mul_left]
      calc
        _ ≤ (List.ofFn (fun _ : Fin n => (D-1)*n^t)).sum :=
          FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun e => ih _ (closed y e hy))
        _ = _ := by rw [FiniteUniformStoppingTree.ofFn_sum_const,Nat.pow_succ]; ac_rfl

/-- Full variable-length raw-tape renewal. The probability input is a
finite-horizon terminal failure bound, not a claim about consecutive
raw labels. The 'prep' predicate is evaluated on the actual monitor. -/
theorem expected {X : Type} {n : Nat} (step : X → Fin n → X)
    (goal admissible : X → Prop) (R A D : Nat) (hD : 0<D)
    (data : ∀ x, admissible x → ¬ goal x →
      ∃ stage : Stage step x, ∃ prep : stage.State → Prop,
        (¬ stage.ready stage.start) ∧
        (∀ y, stage.reachable y → stage.ready y → ¬ goal (stage.project y) →
          admissible (stage.project y)) ∧
        (∀ y, stage.reachable y → stage.ready y → prep y) ∧
        IIDExpectedHittingTimeAtMost stage.next prep stage.start R ∧
        (∀ y, stage.reachable y → prep y → IIDExpectedHittingTimeAtMost stage.next stage.ready y A) ∧
        (∀ y, stage.reachable y → prep y → ∀ t,
          D * terminalMass stage.next stage.ready (fun z => ¬goal (stage.project z)) t y
            ≤ (D-1)*n^t))
    (x : X) (hx : admissible x) :
    IIDExpectedHittingTimeAtMost step goal x (D*(R+A)) := by
  apply expected_of_uniform_attempts step goal admissible (R+A) D hD _ x hx
  intro y hy hn
  obtain ⟨stage,prep,start,restart,terminal,regen,trial,fail⟩ := data y hy hn
  refine ⟨⟨stage,start,restart,?_,?_⟩⟩
  · intro t
    have h := glue_until_stop stage.next stage.next id (fun _ _ => rfl)
      stage.ready prep stage.reachable stage.reachStep A t
      (fun z u rz hz _ _ => trial z rz hz u) t (Nat.le_refl _) stage.start stage.reachStart
    have mass := terminalMass_le_total stage.next prep (fun z => ¬stage.ready z) t stage.start
    have hm := regen t
    change iidHitCost stage.next stage.ready t stage.start ≤ (R+A)*n^t
    rw [Nat.add_mul]
    exact Nat.le_trans h (Nat.add_le_add hm (Nat.mul_le_mul_left _ mass))
  · intro t
    exact failure_through_regeneration stage.next stage.reachable prep stage.ready
      (fun z => ¬goal (stage.project z)) D stage.reachStep
      (fun z rz dz _ => terminal z rz dz) fail t stage.start stage.reachStart

/-- Local failure potential on a watched-word monitor. Wrong watched
letters can stop in failure; spectators need not stutter raw bytes,
only preserve the indicated potential. -/
theorem terminal_failure_of_potential {Y : Type} {n : Nat}
    (next : Y → Fin n → Y) (reach done bad : Y → Prop)
    (D : Nat) (V : Y → Nat)
    (closed : ∀ y e, reach y → reach (next y e))
    (last : ∀ y, reach y → done y → bad y → D ≤ V y)
    (drift : ∀ y, reach y → ¬done y →
      (List.ofFn (fun e => V (next y e))).sum ≤ n*V y)
    (t : Nat) (y : Y) (hy : reach y) :
    D*terminalMass next done bad t y ≤ V y*n^t := by
  induction t generalizing y with
  | zero =>
    by_cases d : done y <;> by_cases b : bad y
    · simpa [terminalMass,d,b] using last y hy d b
    · simp [terminalMass,d,b]
    · simp [terminalMass,d,b]
    · simp [terminalMass,d,b]
  | succ t ih =>
    by_cases d : done y
    · by_cases b : bad y
      · simpa [terminalMass,d,b] using Nat.mul_le_mul_right (n^(t+1)) (last y hy d b)
      · simp [terminalMass,d,b]
    · simp only [terminalMass,d,if_false,sumEdge,←FiniteUniformStoppingTree.ofFn_sum_mul_left]
      calc
        _ ≤ (List.ofFn (fun e : Fin n => V (next y e)*n^t)).sum :=
          FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun e => ih _ (closed y e hy))
        _ = n^t*(List.ofFn (fun e => V (next y e))).sum := by
          simp only [Nat.mul_comm _ (n^t), FiniteUniformStoppingTree.ofFn_sum_mul_left]
        _ ≤ n^t*(n*V y) := Nat.mul_le_mul_left _ (drift y hy d)
        _ = _ := by rw [Nat.pow_succ]; ac_rfl

#print axioms terminal_failure_of_potential
#print axioms failure_through_regeneration
#print axioms expected
end L4.ShortFiveRenewal
