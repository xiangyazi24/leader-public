import Leader.L4.Height.ProductionBlockMoment
import Leader.L4.Height.RawServiceCore

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarAcquireAnchors
open Classical

noncomputable section

private theorem suffix_publication {s n : Nat} (x : Raw s n) (i : Fin n)
    (a v : List (Fin n)) (h : RawServiceCore.publishes (rawRun x a) i v) :
    RawServiceCore.publishes x i (a++v) := by
  obtain ⟨pre,post,rfl,c⟩ := h
  refine ⟨a++pre,post,(List.append_assoc ..).symm,?_⟩
  change ¬BStarGrantWriterHistory.NoPublication (show 0<2 by decide) (rawRun x (a++pre)) i i
  rw [show rawRun x (a++pre)=rawRun (rawRun x a) pre from BStarResetSchedule.run_append (rawNext s) x a pre]
  exact c

/-- The strict physical block at every production custody state yields the
dyadic moment on the raw chain, including arbitrary surviving prefixes. -/
theorem moment_of_production_block (blocks : ProductionBlock) {s n : Nat} {x : Raw s n}
    (g : CustodyWitness x) (P : Production g) (i : Header (oldH6 (rows s) g.base)) (t : Nat) :
    wordSum (fun w => 2^(min (RawServiceCore.strictWait x i.val w) t /
      (2^(5*longBudget+34)*n*radWidth s))) t ≤ 2*n^t := by
  let H := 2*(2^20*n*width g)
  have hn : 0 < n := Nat.zero_lt_of_lt i.val.isLt
  have hw := width_bounds g
  have hH : 0 < H := Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos (by decide) hn) hw.1)
  apply RawServiceCore.strict_moment_of_history_blocks x i.val H (2^(5*longBudget+1)) _
    hH (Nat.two_pow_pos _) (block_moment_scale longBudget n _ _ hw.2)
  intro a
  have fresh := blocks (extend g a) (production_extend P a) i
  change n^H ≤ _ * wordSum _ H at fresh
  rw [← repair_wordSum_eq_thru]
  apply Nat.le_trans fresh (Nat.mul_le_mul_left _ ?_)
  apply repair_wordSum_mono_length
  intro w _
  by_cases pub : RawServiceCore.publishes (rawRun x a) i.val w
  · simp [pub,suffix_publication x i.val a w pub]
  · simp [pub]

#print axioms moment_of_production_block
end
end L4.Height.ProductionCustody
