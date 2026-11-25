import Leader.L4.Height.G9WirePart01
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section Admission
open PhysicalCustody ClockServiceSpec BStarAcquireAnchors BStarH6WordChart

theorem double_power_mass (k mass : Nat) :
    2 * (2^k * mass) = 2^(k+1) * mass := by
  rw [Nat.pow_succ]
  ac_rfl

/-- A successful steered word can also require that its admissions stay
within budget. Restore the publication count on the unmodified alphabet. -/
theorem publication_block_of_steering {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (i : Header (oldH6 (rows s) g.base))
    (active preferred : Raw s n → Fin n → Bool) (mate : Raw s n → Fin n → Fin n)
    (involutive : ∀ y e, mate y (mate y e) = e)
    (paired : ∀ y e, active y e = true → active y (mate y e) = true)
    (opposite : ∀ y e, active y e = true → preferred y (mate y e) = !(preferred y e))
    (good : List (Fin n) → Prop)
    (genuine : ∀ w, good w → ClockServiceSpec.publishes x i.val w)
    (t : Nat)
    (budget : ∀ w, w.length = t → good w → steeringCount (rawNext s) active x w ≤ 5*longBudget)
    (half : n^t ≤ 2 * failureCount (fun w =>
      good (steerWord (rawNext s) active preferred mate x w)) t) :
    n^t ≤ 2^(5*longBudget+1) * failureCount (ClockServiceSpec.publishes x i.val) t := by
  have restored := restore_prescribed_sides (rawNext s) active preferred mate
    involutive paired opposite x good t (5*longBudget) budget
  have hgood : failureCount good t ≤ failureCount (ClockServiceSpec.publishes x i.val) t := by
    apply wordSum_mono
    intro u
    by_cases h : good u
    · simp [h, genuine u h]
    · simp [h]
  calc
    n^t ≤ 2 * failureCount (fun w => good (steerWord (rawNext s) active preferred mate x w)) t := half
    _ ≤ 2 * (2^(5*longBudget) * failureCount good t) := Nat.mul_le_mul_left 2 restored
    _ ≤ 2 * (2^(5*longBudget) * failureCount (ClockServiceSpec.publishes x i.val) t) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hgood)
    _ = _ := double_power_mass (5*longBudget) (failureCount (ClockServiceSpec.publishes x i.val) t)
end Admission

end L4.Height.G9Wire
