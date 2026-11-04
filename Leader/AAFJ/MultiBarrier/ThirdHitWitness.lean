import Leader.AAFJ.MultiBarrier.ThirdHitRestartOrDrop

set_option autoImplicit false

namespace Q18387

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord

theorem hk3 : 0 < 3 := by
  decide

theorem hn4 : 0 < 4 := by
  decide

theorem hn3_4 : 2 < 4 := by
  decide

/-- Standard four-node directed ring. -/
def ring4 : DirectedRing 4 :=
  ⟨hn4⟩

/-- Literal label vector [2,1,2,1]. -/
def label4 (i : Fin 4) : Fin 3 :=
  if i = (0 : Fin 4) then
    (2 : Fin 3)
  else if i = (1 : Fin 4) then
    (1 : Fin 3)
  else if i = (2 : Fin 4) then
    (2 : Fin 3)
  else
    (1 : Fin 3)

/-- Concrete full payload.

All bullets, leaders, and probes are false.
Only a = 0 is phase-true; every other phase is false.
-/
def C4 (i : Fin 4) : State 3 :=
  { bullet := false
    leader := false
    label := label4 i
    probe := false
    phase := if i = (0 : Fin 4) then true else false }

/-- The projected label vector is literally [2,1,2,1]. -/
theorem C4_label_vector :
    labelsOf C4 (0 : Fin 4) = (2 : Fin 3) ∧
    labelsOf C4 (1 : Fin 4) = (1 : Fin 3) ∧
    labelsOf C4 (2 : Fin 4) = (2 : Fin 3) ∧
    labelsOf C4 (3 : Fin 4) = (1 : Fin 3) := by
  decide

/-- Check the actual original-P₃ successor-label convention used by IsBarrier. -/
theorem original_succLabel_values :
    succLabel hk3 (2 : Fin 3) = (0 : Fin 3) ∧
    succLabel hk3 (1 : Fin 3) = (2 : Fin 3) := by
  decide

/-- Under the original IsBarrier convention, [2,1,2,1] has
exactly physical barrier edges 0 and 2.

This is the convention check requested before using the label vector as
support {a,c}.
-/
theorem original_IsBarrier_support :
    ∀ e : Fin 4,
      IsBarrier hk3 (C4 e) (C4 (ring4.rightNeighbor e)) ↔
        e = (0 : Fin 4) ∨ e = (2 : Fin 4) := by
  decide

/-- The same exact support stated in the BarrierAt vocabulary required by
third_hit_restart_or_drop. -/
theorem support_a0_c2 :
    ∀ e : Fin 4,
      BarrierAt hk3 ring4 (labelsOf C4) e ↔
        e = (0 : Fin 4) ∨ e = (2 : Fin 4) := by
  intro e
  rw [barrierAt_labelsOf_iff hk3 ring4 C4 e]
  exact original_IsBarrier_support e

theorem a_to_b :
    ring4.rightNeighbor (0 : Fin 4) = (1 : Fin 4) := by
  decide

theorem b_to_c :
    ring4.rightNeighbor (1 : Fin 4) = (2 : Fin 4) := by
  decide

theorem a_phase_true :
    (C4 (0 : Fin 4)).phase = true := by
  decide

theorem b_probe_false :
    (C4 (1 : Fin 4)).probe = false := by
  decide

theorem c_phase_false :
    (C4 (2 : Fin 4)).phase = false := by
  decide

theorem c_probe_false :
    (C4 (2 : Fin 4)).probe = false := by
  decide

/-- Empty gap: trivially every selected edge is current-nonbarrier. -/
theorem empty_gap_current_nonbarrier :
    CurrentNonbarrierWord hk3 ring4 C4 [] := by
  simp [CurrentNonbarrierWord]

/-- Every configuration/geometry/payload premise of the attached
third_hit_restart_or_drop is simultaneously satisfied by the concrete witness.
-/
theorem third_hit_premises :
    ring4.rightNeighbor (0 : Fin 4) = (1 : Fin 4) ∧
    ring4.rightNeighbor (1 : Fin 4) = (2 : Fin 4) ∧
    (∀ e : Fin 4,
      BarrierAt hk3 ring4 (labelsOf C4) e ↔
        e = (0 : Fin 4) ∨ e = (2 : Fin 4)) ∧
    (C4 (0 : Fin 4)).phase = true ∧
    (C4 (1 : Fin 4)).probe = false ∧
    (C4 (2 : Fin 4)).phase = false ∧
    (C4 (2 : Fin 4)).probe = false ∧
    CurrentNonbarrierWord hk3 ring4 C4 [] := by
  exact ⟨a_to_b, b_to_c, support_a0_c2,
    a_phase_true, b_probe_false, c_phase_false, c_probe_false,
    empty_gap_current_nonbarrier⟩

/-- Explicit nonvacuity statement: the theorem's premise package is inhabited. -/
theorem third_hit_premises_inhabited :
    ∃ (C : Fin 4 → State 3)
      (a b c : Fin 4) (word : List (Fin 4)),
      ring4.rightNeighbor a = b ∧
      ring4.rightNeighbor b = c ∧
      (∀ e : Fin 4,
        BarrierAt hk3 ring4 (labelsOf C) e ↔ e = a ∨ e = c) ∧
      (C a).phase = true ∧
      (C b).probe = false ∧
      (C c).phase = false ∧
      (C c).probe = false ∧
      CurrentNonbarrierWord hk3 ring4 C word := by
  refine
    ⟨C4, (0 : Fin 4), (1 : Fin 4), (2 : Fin 4), [], ?_⟩
  exact third_hit_premises

/-- Concrete state immediately after the theorem's third anchored hit a=0.
The gap is empty, so rawRun C4 [] is definitionally C4. -/
def afterThird : Fin 4 → State 3 :=
  (AAFJPK.protocol 3 hk3).step ring4 C4 (0 : Fin 4)

#check AAFJPK.OriginalGappedFirstTriple.third_hit_restart_or_drop

/-- Apply the actual attached theorem to the inhabited concrete premise package. -/
theorem concrete_third_hit_restart_or_drop :
    barrierCount hk3 ring4 (labelsOf afterThird) <
        barrierCount hk3 ring4 (labelsOf C4) ∨
      (NormalizedAdjacentRestart hk3 ring4 afterThird
          (1 : Fin 4) (2 : Fin 4) ∧
        (afterThird (1 : Fin 4)).probe = false ∧
        (afterThird (2 : Fin 4)).probe = false) := by
  simpa [afterThird, rawRun] using
    (AAFJPK.OriginalGappedFirstTriple.third_hit_restart_or_drop
      hk3 ring4 hn3_4
      C4 (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      a_to_b b_to_c support_a0_c2
      a_phase_true b_probe_false c_phase_false c_probe_false
      [] empty_gap_current_nonbarrier)

#check original_IsBarrier_support
#check support_a0_c2
#check third_hit_premises_inhabited
#check concrete_third_hit_restart_or_drop

end Q18387

#print axioms Q18387.third_hit_premises_inhabited
#print axioms Q18387.concrete_third_hit_restart_or_drop
