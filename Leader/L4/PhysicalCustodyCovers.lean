import Leader.L4.PhysicalCustody
import Leader.L4.BStarClearanceOffsetMask
set_option maxRecDepth 4096
namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarH6WordChart BStarClearanceOffset
local notation "hp" => (show 0<2 by decide)

/-- Different physical covers of the actual raw tape may be used
at each offset stage; no word repetition or rebuilt state. -/
theorem actual_offset_covers {s n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (he : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : Raw s n→Prop) (closed : ∀ y e,Q y→Q (rawNext s y e))
    (same : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i)
    (x : Raw s n) (qx : Q x) (blocks : List (List (Fin n)))
    (H : blocks.length≤5) (full : ∀ w∈blocks,∀ e,e∈w) :
    Q (rawRun x blocks.flatten) ∧ correct h hh blocks.length (rawRun x blocks.flatten) := by
  have run_eq (z : Raw s n) (w : List (Fin n)) :
      BStarClearanceOffset.run hp z w=rawRun z w := by
    induction w generalizing z with
    | nil => rfl
    | cons e w ih => exact ih (rawNext s z e)
  have aux (k : Nat) (x : Raw s n) (blocks : List (List (Fin n)))
      (H : k+blocks.length≤5) (full : ∀ w∈blocks,∀ e,e∈w)
      (qx : Q x) (C : correct h hh k x) :
      Q (rawRun x blocks.flatten) ∧ correct h hh (k+blocks.length) (rawRun x blocks.flatten) := by
    induction blocks generalizing k x with
    | nil => simpa [rawRun,BStarResetSchedule.run] using And.intro qx C
    | cons first rest ih =>
      have hk : k<5 := by simp at H; omega
      have P := cover hp h hh he Q closed same
        (fun y e _ => BStarClearanceOffsetMask.leftFrame hp y e) k hk x first qx C
      rw [run_eq] at P
      have C' : correct h hh (k+1) (rawRun x first) := fun i =>
        P.2.2 i (.inl ⟨RearTrace.predecessor i,full first List.mem_cons_self _,
          RearTrace.right_predecessor i⟩)
      have J := ih (k+1) (rawRun x first) (by simp at H; omega)
        (fun w hw => full w (List.mem_cons_of_mem _ hw)) P.1 C'
      rw [List.flatten_cons]
      rw [show rawRun x (first++rest.flatten) = rawRun (rawRun x first) rest.flatten from
        BStarResetSchedule.run_append (rawNext s) x first rest.flatten]
      rw [show k+(first::rest).length=k+1+rest.length by simp; omega]
      exact J
  simpa using aux 0 x blocks (by simpa using H) full qx (zero_correct h hh x)

end L4.PhysicalCustody
