import Leader.Wu.Carrier.ValidatorPackedCarrier

/-!
# Current packed-table obstruction to a clocked writer

The QMAT row is a validator/sanitation table, not yet a physical AAFJ writer.
On decoded literal modes it frames both payload banks, `message`, and `trail`.
The only composition hook for a writer is the abstract role-3 staging row.
However, the current priority wrapper retags *both* outputs role 3 whenever
either input is role 3.  Hence it has no transition back to the decoded QMAT
free domain, independently of how the supplied staging row behaves.

Unused non-role-3 tags do not provide hidden clock modes: the QMAT partial
decoder returns `none`, and the total row frames the entire pair.  A concrete
clocked producer must therefore change the total transition table (while it
may still reuse the same finite carrier); it cannot be extracted from the
current constructors and wrapper.
-/

namespace PPLLCurrentTableClockObstruction

open PPLLV2ValidatorPhysicalRefinement
open PPLLParallelGeometryLift
open PPLLParallelGeometryPacked

set_option autoImplicit false
set_option warningAsError true

/-- The role-3 priority branch is selected if either endpoint is reserved. -/
theorem prioritized_of_reserved
    {h : Nat} (staging : PackedControlRow h)
    (left right : ParallelCell h PackedControl)
    (hreserved : StagingReserved left.2 = true ∨
      StagingReserved right.2 = true) :
    prioritizedPackedControlRow h staging left right =
      let out := staging left right
      (reserveStaging out.1, reserveStaging out.2) := by
  rcases hreserved with hleft | hright
  · simp [prioritizedPackedControlRow, hleft]
  · simp [prioritizedPackedControlRow, hright]

/-- Once the priority branch fires, both returned controls are reserved,
regardless of the staging row. -/
theorem prioritized_reserved_outputs_both_reserved
    {h : Nat} (staging : PackedControlRow h)
    (left right : ParallelCell h PackedControl)
    (hreserved : StagingReserved left.2 = true ∨
      StagingReserved right.2 = true) :
    let out := prioritizedPackedControlRow h staging left right
    StagingReserved out.1 = true ∧ StagingReserved out.2 = true := by
  rw [prioritized_of_reserved staging left right hreserved]
  simp

/-- Stronger than failure to equal a canonical encoding: neither output tag
decodes to *any* QMAT literal mode.  Therefore a service that ever enters the
current role-3 branch cannot return to a global free domain defined by decoded
QMAT controls, no matter which local staging row is supplied. -/
theorem prioritized_reserved_outputs_decode_none
    {h : Nat} (staging : PackedControlRow h)
    (left right : ParallelCell h PackedControl)
    (hreserved : StagingReserved left.2 = true ∨
      StagingReserved right.2 = true) :
    let out := prioritizedPackedControlRow h staging left right
    decodeLiteralTag out.1.role out.1.rootCtl = none ∧
      decodeLiteralTag out.2.role out.2.rootCtl = none := by
  rw [prioritized_of_reserved staging left right hreserved]
  simp [reserveStaging, decodeLiteralTag_role_three]

/-- In particular, neither output can be a canonical decoded QMAT mode. -/
theorem prioritized_reserved_cannot_reenter_encoded
    {h : Nat} (staging : PackedControlRow h)
    (left right : ParallelCell h PackedControl)
    (hreserved : StagingReserved left.2 = true ∨
      StagingReserved right.2 = true)
    (leftMode rightMode : PackedLiteralMode) :
    prioritizedPackedControlRow h staging left right ≠
      (encodeLiteral leftMode, encodeLiteral rightMode) := by
  intro heq
  have hout := prioritized_reserved_outputs_both_reserved
    staging left right hreserved
  rw [heq] at hout
  have hleft := hout.1
  rw [encodeLiteral_not_stagingReserved] at hleft
  contradiction

/-- First unused root tag.  It is not a new semantic mode in the current
table: the partial decoder rejects it. -/
def spareRootControl : PackedControl :=
  { activeBit := false
    stagingBit := false
    role := 0
    rootCtl := ⟨26, by omega⟩
    message := 0
    trail := 0 }

@[simp] theorem spareRootControl_decode_none :
    decodeLiteralTag spareRootControl.role spareRootControl.rootCtl = none := by
  simp [spareRootControl, decodeLiteralTag] <;> omega

/-- Any pair containing that unused tag is a literal QMAT stutter. -/
theorem packedLiteralStep_spare_left (right : PackedControl) :
    packedLiteralStep spareRootControl right = (spareRootControl, right) := by
  simp [packedLiteralStep]

/-- The actual QMAT branch cannot change either payload bank.  This restates
the existing producer theorem at the clock boundary. -/
theorem qmat_cannot_commit_payload (left right : PackedControl) :
    let out := packedLiteralStep left right
    out.1.activeBit = left.activeBit ∧
      out.2.activeBit = right.activeBit ∧
      out.1.stagingBit = left.stagingBit ∧
      out.2.stagingBit = right.stagingBit := by
  rcases packedLiteralStep_payload_framed left right with
    ⟨hleft, hright, hleftStage, hrightStage, _, _, _, _⟩
  exact ⟨hleft, hright, hleftStage, hrightStage⟩

#print axioms prioritized_reserved_outputs_both_reserved
#print axioms prioritized_reserved_outputs_decode_none
#print axioms prioritized_reserved_cannot_reenter_encoded
#print axioms packedLiteralStep_spare_left
#print axioms qmat_cannot_commit_payload

end PPLLCurrentTableClockObstruction
