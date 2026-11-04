import Leader.Wu.Protocol.WaitStaged

set_option autoImplicit false
set_option Elab.async false

namespace ZZT0WriteSeq

open PPLL ZZWaitStaged

variable {ψ : Nat}


abbrev trapProj {ψ : Nat} (u : AgentState ψ) :=
  (u.leader, u.label, u.bit, u.state,
   u.path, u.path2, u.path3, u.write)

/-- GROUP_INFO start changes only `last_set` / `last_unset`. -/
theorem groupInfoStart_eight_fields
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (trapProj (groupInfoStart hψ l r).1,
      trapProj (groupInfoStart hψ l r).2) =
      (trapProj l, trapProj r) := by
  simp only [groupInfoStart]
  repeat (first | rfl | split)

/-- GROUP_INFO `last_set` movement frames the eight TrapInv fields. -/
theorem groupInfoSet_eight_fields
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (trapProj (groupInfoSet hψ l r).1,
      trapProj (groupInfoSet hψ l r).2) =
      (trapProj l, trapProj r) := by
  simp only [groupInfoSet]
  repeat (first | rfl | split)

/-- GROUP_INFO `last_unset` movement frames the eight TrapInv fields. -/
theorem groupInfoUnset_eight_fields
    (l r : AgentState ψ) :
    (trapProj (groupInfoUnset l r).1,
      trapProj (groupInfoUnset l r).2) =
      (trapProj l, trapProj r) := by
  simp only [groupInfoUnset]
  repeat (first | rfl | split)

/-- GROUP_INFO changes only `last`, `last_set`, and `last_unset`; both
endpoints frame all eight TrapInv-visible fields. -/
theorem groupInfo_eight_fields
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (trapProj (groupInfo hψ l r).1,
      trapProj (groupInfo hψ l r).2) =
      (trapProj l, trapProj r) := by
  rw [groupInfo_eq_staged]
  simp only [groupInfoStaged]
  rw [groupInfoUnset_eight_fields,
    groupInfoSet_eight_fields,
    groupInfoStart_eight_fields]

#print axioms ZZT0WriteSeq.groupInfoStart_eight_fields
#print axioms ZZT0WriteSeq.groupInfoSet_eight_fields
#print axioms ZZT0WriteSeq.groupInfoUnset_eight_fields
#print axioms ZZT0WriteSeq.groupInfo_eight_fields

#print axioms ZZT0WriteSeq.groupInfo_eight_fields

#print axioms ZZT0WriteSeq.groupInfoStart_eight_fields
#print axioms ZZT0WriteSeq.groupInfoSet_eight_fields
#print axioms ZZT0WriteSeq.groupInfoUnset_eight_fields
#print axioms ZZT0WriteSeq.groupInfo_eight_fields
