import Leader.L4.AllSizeS1Geometry

namespace L4.PhysicalCustody.H1
open L4.AllSizeProtocol PhysicalMIS

abbrev Byte := BitVec 6

/-- Raw right-endpoint transitions have only one source of P, and it
writes the actual old left bit while arming its helper. -/
theorem prospective_right : ∀ (x y : Byte),
    role (next (x,y)).2 = 1 →
    role x = 0 ∧ role y = 0 ∧ role (next (x,y)).1 = 3 ∧
      ((next (x,y)).2).getLsbD 1 = selected x ∧
      selected (next (x,y)).1 = selected x := by
  decide +kernel

/-- Every A produced at the left endpoint is formed from P; its new
right helper keeps the actual sampled bit. -/
theorem armed_left : ∀ (x y : Byte),
    role (next (x,y)).1 = 2 →
    role x = 1 ∧ (role y = 0 ∨ role y = 4) ∧ role (next (x,y)).2 = 4 ∧
      ((next (x,y)).1).getLsbD 1 = x.getLsbD 1 ∧
      ((next (x,y)).1).getLsbD 0 = selected y ∧
      selected (next (x,y)).2 = selected y := by
  decide +kernel

/-- A helper's outside edge cannot change any of its bits. -/
theorem left_helper_outside : ∀ (x y : Byte),
    role y = 3 → (next (x,y)).2 = y := by
  decide +kernel

theorem right_helper_outside : ∀ (x y : Byte),
    role x = 4 → (next (x,y)).1 = x := by
  decide +kernel

/-- An incident real hit retires an old P or A. No right hit produces
A and no left hit produces P, including arbitrary spare bytes. -/
theorem prospective_armed_left_retire : ∀ (x y : Byte),
    (role x=1 ∨ role x=2) → role (next (x,y)).1 ≠ 1 := by
  decide +kernel

theorem armed_left_retire : ∀ (x y : Byte),
    role x=2 → role (next (x,y)).1 ≠ 2 := by
  decide +kernel

theorem prospective_armed_right_retire : ∀ (x y : Byte),
    (role y=1 ∨ role y=2) → role (next (x,y)).2 ≠ 1 ∧
      role (next (x,y)).2 ≠ 2 := by
  decide +kernel

theorem no_right_arm : ∀ (x y : Byte), role (next (x,y)).2 ≠ 2 := by
  decide +kernel

theorem no_left_prospective : ∀ (x y : Byte), role (next (x,y)).1 ≠ 1 := by
  decide +kernel

/-- Literal commit semantics: the old armed bytes commit using their
old cached bits; all other bytes keep their installed selection bit. -/
theorem selected_left : ∀ (x y : Byte),
    selected (next (x,y)).1 =
      if role x=2 then !(x.getLsbD 1 || x.getLsbD 0) else selected x := by
  decide +kernel

theorem selected_right : ∀ (x y : Byte),
    selected (next (x,y)).2 =
      if role y=2 then !(y.getLsbD 1 || y.getLsbD 0) else selected y := by
  decide +kernel

end L4.PhysicalCustody.H1
