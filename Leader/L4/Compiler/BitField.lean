import Lean

/-!
Bit fields inside a packed natural-number word.
`extract x off w` reads the `w`-bit field at bit offset `off`;
`patch x off w v` overwrites that field with the low `w` bits of `v`
and leaves every other bit of `x` unchanged.
All facts are proved bit by bit through `Nat.eq_of_testBit_eq`.
-/

namespace L4
namespace Compiler
namespace BitField

/-- The `w`-bit field of `x` at bit offset `off`. -/
def extract (x off w : Nat) : Nat := (x >>> off) % 2 ^ w

/-- Overwrite the `w`-bit field of `x` at offset `off` by the low `w` bits of `v`:
first clear the field (xor with its current contents), then or in the new contents. -/
def patch (x off w v : Nat) : Nat :=
  (x ^^^ (extract x off w <<< off)) ||| ((v % 2 ^ w) <<< off)

theorem testBit_extract (x off w i : Nat) :
    (extract x off w).testBit i = (decide (i < w) && x.testBit (off + i)) := by
  simp [extract, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_patch (x off w v i : Nat) :
    (patch x off w v).testBit i =
      if off ≤ i ∧ i < off + w then v.testBit (i - off) else x.testBit i := by
  unfold patch
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_extract,
    Nat.testBit_mod_two_pow]
  by_cases h1 : off ≤ i
  · by_cases h2 : i < off + w
    · have h3 : i - off < w := by omega
      have h4 : off + (i - off) = i := by omega
      simp [h1, h2, h3, h4]
    · have h3 : ¬ (i - off < w) := by omega
      simp [h1, h2, h3]
  · have h3 : ¬ (i ≥ off) := by omega
    simp [h1, h3]

/-- T1: reading back the patched field gives the low `w` bits of `v`. -/
theorem extract_patch_same (x off w v : Nat) :
    extract (patch x off w v) off w = v % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_extract, testBit_patch, Nat.testBit_mod_two_pow]
  by_cases h : i < w
  · have h1 : off ≤ off + i := by omega
    have h2 : off + i < off + w := by omega
    have h3 : off + i - off = i := by omega
    simp [h, h1, h2, h3]
  · simp [h]

/-- T2: a disjoint field is unchanged by the patch. -/
theorem extract_patch_disjoint (x off w v off' w' : Nat)
    (hdis : off + w ≤ off' ∨ off' + w' ≤ off) :
    extract (patch x off w v) off' w' = extract x off' w' := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_extract, testBit_extract, testBit_patch]
  by_cases h : i < w'
  · have hout : ¬ (off ≤ off' + i ∧ off' + i < off + w) := by omega
    simp [h, hout]
  · simp [h]

/-- T3: every bit outside the patched field is unchanged. -/
theorem testBit_patch_outside (x off w v i : Nat) (hi : i < off ∨ off + w ≤ i) :
    (patch x off w v).testBit i = x.testBit i := by
  rw [testBit_patch]
  have hout : ¬ (off ≤ i ∧ i < off + w) := by omega
  simp [hout]

/-- T4: writing a field's own contents back changes nothing. -/
theorem patch_extract_self (x off w : Nat) :
    patch x off w (extract x off w) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_patch]
  by_cases h : off ≤ i ∧ i < off + w
  · rw [if_pos h, testBit_extract]
    have h1 : i - off < w := by omega
    have h2 : off + (i - off) = i := by omega
    simp [h1, h2]
  · rw [if_neg h]

/-- T5: patches of disjoint fields commute. -/
theorem patch_patch_disjoint (x off w v off' w' v' : Nat)
    (hdis : off + w ≤ off' ∨ off' + w' ≤ off) :
    patch (patch x off w v) off' w' v' = patch (patch x off' w' v') off w v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_patch, testBit_patch, testBit_patch, testBit_patch]
  by_cases h : off ≤ i ∧ i < off + w
  · have h' : ¬ (off' ≤ i ∧ i < off' + w') := by omega
    simp [h, h']
  · by_cases h' : off' ≤ i ∧ i < off' + w'
    · simp [h, h']
    · simp [h, h']

/-- Patching the same field twice keeps only the second value. -/
theorem patch_patch_same (x off w v v' : Nat) :
    patch (patch x off w v) off w v' = patch x off w v' := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_patch, testBit_patch, testBit_patch]
  by_cases h : off ≤ i ∧ i < off + w
  · simp [h]
  · simp [h]

/-- A patched word stays below `2 ^ W` when the field and the word fit in `W` bits. -/
theorem patch_lt (x off w v W : Nat) (hx : x < 2 ^ W) (hw : off + w ≤ W) :
    patch x off w v < 2 ^ W := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_patch]
  have hout : ¬ (off ≤ i ∧ i < off + w) := by omega
  rw [if_neg hout]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

end BitField
end Compiler
end L4

#print axioms L4.Compiler.BitField.testBit_extract
#print axioms L4.Compiler.BitField.testBit_patch
#print axioms L4.Compiler.BitField.extract_patch_same
#print axioms L4.Compiler.BitField.extract_patch_disjoint
#print axioms L4.Compiler.BitField.testBit_patch_outside
#print axioms L4.Compiler.BitField.patch_extract_self
#print axioms L4.Compiler.BitField.patch_patch_disjoint
#print axioms L4.Compiler.BitField.patch_patch_same
#print axioms L4.Compiler.BitField.patch_lt
