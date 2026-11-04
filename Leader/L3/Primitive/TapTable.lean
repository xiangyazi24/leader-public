import Leader.L3.Primitive.TapSelection
import Leader.L3.Primitive.TapSound

/-!
The compiled tap table is primitive at every width `t ≥ 2`: the literal strings for `t ≤ 17`
(`tapTable_primitive`) and the searched masks for `t ≥ 18` (`tapSelectedPrimitive`).
This removes the premise `(compileAdvice q).t ≤ 17` from every consumer of the tap table.
-/

namespace L3

set_option autoImplicit false

/-- For `t ≥ 18` the table is the bit list of the selected mask.
Consumer: `tapTablePrimitive`, `tapTableZeroBit`. -/
private theorem tapTable_large (t : Nat) (h : 18 ≤ t) (j : Nat) :
    (tapTable t).getD j false = Nat.testBit (tapSelectedMask t) j := by
  have hnot : ¬ t ≤ 17 := by omega
  have hmask := (tapSelectedMaskSpec t h).2.1
  have htab : tapTable t =
      (List.range t).map (fun j => Nat.testBit (tapSearchFuel t 0 1 (2 ^ t)) j) := by
    unfold tapTable
    rw [if_neg hnot]
  rw [htab]
  by_cases hj : j < t
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj,
      tapSelectedMask]
  · have hjt : t ≤ j := by omega
    have hpow : 2 ^ t ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hjt
    have hbit : Nat.testBit (tapSelectedMask t) j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hmask hpow)
    rw [hbit]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj]

/-- The compiled tap table gives a primitive recurrence at every width `t ≥ 2`.
Consumer: every former caller of `tapTable_primitive` above `Certificate`. -/
theorem tapTablePrimitive (t : Nat) (h2 : 2 ≤ t) :
    IsPrimitive t (fun j => (tapTable t).getD j false) := by
  by_cases h17 : t ≤ 17
  · exact tapTable_primitive t h2 h17
  · have ht : 18 ≤ t := by omega
    have heq : (fun j => (tapTable t).getD j false) =
        (fun j => Nat.testBit (tapSelectedMask t) j) := by
      funext j
      exact tapTable_large t ht j
    rw [heq]
    exact tapSelectedPrimitive t ht

/-- Every literal tap string starts with a one.
Consumer: `tapTableZeroBit`. -/
private theorem tapTable_small_zero :
    ∀ i : Fin 16, (tapTable (i.val + 2)).getD 0 false = true := by
  decide +kernel

/-- Tap 0 of the compiled table is set at every width `t ≥ 2`.
Consumer: the tap-0 fact of `BankWordPassValues`. -/
theorem tapTableZeroBit (t : Nat) (h2 : 2 ≤ t) :
    (tapTable t).getD 0 false = true := by
  by_cases h17 : t ≤ 17
  · have h := tapTable_small_zero ⟨t - 2, by omega⟩
    have hs : t - 2 + 2 = t := by omega
    simpa only [hs] using h
  · have ht : 18 ≤ t := by omega
    rw [tapTable_large t ht 0]
    exact tapSelectedZeroBit t ht

end L3

#print axioms L3.tapTablePrimitive
#print axioms L3.tapTableZeroBit
