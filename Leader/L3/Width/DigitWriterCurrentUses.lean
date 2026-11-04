import Leader.L3.Width.DigitComparisonValuesFold

/-!
# Writer currentness: every ledger use is a recorded physical write

The ghost ledger of a writer carry records, for each use, the time, the target cell, the consumed
input value and the carry-in (`DigitUse`).  The physical digit rows (`writerAdvanceWrite`,
`writerLaunchWrite`) say what the digit of the target cell is after the edge step.  This module
carries the link between the two along the audit: every use of every ledger of the current ghost
(and of every frame's old ghost) has a frame at its time after which the target digit is
`digitMod (value + carryIn)`, unless the target was dirty or held the base label `ZERO` before it.

* `usesPair`: the abstract one-edge step on the lane replay: a property `P` of uses holding on the
  old ledgers and on the two new use records holds on the new ledgers;
* `UseFrame`, `UsesFramed`, `usesFramed_step`, `usesFramed_fold`: the property along the audit.

Consumer: `Leader/L3/Width/DigitWriterCurrentWrites.lean` (the write of a completion's use).
-/

namespace L3

set_option autoImplicit false

section Abstract

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source dest : Fin n)
  (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n) (P : DigitUse c n → Prop)

/-- **A property of uses that holds on the old ledgers and on the two use records a row can create
holds on the ledgers after the lane replay.**

Consumer: `usesFramed_step`. -/
theorem usesPair
    (hxP : ∀ L, gx.carry = some L → ∀ u ∈ L.uses, P u)
    (hyP : ∀ L, gy.carry = some L → ∀ u ∈ L.uses, P u)
    (hadv : xv.leader = false → yv.leader = false → xv.carryLive = true → yv.marker = false →
      yv.carryLive = false → yv.input.isS = true →
      P { time := time, target := dest, operand := gy.input, value := inV c yv.input,
          tail := inT yv.input, targetDigit := yv.digit, carryIn := xv.carryBit,
          errorIn := xv.carryError })
    (hlau : xv.leader = false → yv.leader = false → xv.carryLive = false → xv.marker = true →
      xv.input.isS = true →
      P { time := time, target := source, operand := gx.input, value := inV c xv.input,
          tail := inT xv.input, targetDigit := xv.digit, carryIn := true, errorIn := false}) :
    (∀ L, (digitLaneReplay lane time source dest xv yv gx gy).x.carry = some L →
        ∀ u ∈ L.uses, P u) ∧
      (∀ L, (digitLaneReplay lane time source dest xv yv gx gy).y.carry = some L →
        ∀ u ∈ L.uses, P u) := by
  by_cases hroot : (xv.leader || yv.leader) = true
  · have g := replay_carry_root lane time source dest xv yv gx gy hroot
    rw [g.1, g.2]
    constructor
    · intro L hL
      by_cases hc : xv.carryLive = true
      · rw [if_pos hc] at hL; cases hL
      · rw [if_neg hc] at hL; exact hxP L hL
    · intro L hL
      by_cases hc : yv.carryLive = true
      · rw [if_pos hc] at hL; cases hL
      · rw [if_neg hc] at hL; exact hyP L hL
  · have hxl : xv.leader = false := by
      cases h : xv.leader
      · rfl
      · exact absurd (by simp [h]) hroot
    have hyl : yv.leader = false := by
      cases h : yv.leader
      · rfl
      · exact absurd (by simp [h]) hroot
    by_cases hxc : xv.carryLive = true
    · by_cases hm : yv.marker = true
      · have g := replay_carry_terminal lane time source dest xv yv gx gy hxl hyl hxc hm
        rw [g.1, g.2]
        exact ⟨(fun L hL => by cases hL), hyP⟩
      · have hm' : yv.marker = false := Bool.eq_false_iff.mpr hm
        by_cases hyc : yv.carryLive = true
        · have g := replay_carry_blockedCarry lane time source dest xv yv gx gy hxl hyl hxc hm' hyc
          rw [g.1, g.2]
          exact ⟨(fun L hL => by cases hL), hyP⟩
        · have hyc' : yv.carryLive = false := Bool.eq_false_iff.mpr hyc
          by_cases his : yv.input.isS = true
          · have g := replay_carry_success lane time source dest xv yv gx gy hxl hyl hxc hm' hyc'
              his
            rw [g.1, g.2]
            refine ⟨(fun L hL => by cases hL), ?_⟩
            intro L hL u hu
            cases hL
            have hu' := List.mem_append.mp hu
            rcases hu' with hu' | hu'
            · cases hgx : gx.carry with
              | none =>
                rw [hgx] at hu'
                simp at hu'
              | some L0 =>
                rw [hgx] at hu'
                exact hxP L0 hgx u hu'
            · simp only [List.mem_singleton] at hu'
              rw [hu']
              exact hadv hxl hyl hxc hm' hyc' his
          · have his' : yv.input.isS = false := Bool.eq_false_iff.mpr his
            have g := replay_carry_blockedInput lane time source dest xv yv gx gy hxl hyl hxc hm'
              his'
            rw [g.1, g.2]
            exact ⟨(fun L hL => by cases hL), hyP⟩
    · have hxc' : xv.carryLive = false := Bool.eq_false_iff.mpr hxc
      by_cases hxm : xv.marker = true
      · by_cases hxs : xv.input.isS = true
        · have g := replay_carry_launch lane time source dest xv yv gx gy hxl hyl hxc' hxm hxs
          rw [g.1, g.2]
          refine ⟨?_, hyP⟩
          intro L hL u hu
          cases hL
          simp only [List.mem_singleton] at hu
          rw [hu]
          exact hlau hxl hyl hxc' hxm hxs
        · have hxs' : xv.input.isS = false := Bool.eq_false_iff.mpr hxs
          have g := replay_carry_idleInput lane time source dest xv yv gx gy hxl hyl hxc' hxs'
          rw [g.1, g.2]
          exact ⟨hxP, hyP⟩
      · have hxm' : xv.marker = false := Bool.eq_false_iff.mpr hxm
        have g := replay_carry_idleMarker lane time source dest xv yv gx gy hxl hyl hxc' hxm'
        rw [g.1, g.2]
        exact ⟨hxP, hyP⟩

end Abstract

end L3

#print axioms L3.usesPair
