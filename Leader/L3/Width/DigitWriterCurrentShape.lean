import Leader.L3.Width.DigitWriterCurrentLedgers

/-!
# Writer currentness: the shape of the carries after one lane replay

For one lane replay of an edge `(x, y)`, with the physical liveness of the two carries matching the
ghost (`xv.carryLive = false → gx.carry = none`, `xv.carryLive = true → gx.carry ≠ none`,
`yv.carryLive = false → gy.carry = none`), the carries after the replay are of one of three shapes:

* `keep`: each carry is dropped or unchanged;
* `success`: the source carry moves onto the empty destination (and gets one more use), the
  destination is not a delimiter;
* `launch`: the source (a delimiter) gets a new carry with no inheritance, the destination keeps.

Consumer: `WidthDigitWriterCurrentOrder` (the order of inherited and new carries in the window).
-/

namespace L3

open L3.WidthDigit

set_option autoImplicit false

section Abstract

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source dest : Fin n)
  (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- **The three shapes of the carries after one lane replay.**

Consumer: `windowShape` (WidthDigitWriterCurrentOrder). -/
theorem carryShape
    (hxN : xv.carryLive = false → gx.carry = none)
    (hxS : xv.carryLive = true → ∃ L, gx.carry = some L)
    (hyN : yv.carryLive = false → gy.carry = none) :
    (((digitLaneReplay lane time source dest xv yv gx gy).x.carry = none ∨
        (digitLaneReplay lane time source dest xv yv gx gy).x.carry = gx.carry) ∧
      ((digitLaneReplay lane time source dest xv yv gx gy).y.carry = none ∨
        (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry)) ∨
    (yv.marker = false ∧ (digitLaneReplay lane time source dest xv yv gx gy).x.carry = none ∧
      gy.carry = none ∧ ∃ (L : DigitCarryGhost c n) (u : DigitUse c n), gx.carry = some L ∧
        (digitLaneReplay lane time source dest xv yv gx gy).y.carry =
          some { inherited := L.inherited, uses := L.uses ++ [u] }) ∨
    (xv.marker = true ∧ gx.carry = none ∧
      (∃ u : DigitUse c n, (digitLaneReplay lane time source dest xv yv gx gy).x.carry =
        some { inherited := none, uses := [u] }) ∧
      (digitLaneReplay lane time source dest xv yv gx gy).y.carry = gy.carry) := by
  by_cases hroot : (xv.leader || yv.leader) = true
  · have g := replay_carry_root lane time source dest xv yv gx gy hroot
    rw [g.1, g.2]
    refine Or.inl ⟨?_, ?_⟩
    · by_cases hc : xv.carryLive = true
      · rw [if_pos hc]; exact Or.inl rfl
      · rw [if_neg hc]; exact Or.inr rfl
    · by_cases hc : yv.carryLive = true
      · rw [if_pos hc]; exact Or.inl rfl
      · rw [if_neg hc]; exact Or.inr rfl
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
        exact Or.inl ⟨Or.inl rfl, Or.inr rfl⟩
      · have hm' : yv.marker = false := Bool.eq_false_iff.mpr hm
        by_cases hyc : yv.carryLive = true
        · have g := replay_carry_blockedCarry lane time source dest xv yv gx gy hxl hyl hxc hm' hyc
          rw [g.1, g.2]
          exact Or.inl ⟨Or.inl rfl, Or.inr rfl⟩
        · have hyc' : yv.carryLive = false := Bool.eq_false_iff.mpr hyc
          by_cases his : yv.input.isS = true
          · have g := replay_carry_success lane time source dest xv yv gx gy hxl hyl hxc hm' hyc'
              his
            obtain ⟨L, hL⟩ := hxS hxc
            exact Or.inr (Or.inl ⟨hm', g.1, hyN hyc', L, _, hL, by rw [g.2, hL]; rfl⟩)
          · have his' : yv.input.isS = false := Bool.eq_false_iff.mpr his
            have g := replay_carry_blockedInput lane time source dest xv yv gx gy hxl hyl hxc hm'
              his'
            rw [g.1, g.2]
            exact Or.inl ⟨Or.inl rfl, Or.inr rfl⟩
    · have hxc' : xv.carryLive = false := Bool.eq_false_iff.mpr hxc
      by_cases hxm : xv.marker = true
      · by_cases hxs : xv.input.isS = true
        · have g := replay_carry_launch lane time source dest xv yv gx gy hxl hyl hxc' hxm hxs
          exact Or.inr (Or.inr ⟨hxm, hxN hxc', ⟨_, g.1⟩, g.2⟩)
        · have hxs' : xv.input.isS = false := Bool.eq_false_iff.mpr hxs
          have g := replay_carry_idleInput lane time source dest xv yv gx gy hxl hyl hxc' hxs'
          rw [g.1, g.2]
          exact Or.inl ⟨Or.inr rfl, Or.inr rfl⟩
      · have hxm' : xv.marker = false := Bool.eq_false_iff.mpr hxm
        have g := replay_carry_idleMarker lane time source dest xv yv gx gy hxl hyl hxc' hxm'
        rw [g.1, g.2]
        exact Or.inl ⟨Or.inr rfl, Or.inr rfl⟩

end Abstract

end L3

#print axioms L3.carryShape
