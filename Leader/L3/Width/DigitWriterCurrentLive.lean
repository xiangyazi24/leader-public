import Leader.L3.Width.DigitComparisonValuesCarry

/-!
# Writer currentness: a live writer carry has an empty input after the step that touched it

The input block of `liveTopPair` (`WI0`-`WI7`) sets the input of an endpoint with a live carry to `E`
(first matches), and every later branch that could write an input is guarded by the slot flags.  So
after a step, an endpoint whose carry is live holds an empty input: a carry kept from before
(`liveTop_in_yLive`), a carry just advanced into the destination (`liveTop_in_success`), a carry
just launched at the source (`liveTop_in_launch`).

Consumer: `Leader/L3/Width/DigitWriterCurrentLiveInv.lean` (the invariant "a non-inherited live
carry has an empty input", which is the `LiveE` clause of the aged window).
-/

namespace L3

set_option autoImplicit false

section Live

variable (c : Compiled) (ox oy : Agent c) (bX bY : Bool)

/-- A destination carry that was live stays with an empty input.  Consumer: `liveTop_live_in`. -/
theorem liveTop_in_yLive (c' : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hy : oy.wCarry = .W c') :
    (liveTopPair c ox oy bX bY).y.wIn = .E := by
  cases hx : ox.wCarry with
  | OFF =>
    cases hxs : ox.wIn <;>
      (simp [liveTopPair, hxl, hyl, hy, hx, hxs, WCarry.isW, WCarry.isOff, topBorder, InTok.isS,
        InTok.isX, InTok.isP, topTerminal] <;>
        (repeat' split) <;> simp_all)
  | W cc =>
    simp [liveTopPair, hxl, hyl, hy, hx, WCarry.isW, WCarry.isOff]

/-- A destination that receives the carry has an empty input.  Consumer: `liveTop_live_in`. -/
theorem liveTop_in_success (cc : Bool) (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbY : bY = false)
    (hw : ox.wCarry = .W cc) (hoff : oy.wCarry = .OFF) (hs : oy.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).y.wIn = .E := by
  simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, WCarry.isW, WCarry.isOff, InTok.isS,
    topTerminal]

/-- A source that launches the carry has an empty input.  Consumer: `liveTop_live_in`. -/
theorem liveTop_in_launch (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbX : bX = true)
    (hw : ox.wCarry = .OFF) (hs : ox.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).x.wIn = .E := by
  cases hy : oy.wCarry with
  | OFF =>
    simp [liveTopPair, hxl, hyl, hbX, hw, hs, hy, WCarry.isW, WCarry.isOff, InTok.isS, InTok.isX,
      InTok.isP, InTok.isE, topBorder, topTerminal, topInternal]
    simp only [apply_ite InSt.iX, ite_self]
  | W c' =>
    simp [liveTopPair, hxl, hyl, hbX, hw, hs, hy, WCarry.isW, WCarry.isOff, InTok.isS, InTok.isX,
      InTok.isP, InTok.isE, topBorder, topTerminal, topInternal]
    all_goals (try simp only [apply_ite InSt.iX, ite_self])

/-- **After a step, an endpoint with a live writer carry has an empty input.**

Consumer: `liveInv_step` (WidthDigitWriterCurrentLiveInv). -/
theorem liveTop_live_in :
    ((liveTopPair c ox oy bX bY).x.wCarry.isW = true → (liveTopPair c ox oy bX bY).x.wIn = .E) ∧
      ((liveTopPair c ox oy bX bY).y.wCarry.isW = true →
        (liveTopPair c ox oy bX bY).y.wIn = .E) := by
  by_cases hroot : ox.l = true ∨ oy.l = true
  · have p := liveTop_carry_root c ox oy bX bY hroot
    rw [p.1, p.2]
    constructor <;> intro h <;> exfalso <;>
      (cases hw : ox.wCarry <;> cases hv : oy.wCarry <;> simp_all [WCarry.isW])
  · have hxl : ox.l = false := by
      cases h : ox.l
      · rfl
      · exact absurd (Or.inl h) hroot
    have hyl : oy.l = false := by
      cases h : oy.l
      · rfl
      · exact absurd (Or.inr h) hroot
    cases hw : ox.wCarry with
    | W cc =>
      by_cases hbY : bY = true
      · have p := liveTop_carry_terminal c ox oy bX bY cc hxl hyl hbY hw
        rw [p.1, p.2]
        refine ⟨fun h => by simp [WCarry.isW] at h, fun h => ?_⟩
        cases hv : oy.wCarry with
        | OFF => rw [hv] at h; simp [WCarry.isW] at h
        | W c' => exact liveTop_in_yLive c ox oy bX bY c' hxl hyl hv
      · have hbY' : bY = false := Bool.eq_false_iff.mpr hbY
        cases hv : oy.wCarry with
        | W c' =>
          have p := liveTop_carry_blockedCarry c ox oy bX bY cc c' hxl hyl hbY' hw hv
          rw [p.1, p.2, hv]
          exact ⟨fun h => by simp [WCarry.isW] at h,
            fun _ => liveTop_in_yLive c ox oy bX bY c' hxl hyl hv⟩
        | OFF =>
          by_cases hs : oy.wIn.isS = true
          · obtain ⟨v, T, hS⟩ : ∃ v T, oy.wIn = .S v T := by
              cases hI : oy.wIn with
              | S v T => exact ⟨v, T, rfl⟩
              | E => rw [hI] at hs; simp [InTok.isS] at hs
              | X => rw [hI] at hs; simp [InTok.isS] at hs
              | P v T => rw [hI] at hs; simp [InTok.isS] at hs
            have p := liveTop_advance_carry c ox oy bX bY cc v T hxl hyl hbY' hw hv hS
            rw [p.2]
            exact ⟨fun h => by simp [WCarry.isW] at h,
              fun _ => liveTop_in_success c ox oy bX bY cc v T hxl hyl hbY' hw hv hS⟩
          · have hs' : oy.wIn.isS = false := Bool.eq_false_iff.mpr hs
            have p := liveTop_carry_blockedInput c ox oy bX bY cc hxl hyl hbY' hw hs'
            rw [p.1, p.2, hv]
            exact ⟨fun h => by simp [WCarry.isW] at h, fun h => by simp [WCarry.isW] at h⟩
    | OFF =>
      by_cases hbX : bX = true
      · by_cases hs : ox.wIn.isS = true
        · obtain ⟨v, T, hS⟩ : ∃ v T, ox.wIn = .S v T := by
            cases hI : ox.wIn with
            | S v T => exact ⟨v, T, rfl⟩
            | E => rw [hI] at hs; simp [InTok.isS] at hs
            | X => rw [hI] at hs; simp [InTok.isS] at hs
            | P v T => rw [hI] at hs; simp [InTok.isS] at hs
          have p := liveTop_carry_launch c ox oy bX bY v T hxl hyl hbX hw hS
          rw [p.2]
          refine ⟨fun _ => liveTop_in_launch c ox oy bX bY v T hxl hyl hbX hw hS, fun h => ?_⟩
          cases hv : oy.wCarry with
          | OFF => rw [hv] at h; simp [WCarry.isW] at h
          | W c' => exact liveTop_in_yLive c ox oy bX bY c' hxl hyl hv
        · have hs' : ox.wIn.isS = false := Bool.eq_false_iff.mpr hs
          have p := liveTop_carry_idleInput c ox oy bX bY hxl hyl hw hs'
          rw [p.1, p.2]
          refine ⟨fun h => by simp [WCarry.isW] at h, fun h => ?_⟩
          cases hv : oy.wCarry with
          | OFF => rw [hv] at h; simp [WCarry.isW] at h
          | W c' => exact liveTop_in_yLive c ox oy bX bY c' hxl hyl hv
      · have hbX' : bX = false := Bool.eq_false_iff.mpr hbX
        have p := liveTop_carry_idleBeta c ox oy bX bY hxl hyl hbX' hw
        rw [p.1, p.2]
        refine ⟨fun h => by simp [WCarry.isW] at h, fun h => ?_⟩
        cases hv : oy.wCarry with
        | OFF => rw [hv] at h; simp [WCarry.isW] at h
        | W c' => exact liveTop_in_yLive c ox oy bX bY c' hxl hyl hv

end Live

end L3

#print axioms L3.liveTop_live_in
