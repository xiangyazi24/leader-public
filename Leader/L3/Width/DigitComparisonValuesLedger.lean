import Leader.L3.Width.DigitComparisonValuesGhost
import Leader.L3.Width.DigitComparisonValuesCarry
import Leader.L3.Width.DigitComparisonValuesArith
import Leader.L3.Target

/-!
# R10c digit values: the carry chain of a writer ledger

The writer ghost of a live physical carry records, for each use, the settled input value `v`, the
carry that entered the cell and (for the first use) the launch.  This module proves that on every
edge step the ledger of a carry that is not inherited is a *carry chain*: its first use enters with
carry `1`, and the carry entering use `h + 1` is the carry leaving use `h`, the leaving carry being
`carry && (v + 1 = topA)` exactly as in the advance row of `liveTopPair`.  Together with
`carry_chain_mod` this gives the value of a completed writer ledger.

Consumer: `Leader/L3/Width/DigitComparisonValuesFold.lean`.
-/

namespace L3

set_option autoImplicit false

/-- A carry chain: the uses of a ledger launched with carry `1`, the carry `cc` leaving the last use.

Consumer: `CarryInv`, `carryInv_pair`. -/
inductive CarryChain {c : Compiled} {n : Nat} (a : Nat) : Bool → List (DigitUse c n) → Prop
  | nil : CarryChain a true []
  | snoc {cc : Bool} {us : List (DigitUse c n)} (u : DigitUse c n)
      (h : CarryChain a cc us) (hu : u.carryIn = cc) :
      CarryChain a (cc && (u.value.val + 1 == a)) (us ++ [u])

/-- `snoc` with the value of the new use named.  Consumer: `carryInv_pair`. -/
theorem CarryChain.snoc_value {c : Compiled} {n : Nat} {a : Nat} {cc : Bool}
    {us : List (DigitUse c n)} (u : DigitUse c n) (h : CarryChain a cc us)
    (hu : u.carryIn = cc) (v : Fin c.topA) (hv : u.value = v) :
    CarryChain a (cc && (v.val + 1 == a)) (us ++ [u]) := by
  have := CarryChain.snoc u h hu
  rw [hv] at this
  exact this

/-- The writer-carry invariant of one site: a physical carry is live exactly when the ghost has a
carry, and the ledger of a live ghost carry that is not inherited is a carry chain ending in the
physical carry bit.

Consumer: `carryInv_pair`, `writerTerminalChain` (WidthDigitComparisonValuesFold). -/
def CarryInv {c : Compiled} {n : Nat} (a : Nat) (w : WCarry) (g : Option (DigitCarryGhost c n)) :
    Prop :=
  match w with
  | .OFF => g = none
  | .W cc => ∃ L : DigitCarryGhost c n, g = some L ∧ (L.inherited = none → CarryChain a cc L.uses)

/-- Consumer: `carryInv_pair`. -/
theorem carryInv_off {c : Compiled} {n : Nat} (a : Nat) :
    CarryInv (c := c) (n := n) a .OFF none := rfl

/-- Leader row of the invariant.  Consumer: `carryInv_pair`. -/
theorem carryInv_root {c : Compiled} {n : Nat} (a : Nat) (w : WCarry)
    (g : Option (DigitCarryGhost c n)) (hg : CarryInv a w g) :
    CarryInv a (if w.isW = true then .OFF else w) (if w.isW = true then none else g) := by
  cases w with
  | OFF => simpa [WCarry.isW] using hg
  | W cc => simpa [WCarry.isW] using carryInv_off (c := c) (n := n) a

section Step

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source dest : Fin n)
  (ox oy : Agent c) (bX bY : Bool) (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- **One edge step preserves the writer-carry invariant**, for the physical row `liveTopPair` and
the ghost row `digitLaneReplay`, given that the lane views read the physical agents.

Consumer: `writerCarryStep`. -/
theorem carryInv_pair
    (hl : xv.leader = ox.l) (hyl : yv.leader = oy.l)
    (hcx : xv.carryLive = ox.wCarry.isW) (hcy : yv.carryLive = oy.wCarry.isW)
    (hmx : xv.marker = bX) (hmy : yv.marker = bY)
    (hix : xv.input = ox.wIn) (hiy : yv.input = oy.wIn)
    (hbx : xv.carryBit = wcC ox.wCarry)
    (hx : CarryInv c.topA ox.wCarry gx.carry) (hy : CarryInv c.topA oy.wCarry gy.carry) :
    CarryInv c.topA (liveTopPair c ox oy bX bY).x.wCarry
        (digitLaneReplay lane time source dest xv yv gx gy).x.carry ∧
      CarryInv c.topA (liveTopPair c ox oy bX bY).y.wCarry
        (digitLaneReplay lane time source dest xv yv gx gy).y.carry := by
  by_cases hroot : ox.l = true ∨ oy.l = true
  · have hr : (xv.leader || yv.leader) = true := by
      rw [hl, hyl]; rcases hroot with h | h <;> simp [h]
    have p := liveTop_carry_root c ox oy bX bY hroot
    have g := replay_carry_root lane time source dest xv yv gx gy hr
    rw [p.1, p.2, g.1, g.2, hcx, hcy]
    exact ⟨carryInv_root _ _ _ hx, carryInv_root _ _ _ hy⟩
  · have hxl : ox.l = false := by
      cases h : ox.l
      · rfl
      · exact absurd (Or.inl h) hroot
    have hyl' : oy.l = false := by
      cases h : oy.l
      · rfl
      · exact absurd (Or.inr h) hroot
    have hvx : xv.leader = false := by rw [hl, hxl]
    have hvy : yv.leader = false := by rw [hyl, hyl']
    cases hw : ox.wCarry with
    | W cc =>
      have hxc : xv.carryLive = true := by rw [hcx, hw]; rfl
      rw [hw] at hx hbx
      have hbx' : xv.carryBit = cc := hbx
      by_cases hbY : bY = true
      · have hm : yv.marker = true := by rw [hmy]; exact hbY
        have p := liveTop_carry_terminal c ox oy bX bY cc hxl hyl' hbY hw
        have g := replay_carry_terminal lane time source dest xv yv gx gy hvx hvy hxc hm
        rw [p.1, p.2, g.1, g.2]
        exact ⟨carryInv_off _, hy⟩
      · have hbY' : bY = false := Bool.eq_false_iff.mpr hbY
        have hm : yv.marker = false := by rw [hmy]; exact hbY'
        cases hyw : oy.wCarry with
        | W c' =>
          have hyc : yv.carryLive = true := by rw [hcy, hyw]; rfl
          have p := liveTop_carry_blockedCarry c ox oy bX bY cc c' hxl hyl' hbY' hw hyw
          have g := replay_carry_blockedCarry lane time source dest xv yv gx gy hvx hvy hxc hm hyc
          rw [p.1, p.2, g.1, g.2, hyw]
          rw [hyw] at hy
          exact ⟨carryInv_off _, hy⟩
        | OFF =>
          have hyc : yv.carryLive = false := by rw [hcy, hyw]; rfl
          rw [hyw] at hy
          by_cases hs : oy.wIn.isS = true
          · obtain ⟨v, T, hS⟩ : ∃ v T, oy.wIn = .S v T := by
              cases hI : oy.wIn with
              | S v T => exact ⟨v, T, rfl⟩
              | E => rw [hI] at hs; simp [InTok.isS] at hs
              | X => rw [hI] at hs; simp [InTok.isS] at hs
              | P v T => rw [hI] at hs; simp [InTok.isS] at hs
            have his : yv.input.isS = true := by rw [hiy, hS]; rfl
            have p := liveTop_advance_carry c ox oy bX bY cc v T hxl hyl' hbY' hw hyw hS
            have g := replay_carry_success lane time source dest xv yv gx gy hvx hvy hxc hm hyc his
            rw [p.1, p.2, g.1, g.2]
            refine ⟨carryInv_off _, ?_⟩
            obtain ⟨L, hL, hch⟩ := hx
            rw [hL]
            refine ⟨_, rfl, ?_⟩
            intro hinh
            have hv : inV c yv.input = v := by rw [hiy, hS]; rfl
            exact CarryChain.snoc_value _ (hch hinh) hbx' v hv
          · have hs' : oy.wIn.isS = false := Bool.eq_false_iff.mpr hs
            have his : yv.input.isS = false := by rw [hiy]; exact hs'
            have p := liveTop_carry_blockedInput c ox oy bX bY cc hxl hyl' hbY' hw hs'
            have g := replay_carry_blockedInput lane time source dest xv yv gx gy hvx hvy hxc hm his
            rw [p.1, p.2, g.1, g.2, hyw]
            exact ⟨carryInv_off _, hy⟩
    | OFF =>
      have hxc : xv.carryLive = false := by rw [hcx, hw]; rfl
      rw [hw] at hx
      have hx0 : gx.carry = none := hx
      by_cases hbX : bX = true
      · by_cases hs : ox.wIn.isS = true
        · obtain ⟨v, T, hS⟩ : ∃ v T, ox.wIn = .S v T := by
            cases hI : ox.wIn with
            | S v T => exact ⟨v, T, rfl⟩
            | E => rw [hI] at hs; simp [InTok.isS] at hs
            | X => rw [hI] at hs; simp [InTok.isS] at hs
            | P v T => rw [hI] at hs; simp [InTok.isS] at hs
          have hm : xv.marker = true := by rw [hmx]; exact hbX
          have his : xv.input.isS = true := by rw [hix, hS]; rfl
          have p := liveTop_carry_launch c ox oy bX bY v T hxl hyl' hbX hw hS
          have g := replay_carry_launch lane time source dest xv yv gx gy hvx hvy hxc hm his
          rw [p.1, p.2, g.1, g.2]
          refine ⟨⟨_, rfl, ?_⟩, hy⟩
          intro _
          have hv : inV c xv.input = v := by rw [hix, hS]; rfl
          exact CarryChain.snoc_value _ CarryChain.nil rfl v hv
        · have hs' : ox.wIn.isS = false := Bool.eq_false_iff.mpr hs
          have his : xv.input.isS = false := by rw [hix]; exact hs'
          have p := liveTop_carry_idleInput c ox oy bX bY hxl hyl' hw hs'
          have g := replay_carry_idleInput lane time source dest xv yv gx gy hvx hvy hxc his
          rw [p.1, p.2, g.1, g.2, hx0]
          exact ⟨carryInv_off _, hy⟩
      · have hbX' : bX = false := Bool.eq_false_iff.mpr hbX
        have hm : xv.marker = false := by rw [hmx]; exact hbX'
        have p := liveTop_carry_idleBeta c ox oy bX bY hxl hyl' hbX' hw
        have g := replay_carry_idleMarker lane time source dest xv yv gx gy hvx hvy hxc hm
        rw [p.1, p.2, g.1, g.2, hx0]
        exact ⟨carryInv_off _, hy⟩

end Step

/-- **One edge of the audit preserves the writer-carry invariant of the two endpoints.**

Consumer: `carryAll_step`. -/
theorem writerCarryStep {c : Compiled} {n : Nat} (time : Nat) (source dest : Fin n)
    (x y : ProjD c) (gx gy : DigitGhost c n)
    (hx : CarryInv c.topA x.top.wCarry gx.writer.carry)
    (hy : CarryInv c.topA y.top.wCarry gy.writer.carry) :
    CarryInv c.topA (pairD x y).1.top.wCarry
        (digitService time source dest x y gx gy).x.writer.carry ∧
      CarryInv c.topA (pairD x y).2.top.wCarry
        (digitService time source dest x y gx gy).y.writer.carry :=
  carryInv_pair .writer time source dest x.lift y.lift (pairW x.word y.word).1.beta
    (pairW x.word y.word).2.beta
    (digitLaneView .writer x (workerW x.word y.word).betaX)
    (digitLaneView .writer y (workerW x.word y.word).betaY) gx.writer gy.writer
    rfl rfl rfl rfl rfl rfl rfl rfl rfl hx hy

/-- The writer-carry invariant at every site of a physical state with ghost.

Consumer: `carryAll_step`, `AuditCarryInv` (WidthDigitComparisonValuesFold). -/
def CarryAll {c : Compiled} {n : Nat} (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) : Prop :=
  ∀ i, CarryInv c.topA (S i).top.wCarry (G i).writer.carry

/-- The invariant is preserved by one audited edge.

Consumer: `auditCarryInv_step` (WidthDigitComparisonValuesFold). -/
theorem carryAll_step {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) (time : Nat) (e : Fin n)
    (h : CarryAll S G) :
    CarryAll (phiD ring S e) (digitGhostStep ring S G time e) := by
  intro i
  have hs := writerCarryStep time e (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
    (G e) (G (ring.rightNeighbor e)) (h e) (h (ring.rightNeighbor e))
  by_cases hie : i = e
  · subst hie
    simpa [phiD, projectedEdge, digitGhostStep] using hs.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      simpa [phiD, projectedEdge, digitGhostStep, hie] using hs.2
    · simpa [phiD, projectedEdge, digitGhostStep, hie, hij] using h i

end L3

#print axioms L3.carryAll_step
#print axioms L3.carryInv_pair
