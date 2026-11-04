import Leader.L3.Width.DigitWriterCurrentOrderStep

/-!
# Writer currentness: the new use records of one lane replay

Like `carryShape`, but the success and launch shapes also expose the use record that is appended or
created: its time is the replay time and its operand is the ghost input of the destination
(success) or of the source (launch), whose physical input is settled.

* `carryShapeU` (abstract replay), `edgeCarryU` (the two sites of one audited edge);
* `windowUses`: a property of uses that depends only on the time and the operand, holds on the old
  ledgers of the target window, and holds on every record that a success or a launch inside the
  window can create, holds on the ledgers of the window after one audited edge.

Consumer: `WidthDigitWriterCurrentUseStruct` (the structural half of the aged uses).
-/

namespace L3

open L3.WidthDigit
open L3.RenewalReferenceClock

set_option autoImplicit false

section Abstract

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source dest : Fin n)
  (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- **The three shapes of the carries after one lane replay, with the new use records.**

Consumer: `edgeCarryU`. -/
theorem carryShapeU
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
          some { inherited := L.inherited, uses := L.uses ++ [u] } ∧
        u.time = time ∧ u.operand = gy.input ∧ yv.input.isS = true) ∨
    (xv.marker = true ∧ gx.carry = none ∧
      (∃ u : DigitUse c n, (digitLaneReplay lane time source dest xv yv gx gy).x.carry =
        some { inherited := none, uses := [u] } ∧ u.time = time ∧ u.operand = gx.input ∧
        xv.input.isS = true) ∧
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
            exact Or.inr (Or.inl ⟨hm', g.1, hyN hyc', L, _, hL, by rw [g.2, hL]; rfl, rfl,
              rfl, his⟩)
          · have his' : yv.input.isS = false := Bool.eq_false_iff.mpr his
            have g := replay_carry_blockedInput lane time source dest xv yv gx gy hxl hyl hxc hm'
              his'
            rw [g.1, g.2]
            exact Or.inl ⟨Or.inl rfl, Or.inr rfl⟩
    · have hxc' : xv.carryLive = false := Bool.eq_false_iff.mpr hxc
      by_cases hxm : xv.marker = true
      · by_cases hxs : xv.input.isS = true
        · have g := replay_carry_launch lane time source dest xv yv gx gy hxl hyl hxc' hxm hxs
          exact Or.inr (Or.inr ⟨hxm, hxN hxc', ⟨_, g.1, rfl, rfl, hxs⟩, g.2⟩)
        · have hxs' : xv.input.isS = false := Bool.eq_false_iff.mpr hxs
          have g := replay_carry_idleInput lane time source dest xv yv gx gy hxl hyl hxc' hxs'
          rw [g.1, g.2]
          exact Or.inl ⟨Or.inr rfl, Or.inr rfl⟩
      · have hxm' : xv.marker = false := Bool.eq_false_iff.mpr hxm
        have g := replay_carry_idleMarker lane time source dest xv yv gx gy hxl hyl hxc' hxm'
        rw [g.1, g.2]
        exact Or.inl ⟨Or.inr rfl, Or.inr rfl⟩

end Abstract

section Step

variable {c : Compiled} {n : Nat}

/-- **The three shapes of the writer carries at the two sites of one audited edge, with the new
use records.**

Consumer: `windowUses`. -/
theorem edgeCarryU (ring : DirectedRing n) (hn : 2 ≤ n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) (time : Nat) (e : Fin n) (hcar : CarryAll S G) :
    (((digitGhostStep ring S G time e e).writer.carry = none ∨
        (digitGhostStep ring S G time e e).writer.carry = (G e).writer.carry) ∧
      ((digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry = none ∨
        (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
          (G (ring.rightNeighbor e)).writer.carry)) ∨
    ((workerW (S e).word (S (ring.rightNeighbor e)).word).betaY = false ∧
      (digitGhostStep ring S G time e e).writer.carry = none ∧
      (G (ring.rightNeighbor e)).writer.carry = none ∧
      ∃ (L : DigitCarryGhost c n) (u : DigitUse c n), (G e).writer.carry = some L ∧
        (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
          some { inherited := L.inherited, uses := L.uses ++ [u] } ∧
        u.time = time ∧ u.operand = (G (ring.rightNeighbor e)).writer.input ∧
        (S (ring.rightNeighbor e)).top.wIn.isS = true) ∨
    ((workerW (S e).word (S (ring.rightNeighbor e)).word).betaX = true ∧
      (G e).writer.carry = none ∧
      (∃ u : DigitUse c n, (digitGhostStep ring S G time e e).writer.carry =
        some { inherited := none, uses := [u] } ∧ u.time = time ∧
        u.operand = (G e).writer.input ∧ (S e).top.wIn.isS = true) ∧
      (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
        (G (ring.rightNeighbor e)).writer.carry) := by
  have hne := rightNeighbor_ne ring hn e
  have hx := hcar e
  have hy := hcar (ring.rightNeighbor e)
  have hxN : (digitLaneView .writer (S e)
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX).carryLive = false →
      (G e).writer.carry = none := by
    intro h
    have h' : (S e).top.wCarry.isW = false := h
    cases hh : (S e).top.wCarry with
    | OFF => rw [hh] at hx; exact hx
    | W cc => rw [hh] at h'; simp [WCarry.isW] at h'
  have hxS : (digitLaneView .writer (S e)
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX).carryLive = true →
      ∃ L, (G e).writer.carry = some L := by
    intro h
    have h' : (S e).top.wCarry.isW = true := h
    cases hh : (S e).top.wCarry with
    | OFF => rw [hh] at h'; simp [WCarry.isW] at h'
    | W cc =>
      rw [hh] at hx
      obtain ⟨L, hL, -⟩ := hx
      exact ⟨L, hL⟩
  have hyN : (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY).carryLive = false →
      (G (ring.rightNeighbor e)).writer.carry = none := by
    intro h
    have h' : (S (ring.rightNeighbor e)).top.wCarry.isW = false := h
    cases hh : (S (ring.rightNeighbor e)).top.wCarry with
    | OFF => rw [hh] at hy; exact hy
    | W cc => rw [hh] at h'; simp [WCarry.isW] at h'
  have key := carryShapeU DigitLane.writer time e (ring.rightNeighbor e)
    (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
    (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
    (G e).writer (G (ring.rightNeighbor e)).writer hxN hxS hyN
  have hx' : (digitGhostStep ring S G time e e).writer.carry =
      (digitLaneReplay DigitLane.writer time e (ring.rightNeighbor e)
        (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
        (digitLaneView .writer (S (ring.rightNeighbor e))
          (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
        (G e).writer (G (ring.rightNeighbor e)).writer).x.carry := by
    simp [digitGhostStep, digitService]
  have hy' : (digitGhostStep ring S G time e (ring.rightNeighbor e)).writer.carry =
      (digitLaneReplay DigitLane.writer time e (ring.rightNeighbor e)
        (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
        (digitLaneView .writer (S (ring.rightNeighbor e))
          (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
        (G e).writer (G (ring.rightNeighbor e)).writer).y.carry := by
    simp [digitGhostStep, digitService, hne]
  rw [hx', hy']
  exact key

/-- **One audited edge keeps a use property on the ledgers of the target window.**  The property
is assumed to depend only on the time and the operand of the use; it holds on the old ledgers and
on the record of a success or a launch inside the window.

Consumer: `useStructStep` (WidthDigitWriterCurrentUseStruct). -/
theorem windowUses (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) (time R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (hcar : CarryAll S G) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (ring.rightNeighbor (digitSite ring root j))).word).1.beta =
        (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (ring.rightNeighbor (digitSite ring root j))).word).2.beta =
        (S (ring.rightNeighbor (digitSite ring root j))).word.beta)
    (P : DigitUse c n → Prop)
    (hold : ∀ q (L : DigitCarryGhost c n), R ≤ q → q < 2 * R →
      winCarry ring root src G q = some L → ∀ u ∈ L.uses, P u)
    (hadv : ∀ q (u : DigitUse c n), R ≤ q → q + 1 < 2 * R → u.time = time →
      u.operand = (G (digitSite ring root (src + (q + 1)))).writer.input →
      (S (digitSite ring root (src + (q + 1)))).top.wIn.isS = true → P u)
    (hlau : ∀ u : DigitUse c n, u.time = time →
      u.operand = (G (digitSite ring root (src + R))).writer.input →
      (S (digitSite ring root (src + R))).top.wIn.isS = true → P u) :
    ∀ q (L : DigitCarryGhost c n), R ≤ q → q < 2 * R →
      winCarry ring root src (digitGhostStep ring S G time (digitSite ring root j)) q = some L →
      ∀ u ∈ L.uses, P u := by
  intro q L h1 h2 hL u hu
  by_cases hxq : src + q = j
  · subst hxq
    have hx := edgeCarryU ring hn S G time (digitSite ring root (src + q)) hcar
    have hL' : (digitGhostStep ring S G time (digitSite ring root (src + q))
        (digitSite ring root (src + q))).writer.carry = some L := hL
    have hmx : (workerW (S (digitSite ring root (src + q))).word
        (S (ring.rightNeighbor (digitSite ring root (src + q)))).word).betaX =
        (S (digitSite ring root (src + q))).word.beta := hbX
    rcases hx with ⟨hxa, -⟩ | ⟨-, hx0, -⟩ | ⟨hm, -, ⟨u0, hu0, ht, ho, hs⟩, -⟩
    · rcases hxa with h | h
      · rw [h] at hL'; cases hL'
      · rw [h] at hL'
        exact hold q L h1 h2 hL' u hu
    · rw [hx0] at hL'; cases hL'
    · rw [hu0] at hL'
      cases hL'
      have hqR : q = R := by
        by_cases hqR : q = R
        · exact hqR
        · have := hbF q (by omega) h2 hqR
          rw [hmx, this] at hm
          cases hm
      subst hqR
      have hu' : u = u0 := by simpa using hu
      subst hu'
      exact hlau u ht ho hs
  · by_cases hyq : src + q = j + 1
    · obtain ⟨q0, rfl⟩ : ∃ q0, q = q0 + 1 := ⟨q - 1, by omega⟩
      have hj' : j = src + q0 := by omega
      subst hj'
      have hx := edgeCarryU ring hn S G time (digitSite ring root (src + q0)) hcar
      have hL' : (digitGhostStep ring S G time (digitSite ring root (src + q0))
          (ring.rightNeighbor (digitSite ring root (src + q0)))).writer.carry = some L := hL
      have hmy : (workerW (S (digitSite ring root (src + q0))).word
          (S (ring.rightNeighbor (digitSite ring root (src + q0)))).word).betaY =
          (S (ring.rightNeighbor (digitSite ring root (src + q0)))).word.beta := hbY
      rcases hx with ⟨-, hya⟩ | ⟨hm, hx0, hy0, L0, u0, hL0, hy1, ht, ho, hs⟩ | ⟨-, -, -, hyk⟩
      · rcases hya with h | h
        · rw [h] at hL'; cases hL'
        · rw [h] at hL'
          exact hold (q0 + 1) L h1 h2 hL' u hu
      · have hq0 : R ≤ q0 := by
          by_cases hqR : q0 + 1 = R
          · exfalso
            have hb : (S (ring.rightNeighbor (digitSite ring root (src + q0)))).word.beta =
                true := by
              have h := hbR
              rw [← hqR] at h
              exact h
            rw [hmy, hb] at hm
            cases hm
          · omega
        rw [hy1] at hL'
        cases hL'
        rcases List.mem_append.mp hu with hu1 | hu1
        · exact hold q0 L0 hq0 (by omega) hL0 u hu1
        · have hu' : u = u0 := by simpa using hu1
          subst hu'
          exact hadv q0 u hq0 h2 ht ho hs
      · rw [hyk] at hL'
        exact hold (q0 + 1) L h1 h2 hL' u hu
    · have hfar : winCarry ring root src
          (digitGhostStep ring S G time (digitSite ring root j)) q =
          winCarry ring root src G q := by
        unfold winCarry
        have hq : digitSite ring root (src + q) ≠ digitSite ring root j := fun he =>
          hxq (bankRepairDigitSiteInj ring root (by omega) hj he)
        have hq2 : digitSite ring root (src + q) ≠
            ring.rightNeighbor (digitSite ring root j) := by
          intro he
          rw [← bankRepairDigitSiteSucc] at he
          by_cases hjn : j + 1 < n
          · exact hyq (bankRepairDigitSiteInj ring root (by omega) hjn he)
          · have hjn' : j + 1 = n := by omega
            rw [hjn', bankRepairDigitSiteN] at he
            have h0 : digitSite ring root (src + q) = digitSite ring root 0 := he
            have := bankRepairDigitSiteInj ring root (by omega : src + q < n) (by omega : 0 < n)
              h0
            omega
        have hG : digitGhostStep ring S G time (digitSite ring root j)
            (digitSite ring root (src + q)) = G (digitSite ring root (src + q)) := by
          simp [digitGhostStep, hq, hq2]
        rw [hG]
      rw [hfar] at hL
      exact hold q L h1 h2 hL u hu

end Step

end L3

#print axioms L3.carryShapeU
#print axioms L3.edgeCarryU
#print axioms L3.windowUses
