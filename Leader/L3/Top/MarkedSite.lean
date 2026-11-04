import Leader.L3.Top.PortPhase
import Leader.L3.Top.MarkedCells
import Leader.L3.Top.MarkedLinkQI
import Leader.L3.Top.MarkedLinkQC

/-!
# Q7: one fixed-trace edge acts on the abstract site cells as `pair`

`siteCell Z v` is the abstract class of the checker input and of the comparison
carry (physical `qCarry` and its audit ledger) of site `v`.  One edge `e` of
`topFixedTraceNext` sends the cells of `e` and `e + 1` to `pair` (or, at a
marker responder, to the border port rows) and leaves every other site alone.

Consumer: `Leader/L3/Top/MarkedLink.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The abstract class of site `v` at the fixed-trace state `Z`.

Consumer: `link_step`. -/
def siteCell {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) : Cell :=
  { i := absIn (Z.1.1 v).qIn
    c := absCar (Z.1.1 v).qCarry (Z.1.2.current v).comparison.carry }

/-- The carry class is off exactly when the physical carry is off.

Consumer: `link_step`. -/
theorem absCar_off {c : Compiled} {n : Nat} (q : QCarry)
    (g : Option (DigitCarryGhost c n)) : absCar q g = .off ↔ q = .OFF := by
  cases q <;> cases g <;> simp [absCar] <;> split <;> simp

/-- Offness of a site cell matches its physical carry.

Consumer: `link_step`. -/
theorem siteCell_offMatch {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    OffMatch (Z.1.1 v).qCarry (siteCell Z v).c := by
  unfold OffMatch siteCell
  exact absCar_off _ _

/-- The owner checker inputs are the copied QI block.

Consumer: `link_step`. -/
theorem owner_qIn {n : Nat} (ring : DirectedRing n) (D : HeadlineConfiguration n) (e : Fin n)
    (hxl : (D e).l = false) (hyl : (D (ring.rightNeighbor e)).l = false) :
    (topPortLiteralTopOwner ring D e).x.qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (D e) (D (ring.rightNeighbor e))).1.iX ∧
    (topPortLiteralTopOwner ring D e).y.qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (D e) (D (ring.rightNeighbor e))).1.iY := by
  unfold topPortLiteralTopOwner
  exact liveTopPair_qIn _ _ _ _ _ hxl hyl

/-- The owner checker carries are the copied QC block.

Consumer: `link_step`. -/
theorem owner_qCarry {n : Nat} (ring : DirectedRing n) (D : HeadlineConfiguration n) (e : Fin n)
    (hxl : (D e).l = false) (hyl : (D (ring.rightNeighbor e)).l = false) :
    (topPortLiteralTopOwner ring D e).x.qCarry =
      (qcPhys (compileAdvice (ceilLogTwo n)) (D e) (D (ring.rightNeighbor e))).1 ∧
    (topPortLiteralTopOwner ring D e).y.qCarry =
      (qcPhys (compileAdvice (ceilLogTwo n)) (D e) (D (ring.rightNeighbor e))).2.1 := by
  unfold topPortLiteralTopOwner
  exact liveTopPair_qCarry _ _ _ _ _ hxl hyl

/-- Settledness of a site cell is that of its physical input.

Consumer: `link_step`. -/
theorem isS_link {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    (siteCell Z v).i.isS = (Z.1.1 v).qIn.isS := by
  rcases h : (Z.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;> (try cases t) <;>
    simp [siteCell, absIn, Inp.isS, InTok.isS, h]

/-- The ghost carry after the edge, at the source, in terms of `carry_link`.

Consumer: `link_step`. -/
theorem next_ghost_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    ((topFixedTraceNext ring C Z e).1.2.current e).comparison.carry =
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).x.carry := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, ProjD.ofAgent,
    ProjW.ofAgent]

/-- The responder ledger after an edge is the lane replay output.

Consumer: `link_step`. -/
theorem next_ghost_responder {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.carry =
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).y.carry := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, ProjD.ofAgent,
    ProjW.ofAgent, hne]

/-- An unrelated site keeps its ghost.

Consumer: `link_step`. -/
theorem next_ghost_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e v : Fin n) (hx : v ≠ e) (hy : v ≠ ring.rightNeighbor e) :
    ((topFixedTraceNext ring C Z e).1.2.current v) = Z.1.2.current v := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, hx, hy]

/-- The source of the edge.

Consumer: `link_step`. -/
theorem siteCell_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false) :
    siteCell (topFixedTraceNext ring C Z e) e =
      (pair (Z.1.1 e).beta (Z.1.1 (ring.rightNeighbor e)).beta
        (siteCell Z e) (siteCell Z (ring.rightNeighbor e))).1 := by
  have hsrc := topPortLiteralSourceFields ring C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hcarry := carry_link (n := n) (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    ((Z.1.2.current e).comparison) ((Z.1.2.current (ring.rightNeighbor e)).comparison)
    (siteCell Z e) (siteCell Z (ring.rightNeighbor e))
    (isS_link Z e) (isS_link Z _) rfl rfl
  have hphys : (topFixedTraceNext ring C Z e).1.1 e =
      topFixedPublicNext ring C Z.1.1 e e := rfl
  have hin : absIn (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
        (Z.1.1 (ring.rightNeighbor e))).1.iX =
      (inSlots (Z.1.1 e).beta (Z.1.1 (ring.rightNeighbor e)).beta
        (siteCell Z e) (siteCell Z (ring.rightNeighbor e))).iX := by
    cases hb : (Z.1.1 (ring.rightNeighbor e)).beta
    · exact (qi_link_interior (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
        (Z.1.1 (ring.rightNeighbor e)) hxl hyl hb (siteCell Z e)
        (siteCell Z (ring.rightNeighbor e)) rfl rfl
        (siteCell_offMatch Z e) (siteCell_offMatch Z _)).1
    · exact (qi_link_terminal (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
        (Z.1.1 (ring.rightNeighbor e)) hxl hyl hb (siteCell Z e)
        (siteCell Z (ring.rightNeighbor e)) rfl rfl
        (siteCell_offMatch Z e) (siteCell_offMatch Z _)).1
  unfold siteCell
  simp only [pair]
  rw [hphys, hsrc.1, hsrc.2.1, hq.1, hk.1, next_ghost_source]
  simp only [Cell.mk.injEq]
  exact ⟨hin, hcarry.1⟩

/-- On a ring of two or more sites the right neighbour differs.

Consumer: `link_step`. -/
theorem rightNeighbor_ne {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at h1
  have he := e.isLt
  rcases Nat.lt_or_ge (e.val + 1) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h2] at h1; omega
  · have h3 : e.val + 1 = n := by omega
    rw [h3, Nat.mod_self] at h1; omega

/-- The abstract terminal edge leaves the responder carry alone.

Consumer: `link_step`. -/
theorem carries_terminal_y (b : Bool) (x y : Cell) : (carries b true x y).2 = y.c := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [carries, Inp.isS]

/-- Port cleanup keeps the carry class.

Consumer: `link_step`. -/
theorem portClean_c (c : Cell) : (portClean c).c = c.c := by
  unfold portClean; split <;> rfl

/-- Port acceptance keeps the carry class.

Consumer: `link_step`. -/
theorem portAccept_c (t : Bool) (c : Cell) : (portAccept t c).c = c.c := by
  unfold portAccept; split <;> simp_all

/-- The interior responder is the second output of `pair`.

Consumer: `link_step`. -/
theorem siteCell_responder_interior {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    siteCell (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) =
      (pair (Z.1.1 e).beta false
        (siteCell Z e) (siteCell Z (ring.rightNeighbor e))).2 := by
  have hresp := topPortLiteralResponderFields ring hn C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hne : ring.rightNeighbor e ≠ e := rightNeighbor_ne ring hn e
  have hcarry := carry_link (n := n) (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    ((Z.1.2.current e).comparison) ((Z.1.2.current (ring.rightNeighbor e)).comparison)
    (siteCell Z e) (siteCell Z (ring.rightNeighbor e))
    (isS_link Z e) (isS_link Z _) rfl rfl
  have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
  have hin := (qi_link_interior (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
        (Z.1.1 (ring.rightNeighbor e)) hxl hyl hyb (siteCell Z e)
        (siteCell Z (ring.rightNeighbor e)) rfl rfl
        (siteCell_offMatch Z e) (siteCell_offMatch Z _)).2
  unfold siteCell
  simp only [pair]
  rw [hphys, hresp.1, hresp.2.1, hq.2, hk.2, next_ghost_responder ring C Z e hne]
  rw [hyb] at hcarry ⊢
  simp only [Cell.mk.injEq]
  exact ⟨hin, hcarry.2⟩

/-- The marker responder is cleaned or accepts.

Consumer: `link_step`. -/
theorem siteCell_responder_terminal {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true) :
    siteCell (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) =
        portClean (siteCell Z (ring.rightNeighbor e)) ∨
      ∃ t, siteCell (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) =
        portAccept t (siteCell Z (ring.rightNeighbor e)) := by
  have hresp := topPortLiteralResponderFields ring hn C Z.1.1 e
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hk := owner_qCarry ring Z.1.1 e hxl hyl
  have hne : ring.rightNeighbor e ≠ e := rightNeighbor_ne ring hn e
  have hcarry := carry_link (n := n) (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    ((Z.1.2.current e).comparison) ((Z.1.2.current (ring.rightNeighbor e)).comparison)
    (siteCell Z e) (siteCell Z (ring.rightNeighbor e))
    (isS_link Z e) (isS_link Z _) rfl rfl
  have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
  have hin := (qi_link_terminal (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
        (Z.1.1 (ring.rightNeighbor e)) hxl hyl hyb (siteCell Z e)
        (siteCell Z (ring.rightNeighbor e)) rfl rfl
        (siteCell_offMatch Z e) (siteCell_offMatch Z _)).2
  have hcell : siteCell (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) =
      { i := absIn (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
            (Z.1.1 (ring.rightNeighbor e))).1.iY,
        c := (siteCell Z (ring.rightNeighbor e)).c } := by
    unfold siteCell
    rw [hphys, hresp.1, hresp.2.1, hq.2, hk.2, next_ghost_responder ring C Z e hne]
    rw [hyb] at hcarry ⊢
    have h2 := hcarry.2
    rw [carries_terminal_y] at h2
    simp only [Cell.mk.injEq, true_and]
    simpa [siteCell] using h2
  rw [hcell]
  rcases hin with h | ⟨t, h⟩
  · left
    rw [h]
    cases hp : portClean (siteCell Z (ring.rightNeighbor e)) with
    | mk pi pc =>
        have := portClean_c (siteCell Z (ring.rightNeighbor e))
        rw [hp] at this
        simp only at this
        rw [hp] at h
        simp only at h
        simp [h, this]
  · right
    refine ⟨t, ?_⟩
    rw [h]
    cases hp : portAccept t (siteCell Z (ring.rightNeighbor e)) with
    | mk pi pc =>
        have := portAccept_c t (siteCell Z (ring.rightNeighbor e))
        rw [hp] at this
        simp only at this
        simp [this]

/-- An unrelated site cell is unchanged.

Consumer: `link_step`. -/
theorem siteCell_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e v : Fin n) (hx : v ≠ e) (hy : v ≠ ring.rightNeighbor e) :
    siteCell (topFixedTraceNext ring C Z e) v = siteCell Z v := by
  have haway := topPortLiteralAwayFields ring C Z.1.1 e v hx hy
  have hg := next_ghost_away ring C Z e v hx hy
  unfold siteCell
  have hphys : (topFixedTraceNext ring C Z e).1.1 v = topFixedPublicNext ring C Z.1.1 e v := rfl
  rw [hphys, haway.1, haway.2.1, hg]

end MarkedCells
end L3

#print axioms L3.MarkedCells.siteCell_source
#print axioms L3.MarkedCells.siteCell_responder_interior
#print axioms L3.MarkedCells.siteCell_responder_terminal
#print axioms L3.MarkedCells.siteCell_away
