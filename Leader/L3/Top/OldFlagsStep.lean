import Leader.L3.Top.OldFlags
import Leader.L3.Top.MarkedLink
import Leader.L3.Top.OldMark

/-!
# Q7: the old-pending flags move with the pending inputs

Consumer: `Leader/L3/Top/OldMarkStep.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- The register `v` holds a pending input whose atom is not post-anchor.

Consumer: `oldFlag`. -/
def oldSite {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (v : Fin n) : Prop :=
  (Z.1.1 v).qIn.isP = true ∧
    ¬ topClockPostAnchor s Z τ ((Z.1.2.current v).comparison.input)

/-- The old-pending flag of target register `j`.

Consumer: `old_next_window`. -/
noncomputable def oldFlag {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n)
    (j : Nat) : Bool :=
  decide (j < topClockSpan n ∧ oldSite s τ Z (winSite s j))

/-- Auxiliary fact `oldFlag_isP` of the old-pending repair.

Consumer: `old_next_window`. -/
theorem oldFlag_isP {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (j : Nat)
    (h : oldFlag s τ Z j = true) : (cellOf s Z j).i.isP = true := by
  unfold oldFlag at h
  have := of_decide_eq_true h
  unfold cellOf
  rw [siteCell_isP]
  exact this.2.1

/-- Auxiliary fact `oldFlag_iff` of the old-pending repair.

Consumer: `old_next_window`. -/
theorem oldFlag_iff {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (j : Nat) :
    oldFlag s τ Z j = true ↔ j < topClockSpan n ∧ oldSite s τ Z (winSite s j) := by
  unfold oldFlag
  simp

/-- Auxiliary fact `next_input_source` of the old-pending repair.

Consumer: `old_next_window`. -/
theorem next_input_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    ((topFixedTraceNext ring C Z e).1.2.current e).comparison.input =
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).x.input := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, ProjD.ofAgent,
    ProjW.ofAgent]

/-- Auxiliary fact `next_input_responder` of the old-pending repair.

Consumer: `old_next_window`. -/
theorem next_input_responder {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).y.input := by
  simp [topFixedTraceNext, digitAuditStep, digitGhostStep, digitService, piD, ProjD.ofAgent,
    ProjW.ofAgent, hne]

/-- Cell-level: a settled-or-pending source output comes from a pending source.

Consumer: `old_source`. -/
theorem pair_src_isP (b t : Bool) (x y : Cell) (h : (pair b t x y).1.i.isP = true) :
    x.i.isP = true := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;> cases t <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- Cell-level: a pending responder output comes from a pending responder or a pending
source moving in.

Consumer: `old_responder`. -/
theorem pair_resp_isP (b : Bool) (x y : Cell) (h : (pair b false x y).2.i.isP = true) :
    y.i.isP = true ∨ (x.i.isP = true ∧ y.i.isP = false) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- The source of an edge keeps its flag from the old source.

Consumer: `old_next_window`. -/
theorem old_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (h : oldSite s τ (topFixedTraceNext ring C Z e) e) : oldSite s τ Z e := by
  obtain ⟨hP, hnp⟩ := h
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hsrc := topPortLiteralSourceFields ring C Z.1.1 e
  have hphys : (topFixedTraceNext ring C Z e).1.1 e = topFixedPublicNext ring C Z.1.1 e e := rfl
  rw [hphys, hsrc.1, hq.1] at hP
  have hx : (Z.1.1 e).qIn.isP = true := by
    have h1 := siteCell_source ring C Z e hxl hyl
    have h2 : (siteCell (topFixedTraceNext ring C Z e) e).i.isP = true := by
      rw [siteCell_isP]
      rw [hphys, hsrc.1, hq.1]; exact hP
    rw [h1] at h2
    have := pair_src_isP _ _ _ _ h2
    rwa [siteCell_isP] at this
  refine ⟨hx, fun hpost => hnp ?_⟩
  have hg := (input_link (Z.1.2.clock + 1) e (ring.rightNeighbor e) (Z.1.1 e)
    (Z.1.1 (ring.rightNeighbor e)) hxl hyl (Z.1.2.current e).comparison
    (Z.1.2.current (ring.rightNeighbor e)).comparison).1 hP
  rw [next_input_source, hg]
  exact post_next ring C s Z e τ _ hpost

/-- Other registers only lose flags.

Consumer: `old_next_window`. -/
theorem old_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (e v : Fin n) (hx : v ≠ e)
    (hy : v ≠ ring.rightNeighbor e) (h : oldSite s τ (topFixedTraceNext ring C Z e) v) :
    oldSite s τ Z v := by
  obtain ⟨hP, hnp⟩ := h
  have haway := topPortLiteralAwayFields ring C Z.1.1 e v hx hy
  have hphys : (topFixedTraceNext ring C Z e).1.1 v = topFixedPublicNext ring C Z.1.1 e v := rfl
  have hg := next_ghost_away ring C Z e v hx hy
  rw [hphys, haway.1] at hP
  refine ⟨hP, fun hpost => hnp ?_⟩
  rw [hg]
  exact post_next ring C s Z e τ _ hpost

/-- The responder of an edge: a flag is inherited from the old responder or the old
source, and a packet accepted at the border carries a post-anchor atom.

Consumer: `old_next_window`. -/
theorem old_responder {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (C : HeadlineConfiguration n)
    (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hmode : (Z.1.1 (ring.rightNeighbor e)).beta = false ∨
      (τ ≤ Z.1.2.clock ∧ e = certSite s (topClockSpan n - 1) ∧
        ring.rightNeighbor e = certSite s (topClockSpan n)))
    (h : oldSite s τ (topFixedTraceNext ring C Z e) (ring.rightNeighbor e)) :
    ((Z.1.1 (ring.rightNeighbor e)).qIn.isP = true ∧
        oldSite s τ Z (ring.rightNeighbor e)) ∨
      ((Z.1.1 (ring.rightNeighbor e)).beta = false ∧
        (Z.1.1 (ring.rightNeighbor e)).qIn.isP = false ∧
        (Z.1.1 e).qIn.isP = true ∧ oldSite s τ Z e) := by
  obtain ⟨hP, hnp⟩ := h
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hresp := topPortLiteralResponderFields ring hn C Z.1.1 e
  have hne := rightNeighbor_ne ring hn e
  have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
  rw [hphys, hresp.1, hq.2] at hP
  have hg := (input_link (Z.1.2.clock + 1) e (ring.rightNeighbor e) (Z.1.1 e)
    (Z.1.1 (ring.rightNeighbor e)) hxl hyl (Z.1.2.current e).comparison
    (Z.1.2.current (ring.rightNeighbor e)).comparison).2 hP
  rw [next_input_responder ring C Z e hne] at hnp
  rcases hg with ⟨h1, h2⟩ | ⟨hb, h1, h2, h3⟩ | ⟨hb, h2, ex, hex, hop, htime, hsrc, hdst⟩
  · left
    refine ⟨h1, h1, fun hpost => hnp ?_⟩
    rw [h2]
    exact post_next ring C s Z e τ _ hpost
  · right
    refine ⟨hb, h1, h2, h2, fun hpost => hnp ?_⟩
    rw [h3]
    exact post_next ring C s Z e τ _ hpost
  · exfalso
    rcases hmode with hb' | ⟨hτ, he, hy⟩
    · rw [hb'] at hb; exact absurd hb (by decide)
    · apply hnp
      rw [h2, ← hop]
      exact post_accept ring C s Z e τ hτ he hy ex hex htime hsrc hdst

end MarkedCells
end L3

#print axioms L3.MarkedCells.old_source
#print axioms L3.MarkedCells.old_away
#print axioms L3.MarkedCells.old_responder
