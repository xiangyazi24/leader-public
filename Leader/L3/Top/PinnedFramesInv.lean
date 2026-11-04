import Leader.L3.Top.PinnedCarryReplay

/-!
# Q7 (P.12 preparation): the frame log of a run is chronological

Every frame of the audit of a run has a time between `1` and the clock, the times strictly
decrease along the log (newest first), and a comparison export recorded by a frame has the time
of the frame, its edge as source and the right neighbour of the edge as destination.

This is the chronological bookkeeping behind `topClockConcreteExportsAfter`: the exports on one
edge, read in log order, have strictly increasing times.

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The frame-log invariant.

Consumer: `framesInv_run`. -/
def FramesInv {c : Compiled} {n : Nat} (ring : DirectedRing n) (A : DigitAudit c n) : Prop :=
  (∀ f ∈ A.frames, 1 ≤ f.time ∧ f.time ≤ A.clock) ∧
  A.frames.Pairwise (fun f g => g.time < f.time) ∧
  (∀ f ∈ A.frames, ∀ x : DigitExport c n,
    (digitReceiptLane .comparison f.receipt).exported = some x →
      x.time = f.time ∧ x.source = f.edge ∧ x.destination = ring.rightNeighbor f.edge ∧
      x.lane = .comparison)

/-- The initial audit has an empty log.

Consumer: `framesInv_run`. -/
theorem framesInv_initial {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) : FramesInv ring (digitAuditInitial S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf; exact absurd hf (by simp [digitAuditInitial])
  · exact List.Pairwise.nil
  · intro f hf; exact absurd hf (by simp [digitAuditInitial])

/-- One audit step keeps the invariant.

Consumer: `framesInv_run`. -/
theorem framesInv_step {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (h : FramesInv ring A) :
    FramesInv ring (digitAuditStep ring S A e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    simp only [digitAuditStep, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨by simp, by simp [digitAuditStep]⟩
    · have := h1 f hf
      exact ⟨this.1, by simp [digitAuditStep]; omega⟩
  · simp only [digitAuditStep]
    refine List.Pairwise.cons ?_ h2
    intro g hg
    have := (h1 g hg).2
    simp only
    omega
  · intro f hf x hx
    simp only [digitAuditStep, List.mem_cons] at hf
    rcases hf with rfl | hf
    · have hrep := replay_exported_eq .comparison (A.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (S e) (S e).word.beta)
        (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison
      have hx' : (digitLaneReplay .comparison (A.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (S e) (S e).word.beta)
        (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison).exported
          = some x := hx
      rw [hrep] at hx'
      split at hx'
      · have := Option.some.inj hx'
        rw [← this]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact absurd hx' (by simp)
    · exact h3 f hf x hx

/-- **The frame-log invariant holds along every word.**

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved). -/
theorem framesInv_run {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (word : List (Fin n)) : FramesInv ring (topFixedTraceRun ring C word).1.2 := by
  have key : ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), FramesInv ring Z.1.2 →
      FramesInv ring (w.foldl (topFixedTraceNext ring C) Z).1.2 := by
    intro w
    induction w with
    | nil => intro Z h; exact h
    | cons e w ih =>
      intro Z h
      exact ih _ (framesInv_step ring (piD Z.1.1) Z.1.2 e h)
  exact key word _ (framesInv_initial ring _)

end MarkedCells
end L3

#print axioms L3.MarkedCells.framesInv_run
