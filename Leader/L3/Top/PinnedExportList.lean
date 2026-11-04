import Leader.L3.Top.PinnedFramesInv

/-!
# Q7 (P.12 preparation): the chronological export list of a run

`topClockConcreteExportsAfter` lists the comparison exports on the edge from the last source
register to the border, after a given time, in log order.  On a reached state this list is exactly
the set of recorded exports with those fields, and its times strictly increase; so an export
whose time lies between the times of two list entries is an entry in between.

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The list of exports is exactly the set of recorded matching exports.

Consumer: `exportList_between`. -/
theorem exportList_mem {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z) (T : Nat)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n) :
    x ∈ topClockConcreteExportsAfter s Z T ↔
      (DigitRecordedExport Z.1.2 x ∧ x.lane = .comparison ∧ T < x.time ∧
        x.source = certSite s (topClockSpan n - 1) ∧
        x.destination = certSite s (topClockSpan n)) := by
  have hinv : FramesInv ring Z.1.2 := by
    unfold topClockReached at hreach
    rw [hreach]
    exact framesInv_run ring C Z.2
  unfold topClockConcreteExportsAfter
  rw [List.mem_filter, List.mem_filterMap]
  constructor
  · rintro ⟨⟨f, hf, hfx⟩, hp⟩
    rw [List.mem_reverse] at hf
    obtain ⟨h1, h2, h3, h4⟩ := hinv.2.2 f hf x hfx
    have hp' : T < x.time ∧ x.source = certSite s (topClockSpan n - 1) ∧
        x.destination = certSite s (topClockSpan n) :=
      Classical.byContradiction (fun hcon => by
        rw [if_neg hcon] at hp
        exact absurd hp (by simp))
    refine ⟨⟨f, hf, h1.symm, h2.symm, ?_⟩, h4, hp'⟩
    rw [h4]; exact hfx
  · rintro ⟨⟨f, hf, h1, h2, h3⟩, hl, hT, hs, hd⟩
    refine ⟨⟨f, List.mem_reverse.2 hf, ?_⟩, ?_⟩
    · rw [hl] at h3; exact h3
    · rw [if_pos ⟨hT, hs, hd⟩]

/-- The times in the list strictly increase.

Consumer: `exportList_between`. -/
theorem exportList_pairwise {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z) (T : Nat) :
    (topClockConcreteExportsAfter s Z T).Pairwise (fun x y => x.time < y.time) := by
  have hinv : FramesInv ring Z.1.2 := by
    unfold topClockReached at hreach
    rw [hreach]
    exact framesInv_run ring C Z.2
  unfold topClockConcreteExportsAfter
  apply List.Pairwise.filter
  rw [List.pairwise_filterMap]
  have hrev : Z.1.2.frames.reverse.Pairwise (fun f g => f.time < g.time) := by
    rw [List.pairwise_reverse]
    exact hinv.2.1
  refine List.Pairwise.imp_of_mem ?_ hrev
  intro f g hf hg hlt x hx y hy
  have hf' := List.mem_reverse.1 hf
  have hg' := List.mem_reverse.1 hg
  have hx' := (hinv.2.2 f hf' x hx).1
  have hy' := (hinv.2.2 g hg' y hy).1
  omega

/-- **An export recorded between two list entries is an entry in between.**

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved). -/
theorem exportList_between {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z) (T : Nat)
    (a b : Nat) (ha : a < (topClockConcreteExportsAfter s Z T).length)
    (hb : b < (topClockConcreteExportsAfter s Z T).length)
    (o : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (ho : DigitRecordedExport Z.1.2 o) (hl : o.lane = .comparison) (hT : T < o.time)
    (hs : o.source = certSite s (topClockSpan n - 1))
    (hd : o.destination = certSite s (topClockSpan n))
    (h1 : (topClockConcreteExportsAfter s Z T)[a].time ≤ o.time)
    (h2 : o.time ≤ (topClockConcreteExportsAfter s Z T)[b].time) :
    ∃ m, ∃ hm : m < (topClockConcreteExportsAfter s Z T).length, a ≤ m ∧ m ≤ b ∧
      (topClockConcreteExportsAfter s Z T)[m] = o := by
  have hmem := (exportList_mem ring C s Z hreach T o).2 ⟨ho, hl, hT, hs, hd⟩
  obtain ⟨m, hm, hmo⟩ := List.getElem_of_mem hmem
  have hpw := List.pairwise_iff_getElem.1 (exportList_pairwise ring C s Z hreach T)
  refine ⟨m, hm, ?_, ?_, hmo⟩
  · exact Classical.byContradiction (fun hcon => by
      have hlt : m < a := by omega
      have := hpw m a hm ha hlt
      rw [hmo] at this
      omega)
  · exact Classical.byContradiction (fun hcon => by
      have hlt : b < m := by omega
      have := hpw b m hb hm hlt
      rw [hmo] at this
      omega)

end MarkedCells
end L3

#print axioms L3.MarkedCells.exportList_between
