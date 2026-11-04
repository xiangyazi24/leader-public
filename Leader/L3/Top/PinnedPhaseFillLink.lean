import Leader.L3.Top.PinnedPhaseFillNominate
import Leader.L3.Top.PinnedPrepClasses

/-!
# Q7 (P.12 preparation, lemma 3, concrete layer): the fill invariant of a labelled state

The pending-or-settled labelled window invariant of a state (`PuLinv`, `PuAllAt`) together with
the pure source stream gives the fill invariant of the abstract window: the tail bits of the
packets in the window are the tail pattern of consecutive serials, starting at the residue
`aOf = (|Q| - p) mod r` of the index of the oldest outstanding serial.

Consumer: `Leader/L3/Top/PinnedPhaseFillCost.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The tail bit of a label: the tail flag of its pending token.

Consumer: `fillInv_of_pu`. -/
def tailOfLab {n : Nat} (l : PaLabel n) : Bool :=
  match l.2 with
  | .P _ t => t
  | _ => false

/-- A map commutes with the reading.

Consumer: `fillInv_of_pu`. -/
theorem ordLab_map {α β : Type} (f : α → β) (o : Nat → Bool) (ℓ : Nat → α) :
    ∀ k, (ordLab o ℓ k).map f = ordLab o (fun j => f (ℓ j)) k
  | 0 => rfl
  | k + 1 => by
      simp only [ordLab, List.map_append]
      rw [ordLab_map f o ℓ k]
      by_cases h : o k = true <;> simp [h]

/-- The residue of the index of the oldest outstanding serial.

Consumer: `fillInv_of_pu`. -/
noncomputable def aOf {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat) : Nat :=
  ((paQ s Z τ).length - fcnt (topClockSpan n) (cellOf s Z)) % topClockSpan n

/-- The tail bit of a flagged register is the tail flag of its label.

Consumer: `fillInv_of_pu`. -/
theorem tailBit_cell {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat)
    (h : puNonE (cellOf s Z j).i = true) : tailBit (cellOf s Z j) = tailOfLab (paLabSettled s Z j) := by
  unfold cellOf siteCell paLabSettled tailOfLab tailBit puTok
  unfold cellOf siteCell puNonE at h
  rcases (Z.1.1 (winSite s j)).qIn with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;>
    (try cases t) <;>
    simp [absIn, Inp.isP, Inp.isS] at h ⊢

/-- The tail bits of the accepted queue are the tail pattern of the pure stream.

Consumer: `fillInv_of_pu`. -/
theorem paQ_tails {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hpure : topClockConcretePureStream s Z anchor) :
    (paQ s Z anchor.time).map tailOfLab =
      (List.range (paQ s Z anchor.time).length).map
        (fun i => decide (i % topClockSpan n = topClockSpan n - 1)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hlen : (paQ s Z anchor.time).length = (topClockConcreteExportsAfter s Z anchor.time).length := by
      unfold paQ; simp
    have h1' : i < (paQ s Z anchor.time).length := by simpa using h1
    have hi : i < (topClockConcreteExportsAfter s Z anchor.time).length := by omega
    obtain ⟨sample, _, _, _, htail, _, _, htl⟩ := hpure ⟨i, hi⟩
    have hq : (paQ s Z anchor.time)[i]? =
        some ((topClockConcreteExportAt s Z anchor.time ⟨i, hi⟩).operand,
          InTok.P (topClockConcreteExportAt s Z anchor.time ⟨i, hi⟩).value
            (topClockConcreteExportAt s Z anchor.time ⟨i, hi⟩).tail) := by
      unfold paQ
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    have hex : (paQ s Z anchor.time)[i] =
        ((topClockConcreteExportAt s Z anchor.time ⟨i, hi⟩).operand,
          InTok.P (topClockConcreteExportAt s Z anchor.time ⟨i, hi⟩).value
            (topClockConcreteExportAt s Z anchor.time ⟨i, hi⟩).tail) := by
      have h3 := List.getElem?_eq_getElem h1'
      rw [hq] at h3
      exact (Option.some.inj h3).symm
    simp only [List.getElem_map, hex, tailOfLab, List.getElem_range]
    rw [htl, htail]
    by_cases hh : i % topClockSpan n = topClockSpan n - 1 <;> simp [hh]

/-- The drop of a mapped range.

Consumer: `fillInv_of_pu`. -/
theorem drop_map_range (f : Nat → Bool) (N k : Nat) :
    ((List.range N).map f).drop k = (List.range (N - k)).map (fun i => f (k + i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]

/-- **The fill invariant of a labelled state.**

Consumer: `fillReg_step`. -/
theorem fillInv_of_pu {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hpure : topClockConcretePureStream s Z anchor)
    (hl : PuLinv s Z anchor.time) (ha : PuAllAt s Z anchor.time)
    (hs : FillShape (topClockSpan n) (cellOf s Z)) :
    FillInv (topClockSpan n) (cellOf s Z) (aOf s Z anchor.time) ∧
    fcnt (topClockSpan n) (cellOf s Z) ≤ (paQ s Z anchor.time).length := by
  obtain ⟨hfree, hI, k, hk, hlist⟩ := hl
  have hflag : ∀ j, j < topClockSpan n →
      puNonE (cellOf s Z j).i = paFlagSettled s Z anchor.time j := by
    intro j hj
    apply Bool.eq_iff_iff.2
    constructor
    · intro h; exact ha j hj h
    · intro h; exact hI j hj h
  have hr0 : 0 < topClockSpan n := by
    obtain ⟨m, hm, _⟩ := hs; omega
  have htl : tl (topClockSpan n) (cellOf s Z) =
      ((paQ s Z anchor.time).drop k).map tailOfLab := by
    rw [← hlist, ordLab_map]
    unfold tl
    apply ordLab_congr
    · intro j hj; exact hflag j hj
    · intro j hj hj1
      exact tailBit_cell s Z j hj1
  have hlen := tl_length (topClockSpan n) (cellOf s Z)
  rw [htl, List.length_map, List.length_drop] at hlen
  have hcnt : fcnt (topClockSpan n) (cellOf s Z) = (paQ s Z anchor.time).length - k := hlen.symm
  have hmod : aOf s Z anchor.time = k % topClockSpan n := by
    unfold aOf
    rw [hcnt]
    congr 1
    omega
  refine ⟨⟨hs, ?_⟩, by omega⟩
  rw [htl, hmod, hcnt, List.map_drop, paQ_tails s Z anchor hpure, drop_map_range, pat_mod]
  unfold pat
  rfl

end MarkedCells
end L3

#print axioms L3.MarkedCells.fillInv_of_pu
