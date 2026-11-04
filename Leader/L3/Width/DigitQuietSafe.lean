import Leader.L3.Width.DigitQuiet
import Leader.L3.Width.DigitQuietRows
import Leader.L3.Bank.WordCleanWord

/-!
# `QDigit` from the quiet class

`AcceptedReceipts.QDigit ring S` (no future letter changes a visible digit coordinate or reports)
is the quiet class `WidthDigitQuiet` together with `NoDirty`, at a clean word root, given the
one-letter law `QuietStepLaw` of the class: the class is closed, digits are kept, and a report
clears an OLD dirty endpoint (`liveTop_report_source`), so with no dirty bit there is no report;
a new dirty bit is a digit change (`liveTop_dirty_x/y`), so with the digits kept no dirty bit
appears.  The visible word coordinates are fixed by `QWord` (part of `CleanWordAtRoot`, itself
closed by `cleanWordRootPhiStep`).

Consumer: the corrected comparison-entry certificate (R10c-qdigit-notes.md section 4): at the
drained writer comparison cut, `CleanWordAtRoot`, `DigitValuesCorrect` (inside the class) and
`WidthDigitQuiet` replace `QDigit`; the dirty drain of `widthWriterDirtyRank` runs on the identity
of digits given by the law, and `QDigit` is reached at zero dirty count by `qdigitOfQuiet`.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts
open L3.RenewalReferenceClock

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- The left endpoint of a projected letter is the `x` side of `liveTopPair` on the lifted
records.  Consumer: `noDirtyStep`. -/
theorem phiD_at_left (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n) :
    (phiD ring S e) e =
      { word := (pairW (S e).word (S (ring.rightNeighbor e)).word).1
        top := (topD (S e) (S (ring.rightNeighbor e))).x } := by
  simp [phiD, projectedEdge, pairD]

/-- The right endpoint of a projected letter (`n ≥ 2`: the neighbour differs from the site).
Consumer: `noDirtyStep`. -/
theorem phiD_at_right (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (phiD ring S e) (ring.rightNeighbor e) =
      { word := (pairW (S e).word (S (ring.rightNeighbor e)).word).2
        top := (topD (S e) (S (ring.rightNeighbor e))).y } := by
  simp [phiD, projectedEdge, pairD, hne]

/-- A site off the letter is unchanged.  Consumer: `noDirtyStep`. -/
theorem phiD_at_other (ring : DirectedRing n) (S : Fin n → ProjD c) (e i : Fin n)
    (hie : i ≠ e) (hij : i ≠ ring.rightNeighbor e) :
    (phiD ring S e) i = S i := by
  simp [phiD, projectedEdge, hie, hij]

/-- With every digit kept, a letter creates no dirty bit.  Consumer: `qdigitOfQuiet`. -/
theorem noDirtyStep (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hid : ∀ i : Fin n, ((phiD ring S e) i).top.d = (S i).top.d)
    (hnd : NoDirty S) : NoDirty (phiD ring S e) := by
  intro i
  by_cases hie : i = e
  · subst hie
    have hd := hid i
    rw [phiD_at_left] at hd ⊢
    change (liveTopPair c (S i).lift (S (ring.rightNeighbor i)).lift _ _).x.topDirty = false
    change (liveTopPair c (S i).lift (S (ring.rightNeighbor i)).lift _ _).x.d = (S i).top.d at hd
    rw [liveTop_dirty_x]
    have hx : (S i).lift.topDirty = false := hnd i
    have hxd : (S i).lift.d = (S i).top.d := rfl
    simp [hx, hxd, hd]
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have hd := hid (ring.rightNeighbor e)
      rw [phiD_at_right ring S e hne] at hd ⊢
      change (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift _ _).y.topDirty = false
      change (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift _ _).y.d =
        (S (ring.rightNeighbor e)).top.d at hd
      rw [liveTop_dirty_y]
      have hy : (S (ring.rightNeighbor e)).lift.topDirty = false := hnd _
      have hyd : (S (ring.rightNeighbor e)).lift.d = (S (ring.rightNeighbor e)).top.d := rfl
      simp [hy, hyd, hd]
    · rw [phiD_at_other ring S e i hie hij]
      exact hnd i

/-- The right neighbour differs from the site on a ring of at least two sites.  Consumer:
`qdigitOfQuiet`. -/
theorem rightNeighbor_ne (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- **`QDigit` from the quiet class.**  At a clean word root, a quiet state with no dirty bit
is `QDigit`, given the one-letter law of the class.  Consumer: the corrected certificate
(R10c-qdigit-notes.md section 4) and the zero-dirty acceptance of the dirty drain. -/
theorem qdigitOfQuiet (hn : 3 ≤ n) (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (hlaw : QuietStepLaw (c := c) ring root first)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (hnd : NoDirty S)
    (hW : CleanWordAtRoot ring root (wordProjection S)) : QDigit ring S := by
  apply safe_inclusion (phiD ring) (badDigit ring)
    (fun p => WidthDigitQuiet ring root first p ∧ NoDirty p ∧
      CleanWordAtRoot ring root (wordProjection p))
  · intro p hp e
    obtain ⟨hq, hd, hw⟩ := hp
    obtain ⟨hq', hid, hrep⟩ := hlaw p e hq hw.1 hw.2.2
    have hne := rightNeighbor_ne ring (by omega) e
    refine ⟨?_, hq', noDirtyStep ring p e hne hid hd, ?_⟩
    · intro hbad
      rcases hbad with ⟨i, hi⟩ | hr
      · apply hi
        have hvis := qword_visible_fixed ring (wordProjection p) hw.2.2 e i
        rw [← wordProjection_phiD] at hvis
        have hu : ((phiD ring p e) i).word.u = (p i).word.u :=
          congrArg (fun z : Bool × Bool => z.1) hvis
        have hb : ((phiD ring p e) i).word.beta = (p i).word.beta :=
          congrArg (fun z : Bool × Bool => z.2) hvis
        simp only [digitVisible, hu, hb, hid i]
      · rcases hrep hr with h1 | h1
        · exact absurd h1 (by simp [hd e])
        · exact absurd h1 (by simp [hd (ring.rightNeighbor e)])
    · have hstep := cleanWordRootPhiStep hn ring root (wordProjection p) e hw
      rw [← wordProjection_phiD] at hstep
      exact hstep
  · exact ⟨hQ, hnd, hW⟩

end L3.DigitQuiet

#print axioms L3.DigitQuiet.qdigitOfQuiet
#print axioms L3.DigitQuiet.noDirtyStep
