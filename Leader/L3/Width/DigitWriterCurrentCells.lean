import Leader.L3.Width.DigitWriterCurrentWrites
import Leader.L3.Width.DigitCloseBoundary

/-!
# Writer currentness: the cells of a completion on the audit fold

Time-indexed states of the audit fold, the link between the frames of the audit and these states,
and the persistence of a digit across a quiet interval.  With `UsesFramed` this reduces the two cell
facts of `writerBlockValue` (the source cells hold the consumed string, the target cells hold the
string the ledger stores) to

* the source cells `source + j` do not change from the cut on;
* the target cells `target + j` do not change from the time of their use on, and were clean and
  free of the base label `ZERO` at that time.

These are the quiet-interval facts (c); they are not derived here.

Consumer: `writerBlockValueQuiet`, the physical value step of a completion.
-/

namespace L3

open L3.WidthDigit
open L3.CloseBoundary

set_option autoImplicit false

section States

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (start : ref.State)
  (w : List (Fin n))

/-- The coupled state after the first `k` letters of `w` from `start`.

Consumer: `frameLink`, `digitAt`. -/
def stateAt (k : Nat) : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  (w.take k).foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))

/-- The digit of site `i` after the first `k` letters.

Consumer: `frameLink`, `digitAt_quiet`. -/
def digitAt (k : Nat) (i : Fin n) : Fin (compileAdvice (ceilLogTwo n)).topA :=
  ((piD (ref.phys (stateAt ref start w k).1)) i).top.d

/-- Consumer: `frameLink`. -/
theorem drained_fold :
    ∀ (w : List (Fin n)) (p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      ref.drained p.1 → ref.drained (w.foldl (widthDigitAuditNext ref) p).1 := by
  intro w
  induction w with
  | nil => intro p h; exact h
  | cons e w ih => intro p h; exact ih _ (ref.drainedClosed p.1 h e)

/-- **A digit that does not change from step `m` on is the same at the end.**

Consumer: `writerBlockValueQuiet`. -/
theorem digitAt_quiet (i : Fin n) (m : Nat) (hm : m ≤ w.length)
    (hq : ∀ k, m ≤ k → k < w.length → digitAt ref start w (k + 1) i = digitAt ref start w k i) :
    digitAt ref start w w.length i = digitAt ref start w m i := by
  have : ∀ d, m + d ≤ w.length → digitAt ref start w (m + d) i = digitAt ref start w m i := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc, hq (m + d) (by omega) (by omega)]
      exact ih (by omega)
  have h := this (w.length - m) (by omega)
  rw [show m + (w.length - m) = w.length by omega] at h
  exact h

/-- Consumer: `frameLink`. -/
theorem frameLinkAux (hd : ref.drained start) :
    ∀ N : Nat, ∀ w : List (Fin n), w.length = N → ∀ f ∈ (w.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start)))).2.frames,
      1 ≤ f.time ∧ f.time ≤ w.length ∧
        f.old = piD (ref.phys (stateAt ref start w (f.time - 1)).1) ∧
        piD (ref.phys (stateAt ref start w f.time).1) = phiD ring f.old f.edge := by
  intro N
  induction N with
  | zero =>
    intro w hw f hf
    have : w = [] := List.eq_nil_of_length_eq_zero hw
    subst this
    simp [digitAuditInitial] at hf
  | succ N ih =>
    intro w hw f hf
    obtain ⟨w, e, rfl⟩ : ∃ w' e, w = w' ++ [e] := by
      rcases List.eq_nil_or_concat w with h | ⟨w', e, h⟩
      · subst h; simp at hw
      · exact ⟨w', e, by rw [h]; simp⟩
    have hlen : w.length = N := by simp at hw; omega
    have hfold : (w ++ [e]).foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start))) =
        widthDigitAuditNext ref (w.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))) e := by
      simp [List.foldl_append]
    rw [hfold] at hf
    have hdy := drained_fold ref w (start, digitAuditInitial (piD (ref.phys start))) hd
    have hclk : (w.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock = w.length := by
      have := clockFold ref w (start, digitAuditInitial (piD (ref.phys start)))
      have h1 : (w.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock = 0 + w.length := this
      omega
    have hmem : f ∈ (digitAuditStep ring (piD (ref.phys (w.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start)))).1))
        (w.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).2 e).frames := hf
    simp only [digitAuditStep, List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · subst hmem
      have e1 : (w ++ [e]).take w.length = w := by
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have e2 : (w ++ [e]).take (w.length + 1) = w ++ [e] :=
        List.take_of_length_le (by simp)
      refine ⟨by simp, by simp [hclk], ?_, ?_⟩
      · show piD (ref.phys (w.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).1) = _
        simp only [stateAt, hclk, Nat.add_sub_cancel, e1]
      · simp only [stateAt, hclk, e2, hfold]
        exact ref.digitStep _ hdy e
    · obtain ⟨h1, h2, h3, h4⟩ := ih w hlen f hmem
      have t1 : (w ++ [e]).take (f.time - 1) = w.take (f.time - 1) :=
        List.take_append_of_le_length (by omega)
      have t2 : (w ++ [e]).take f.time = w.take f.time :=
        List.take_append_of_le_length h2
      refine ⟨h1, by simp; omega, ?_, ?_⟩
      · rw [h3]; simp only [stateAt, t1]
      · rw [← h4]; simp only [stateAt, t2]

/-- **The frames of the audit fold are the letters of the word.**  Every frame has a time between
`1` and the length, its old state is the physical state one step before, and the state at its time
is the digit projection of the old state on its edge.

Consumer: `writerBlockValueQuiet`. -/
theorem frameLink (hd : ref.drained start) (f : DigitFrame (compileAdvice (ceilLogTwo n)) n)
    (hf : f ∈ (w.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start)))).2.frames) :
    1 ≤ f.time ∧ f.time ≤ w.length ∧
      f.old = piD (ref.phys (stateAt ref start w (f.time - 1)).1) ∧
      piD (ref.phys (stateAt ref start w f.time).1) = phiD ring f.old f.edge :=
  frameLinkAux ref start hd w.length w rfl f hf

end States

end L3

#print axioms L3.frameLink
#print axioms L3.digitAt_quiet
