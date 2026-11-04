import Leader.L3.Width.DigitComparisonCertificateWord
import Leader.L3.Width.DigitWriterOrderedClose
import Leader.L3.Width.DigitQuiet

/-!
# The entrance into the quiet class, boundary part

At a writer comparison cut of a boundary reference the root, layout and leading-segment clauses
of `WidthDigitQuiet` follow from the word (`cleanWordOfWriterComparisonCut`, the delimiter layout
`widthCleanBoundaryDelimiters`) and the boundary leader receipt carried by the cut
(`WidthDigitLeaderReceipt`): `quietBoundaryOfCut`.  The remaining clauses (first segment, base
labels, values, pairs, fragment) are mapped onto the tree's post-strict and window classes in
research/lean-l3/ledgers/R10c-qdigit-notes.md section 7 and are not proved here.
-/

namespace L3.DigitQuiet

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WriterValueCuts
open L3.AcceptedReceipts
open L3.WriterCertificate

set_option autoImplicit false

variable {n : Nat} {ring : DirectedRing n}

/-- The singleton class is kept along every word from a start.  Consumer:
`quietBoundaryOfCut`. -/
theorem singletonFold (ref : WidthDigitReference ring) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : ref.State), ref.singleton root z →
      ref.singleton root (word.foldl ref.next z) := by
  intro word
  induction word with
  | nil => intro z h; exact h
  | cons e rest ih =>
      intro z h
      exact ih (ref.next z e) (ref.singletonClosed root z h e)

/-- **The boundary clauses of the quiet class at the cut**: the unique root, the delimiter
layout at some `first ≥ 2`, and the leading segment (empty outputs, settled non-tail inputs, no
live carry) at the fixed root of the cut.  Consumer: the entrance `WidthWriterQuietAtCut`
(open: the remaining clauses). -/
theorem quietBoundaryOfCut (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hcut : WidthWriterComparisonCut ref.toWidthDigitReference z)
    (root : Fin n) (hfixed : WFixedRoot ring root (piW (ref.phys z))) :
    ∃ first : Nat,
      (∀ i : Fin n, (piD (ref.phys z) i).word.native.l = true ↔ i = root) ∧
      (2 ≤ first ∧ first < n ∧
        ∀ k : Nat, 0 < k → k < n →
          ((piD (ref.phys z) (digitSite ring root k)).word.beta = true ↔
            first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0)) ∧
      (∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
        (view ring root (piD (ref.phys z)) lane k).out = .E ∧
        DigitLeadingInput (view ring root (piD (ref.phys z)) lane k).input ∧
        (view ring root (piD (ref.phys z)) lane k).carryLive = false) := by
  -- the word and the singleton at the cut
  obtain ⟨start, word, root₀, audit, retired, restart, cmp, hstart, hrun, hfixed₀, -, -, -,
    hleader⟩ := hcut
  have hz : z = word.foldl ref.next start := by
    have := widthAuditFoldFst ref.toWidthDigitReference word start
      (digitAuditInitial (piD (ref.phys start)))
    rw [hrun] at this
    exact this
  obtain ⟨root', hroot'⟩ := ref.startClean start hstart
  have hD := ref.startDrained start hstart
  have hW := widthCutWordRun ref.toWidthDigitReference hn root' word start hD hroot'
  rw [← hz] at hW
  have hroot : root' = root := by
    exact hfixed.2.1 root' hW.1.1
  subst hroot
  have hsing : ref.singleton root' z := by
    rw [hz]
    exact singletonFold ref.toWidthDigitReference root' word start
      (ref.singletonOfStart root' start hstart hroot'.1)
  have hL : WidthBoundaryDigitLayoutValues ref root' z :=
    ⟨⟨hsing, hW.2.2⟩, hW.2.1⟩
  obtain ⟨first, ht, hf, hb⟩ := widthCleanBoundaryDelimiters ref hn root' z hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hlead := L3.WriterOrderedClose.leadWidthBand (n := n) hn
  refine ⟨first, ?_, ⟨by omega, by omega, hb⟩, ?_⟩
  · intro i
    constructor
    · intro hi
      exact hfixed.2.1 i hi
    · intro hi
      subst hi
      exact hfixed.1
  · -- the leading clause from the boundary leader receipt
    obtain ⟨root'', hfixed'', hrec⟩ := hleader
    have hr : root'' = root' := hfixed.2.1 root'' hfixed''.1
    subst hr
    obtain ⟨first', stop, ⟨⟨⟨hpos', hlt', hbeta'⟩, hbelow'⟩, -⟩, hleadclause, -⟩ := hrec.1
    have hfirst : first' = first := by
      have h1 : first ≤ first' := ((hb first' hpos' hlt').1 hbeta').1
      by_cases hlt : first < first'
      · have := hbelow' first (by omega) hlt
        have hbf : (piD (ref.phys z) (digitSite ring root'' first)).word.beta = true :=
          (hb first (by omega) (by omega)).2 ⟨Nat.le_refl _, by simp⟩
        rw [this] at hbf
        exact absurd hbf (by simp)
      · omega
    intro lane k hk hkf
    have hkf' : k < first' := by omega
    obtain ⟨hout, hcarry, hinput⟩ := hleadclause lane k hk hkf'
    exact ⟨hout, hinput, hcarry⟩

end L3.DigitQuiet

#print axioms L3.DigitQuiet.quietBoundaryOfCut
