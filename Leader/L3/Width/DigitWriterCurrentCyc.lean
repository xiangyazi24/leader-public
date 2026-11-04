import Leader.L3.Width.DigitWriterCurrentAgedUses
import Leader.L3.StageM.EntryCyc

/-!
# Writer currentness: the cycle class at a recorded writer completion, at every boundary reference

`L3.StageMEntryCyc.wCycStartOfCompletion` puts the masked writer lane of a pair in the cycle class
`CohortCycIn` right after the export of the tail of a recorded completion, on a coupled run from a
start with the run invariant.  This module replays the proof of `cycStartAfterStrict` on the clean
run from a start (no first-zero data, which that proof does not use), and carries the cycle class
to the end of the run (`cycPersist`).  The result holds at every `WidthBoundaryReference`, SMALL
and BANK alike; `writerCycOfBank` (BANK only, through `strictCompletionCyc`) is not needed.

Consumer: `writerEntryCoreOfAgedCore`, `writersCurrentOfAgedCore`.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
open L3.StageMEntryRun
open L3.StageMEntryCyc
open L3.ValueWaveClose
open L3.CloseEntry

variable {n : Nat} {ring : DirectedRing n}

/-- **The cycle class persists along any word** from a state with the marker layout.

Consumer: `writerCycOfStrict`. -/
theorem cycPersist (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (w : List (Fin n)) :
    ∀ y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthCohortLayout ref root src R y.1 →
      (∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
        CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys y.1))) g o) →
      ∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
        CohortCycIn R j (cohortProj ring root lane src R
          (piD (ref.phys (w.foldl (widthDigitAuditNext ref) y).1))) g o := by
  induction w with
  | nil => intro y _ h; exact h
  | cons e rest ih =>
    intro y hl ⟨jj, g, o, hcyc⟩
    obtain ⟨hl', hproj⟩ := widthCohortStep ref hfix hn root lane src R hR hsrc hend y.1 hl e
    apply ih (widthDigitAuditNext ref y e) hl'
    show ∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat), CohortCycIn R j
      (cohortProj ring root lane src R (piD (ref.phys (ref.next y.1 e)))) g o
    rw [hproj]
    rcases cohortCycStep hcyc (cohortEdgeOf root src R e) with ⟨o', -, h', -⟩ | h'
    · exact ⟨jj, _, o', h'⟩
    · exact ⟨jj + 1, _, 0, h'⟩

/-- **A recorded writer completion of a complete pair puts the writer lane in the cycle class at
the end of the clean run** (any boundary reference).

Consumer: `writerEntryCoreOfAgedCore`. -/
theorem writerCycOfStrict (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hst : ref.start start) (hs : ref.singleton root start) (u : List (Fin n))
    (src : Nat) (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (h2 : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n)
    (hcomp : DigitCompletion ring
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2
      root src (src + valueSpan n) DigitLane.writer 0 tm) :
    ∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
      CohortCycIn (valueSpan n) j (cohortProj ring root DigitLane.writer src (valueSpan n)
        (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1))) g o := by
  have hR := valueSpanTwo hn
  have hW : WFixedRoot ring root (piW (ref.phys start)) := ref.singletonFixed root start hs
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root hW.1
  subst hr
  have hstart : (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.start = piD (ref.phys start) := by
    rw [L3.WriterReceipts.widthAuditStartFold]
    rfl
  obtain ⟨first0, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  obtain ⟨⟨⟨⟨⟨-, -, hbeta⟩, -⟩, -⟩, -⟩, -⟩ := id hcomp
  rw [hstart] at hbeta
  obtain ⟨hfs, hmod⟩ := (hb src (by omega) (by omega)).1 hbeta
  have hf : DigitFirstDelimiter ring root (piD (ref.phys start)) first0 := by
    refine ⟨⟨by omega, by omega, (hb first0 (by omega) (by omega)).2 ⟨Nat.le_refl _, by simp⟩⟩,
      fun k hk1 hk2 => ?_⟩
    cases hbk : (piD (ref.phys start) (digitSite ring root k)).word.beta with
    | false => rfl
    | true =>
      exfalso
      have := ((hb k hk1 (by omega)).1 hbk).1
      omega
  obtain ⟨i, hi⟩ : ∃ i, src = first0 + i * valueSpan n := by
    refine ⟨(src - first0) / valueSpan n, ?_⟩
    have h1 := Nat.div_add_mod (src - first0) (valueSpan n)
    rw [show (src - first0) % valueSpan n = 0 from hmod, Nat.add_zero, Nat.mul_comm] at h1
    rw [h1]
    omega
  have hend' : first0 + i * valueSpan n + 2 * valueSpan n < n := by
    rw [← hi]
    exact hend
  obtain ⟨-, hI⟩ := widthCleanRunStart ring ref hn root DigitLane.writer start hst []
    hW first0 hf i hend'
  have hq0 : WidthRunInv ring ref root DigitLane.writer src (valueSpan n)
      (start, digitAuditInitial (piD (ref.phys start))) := by
    rw [hi]
    exact hI
  have hxEnd : wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start)))
      u u.length = u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))) :=
    wRunAtLen ref.toWidthDigitReference u _ _ (Nat.le_refl _)
  have hcomp' : DigitCompletion ring
      (wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start)))
        u u.length).2 root src (src + valueSpan n) DigitLane.writer 0 tm := by
    rw [hxEnd]
    exact hcomp
  obtain ⟨t, -, hcyc, -⟩ := wCycStartOfCompletion ref hn root DigitLane.writer src (valueSpan n)
    hR h2 hend (start, digitAuditInitial (piD (ref.phys start))) hq0 rfl rfl u rfl 0 tm hcomp'
  have hinv := wInvAt ref hn root DigitLane.writer src (valueSpan n) hR h2 hend _ hq0 u t
  have hrun := cycPersist ref.toWidthDigitReference ref.singletonFixed hn root DigitLane.writer
    src (valueSpan n) hR h2 hend (u.drop t)
    (wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start))) u t)
    hinv.1.1 ⟨0, _, 0, hcyc⟩
  rw [wRunAtSplit ref.toWidthDigitReference u _ t] at hrun
  exact hrun

/-- **The writer entry content from the age core, at every boundary reference.**

Consumer: `writersCurrentOfAgedCore`. -/
theorem writerEntryCoreOfAgedCore (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hcore : WriterAgedCore ref.toWidthDigitReference) :
    WriterEntryCore ref.toWidthDigitReference := by
  intro root start u source after T hst hs hpair hT hTc
  refine ⟨?_, writerAgeCoreOfBody ref.toWidthDigitReference
    (writerAgeBodyOfAged ref hn (writerAgedBodyOfCore ref hn hcore)) root start u source
    after T hst hs hpair hT hTc⟩
  obtain ⟨root0, hs0, hL0⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, -⟩ := pairLayoutStart ref hn root start hL0 source hpair
  obtain ⟨t1, -, -, -, h1, -, -, -, -⟩ := hT
  exact writerCycOfStrict ref hn root start hst hs u source t1 hsrc hend h1.1

/-- **`DigitWritersCurrent` at the writer comparison cut, at every boundary reference (SMALL and
BANK), from the age core alone.**

Consumer: the writer comparison certificate (second conjunct), once `WriterAgedCore` is
produced. -/
theorem writersCurrentOfAgedCore (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hcore : WriterAgedCore ref.toWidthDigitReference)
    (start : ref.State) (word : List (Fin n)) (root : Fin n) (z : ref.State)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat)
    (hst : ref.start start)
    (hfold : word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit))
    (hW : WFixedRoot ring root (piW (ref.phys z)))
    (hrec : L3.WriterValueCuts.WidthWriterValueReceipts ring root audit retired restart) :
    ∃ (structural first baseCut last : Nat) (cuts : List (Nat × Nat)),
      DigitValueChain ring root audit structural first baseCut last restart cuts ∧
      DigitWritersCurrent ring root audit (piD (ref.phys z)) audit.current structural audit.clock
        cuts :=
  writersCurrentOfCore ref hn (writerEntryCoreOfAgedCore ref hn hcore) start word root z
    audit retired restart hst hfold hW hrec

end L3.WriterCurrent

#print axioms L3.WriterCurrent.cycPersist
#print axioms L3.WriterCurrent.writerCycOfStrict
#print axioms L3.WriterCurrent.writersCurrentOfAgedCore
