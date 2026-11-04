import Leader.L3.Width.DigitWriterCurrentUseShape
import Leader.L3.Width.DigitWriterCurrentEntry

/-!
# Writer currentness: the structural half of the aged uses

`UseOkS … now u`: the use `u` was made by `now`, and a sampled operand was stamped before the use,
on the writer lane, at a cell of the source window.  `UseStructInv` asks this of every use of every
ledger of the target window.  It is carried by the audit (`useStructStep`) from the ghost
correspondence `GhostCorrDistinct` (a settled input holding a sampled atom is a recorded sample of
this lane at a source cell, stamped no later than the clock) and `windowUses`.

Consumer: `WidthDigitWriterCurrentAgedUses` (the residual keeps only the age of the operands).
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.WidthWave

variable {n : Nat} {ring : DirectedRing n}

section Struct

variable {c : Compiled}

/-- Consumer: `UseStructInv`. -/
def UseOkS (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R now : Nat)
    (u : DigitUse c n) : Prop :=
  u.time ≤ now ∧ ∀ id : DigitStamp n, u.operand = some (.sampled id) →
    id.time < u.time ∧ id.lane = lane ∧ ∃ q, q < R ∧ id.site = digitSite ring root (src + q)

/-- Consumer: `useStructStep`. -/
def UseStructInv (ring : DirectedRing n) (root : Fin n) (src R : Nat) (A : DigitAudit c n) :
    Prop :=
  ∀ q (L : DigitCarryGhost c n), R ≤ q → q < 2 * R →
    winCarry ring root src A.current q = some L →
    ∀ u ∈ L.uses, UseOkS ring root DigitLane.writer src R A.clock u

/-- **A settled sampled input of a target cell is a recorded writer sample of a source cell,
stamped no later than the clock.**

Consumer: `useStructStep`. -/
theorem inputAtomOk (root : Fin n) (S : Fin n → ProjD c) (A : DigitAudit c n) (src R : Nat)
    (hgc : GhostCorrDistinct ring root DigitLane.writer src R (InheritedOk DigitLane.writer) S A)
    (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R)
    (his : (S (digitSite ring root (src + q))).top.wIn.isS = true) (id : DigitStamp n)
    (hid : (A.current (digitSite ring root (src + q))).writer.input = some (.sampled id)) :
    id.time ≤ A.clock ∧ id.lane = DigitLane.writer ∧
      ∃ q', q' < R ∧ id.site = digitSite ring root (src + q') := by
  obtain ⟨hgc1, -, htb, -⟩ := hgc
  obtain ⟨v, T, hs⟩ : ∃ v T, (S (digitSite ring root (src + q))).top.wIn = .S v T := by
    cases hI : (S (digitSite ring root (src + q))).top.wIn with
    | S v T => exact ⟨v, T, rfl⟩
    | E => rw [hI] at his; simp [InTok.isS] at his
    | X => rw [hI] at his; simp [InTok.isS] at his
    | P v T => rw [hI] at his; simp [InTok.isS] at his
  have hcorr := (hgc1.2 q h1 h2).1
  rw [projIn ring root DigitLane.writer src R S q h1 h2] at hcorr
  have hshape : bankRepairDigitInShOf (bankRepairDigitLaneIn DigitLane.writer
      (S (digitSite ring root (src + q))).top) = .S T := by
    show bankRepairDigitInShOf (S (digitSite ring root (src + q))).top.wIn = .S T
    rw [hs]
    rfl
  rw [hshape] at hcorr
  have hin : (laneCells ring root DigitLane.writer src A.current q).input = some (.sampled id) :=
    hid
  rw [hin] at hcorr
  have hok : GhostOk ring root DigitLane.writer src R (InheritedOk DigitLane.writer) A T
      (.sampled id) := hcorr
  have htr : tracked ring root DigitLane.writer src R A q = some (.sampled id) := by
    unfold tracked trackedAt
    rw [if_neg (by omega), if_pos h2]
    exact hin
  refine ⟨htb q id htr, ?_⟩
  rcases hok with ⟨site, slot, hb⟩ | ⟨s, hs1, -, -, hl, q', hq', hsite⟩
  · cases hb
  · have hid' : id = s.id := by
      have := hs1
      simp only [DigitAtom.sampled.injEq] at this
      exact this
    subst hid'
    exact ⟨hl, q', hq', hsite⟩

end Struct

section Run

/-- **The bundle carried by the audit fold.**  Consumer: `useStructStep`. -/
def StructBundle (ref : WidthDigitReference ring) (root : Fin n) (src R : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref root src R y.1 ∧
  GhostCorrDistinct ring root DigitLane.writer src R (InheritedOk DigitLane.writer)
    (piD (ref.phys y.1)) y.2 ∧
  CarryAll (piD (ref.phys y.1)) y.2.current ∧
  UseStructInv ring root src R y.2

/-- **One letter preserves `StructBundle`.**  Consumer: `useStructRun`. -/
theorem useStructStep (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : StructBundle ref root src R y) :
    StructBundle ref root src R (widthDigitAuditNext ref y e) := by
  obtain ⟨hlay, hgc, hcar, hus⟩ := h
  obtain ⟨hlay', hgc'⟩ := widthGhostCorrDistinctStep ref hfix hn root DigitLane.writer src R hR
    hsrc hend (InheritedOk DigitLane.writer) y hlay hgc e
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root y.1 hL e
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  refine ⟨hlay', hgc', ?_, ?_⟩
  · show CarryAll (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
      (digitGhostStep ring (piD (ref.phys y.1)) y.2.current (y.2.clock + 1)
        (digitSite ring root j))
    rw [heq]
    exact carryAll_step ring _ _ _ _ hcar
  · intro q L h1 h2 hL' u hu
    have key := windowUses ring (by omega) root (piD (ref.phys y.1)) y.2.current (y.2.clock + 1)
      R src hR hsrc hend hbR hbF hcar j hj hbX hbY
      (UseOkS ring root DigitLane.writer src R (y.2.clock + 1))
      (fun q L h1 h2 hL u hu => by
        obtain ⟨a, b⟩ := hus q L h1 h2 hL u hu
        exact ⟨Nat.le_succ_of_le a, b⟩)
      (fun q u h1 h2 ht ho his => by
        refine ⟨by omega, fun id hid => ?_⟩
        obtain ⟨hti, hl, hs⟩ := inputAtomOk root (piD (ref.phys y.1)) y.2 src R hgc (q + 1)
          (by omega) h2 his id (by rw [← ho]; exact hid)
        exact ⟨by omega, hl, hs⟩)
      (fun u ht ho his => by
        refine ⟨by omega, fun id hid => ?_⟩
        obtain ⟨hti, hl, hs⟩ := inputAtomOk root (piD (ref.phys y.1)) y.2 src R hgc R
          (Nat.le_refl _) (by omega) his id (by rw [← ho]; exact hid)
        exact ⟨by omega, hl, hs⟩)
    exact key q L h1 h2 hL' u hu

/-- **`StructBundle` along a word.**  Consumer: `usesStructural`. -/
theorem useStructRun (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (w : List (Fin n)) :
    ∀ y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      StructBundle ref root src R y →
      StructBundle ref root src R (w.foldl (widthDigitAuditNext ref) y) := by
  induction w with
  | nil => intro y h; exact h
  | cons e rest ih =>
    intro y h
    exact ih _ (useStructStep ref hfix hn root src R hR hsrc hend y e h)

end Run

end L3.WriterCurrent

#print axioms L3.WriterCurrent.inputAtomOk
#print axioms L3.WriterCurrent.useStructRun
