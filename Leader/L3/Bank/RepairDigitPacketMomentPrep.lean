import Leader.L3.Bank.RepairDigitPacketMomentVSerial

/-!
# Lemma e-packet: the aligned queue along U, retirement and the renewal trial

repair.tex, Lemma e-packet: after the distinguished tail exports, "exclusion and its rearms force
each subsequent group's export origins to be `r-1, …, 0`"; the renewal trial starts at the
packet-only cut reached by phase U and the retirement.

On the coupled BANK x audit chain:
* the source alignment (`SrcAligned`: `Align a` of the source word, started by the distinguished
  export, `L3.PacketMomentAlign.preStep`) is kept by every edge (`srcAlignCoupled`);
* at a mobile-free cut with an aligned source the whole queue is aligned (`winAlignedOfMobileFree`),
  and the aligned queue with the window invariants (`WinAligned`) is kept by every edge
  (`winAlignedCoupled`; `L3.PacketMomentU.winKeep` and `L3.PacketMomentV.alignKeep`);
* an invariant kept by every edge rides along a first-hit moment (`momentKeep`), so the settled-
  empty cut (`uMomentCoupled`) and the packet-only cut (`retMomentCoupled`) are reached in
  `WinAligned`, with `CZero` and an aligned queue there; the packet-only cut is a trial state
  (`viOfPacketOnly`) and `vMomentCoupled` settles a tail at an offset `h ≤ R - 2`.
`prepMomentCoupled`: from a layout state with `WinAligned`,
`E[z^{T_{U + ret + V}}] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`, `w = N/(N-n)`;
`prepCutCoupled` stops at the packet-only cut with the aligned queue.
-/

namespace L3.PacketMomentPrep

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketRelease
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentAlign
open L3.PacketMomentPending
open L3.PacketMomentU
open L3.PacketMomentRetire
open L3.PacketMomentV

/-! ### Invariants along a first hit -/

/-- **An invariant kept by every letter rides along a first hit**: the target is hit in the
invariant. Consumer: `prepCutCoupled`, `prepMomentCoupled`. -/
theorem momentKeep {S : Type} {n : Nat} (next : S → Fin n → S) (Q I : S → Prop) (N a b : Nat)
    (hI : ∀ y e, I y → I (next y e)) (x : S) (hx : I x) (h : MomentBoundQ next Q N a b x) :
    MomentBoundQ next (fun y => Q y ∧ I y) N a b x :=
  momentSimQ next next (fun y z => y = z ∧ I y) (fun y => Q y ∧ I y) Q N a b
    (fun y z e hyz _ => by
      obtain ⟨rfl, hy⟩ := hyz
      exact ⟨rfl, hI y e hy⟩)
    (fun y z hyz hg => by
      obtain ⟨rfl, hy⟩ := hyz
      exact ⟨hg, hy⟩) x x ⟨rfl, hx⟩ h

/-! ### The source alignment -/

/-- **The aligned source**: some `Align a` (begun at the distinguished export). Consumer:
`winAlignedOfMobileFree`. -/
def SrcAligned (R : Nat) (s : CohortLane) : Prop := ∃ a, Align R a s.out

/-- The aligned source is kept by every lane letter. Consumer: `srcAlignCoupled`. -/
theorem srcAlignKeep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (o : Option Nat)
    (h : SrcAligned R s) : SrcAligned R (cohortLaneStep R s o) := by
  cases o with
  | none => exact h
  | some k =>
    obtain ⟨a, ha⟩ := h
    rcases alignStep R a hR s k ha with ⟨h1, _⟩ | ⟨_, _, _, _, h1⟩
    · exact ⟨a, h1⟩
    · exact ⟨_, h1⟩

/-- The distinguished export aligns the source: the first export of the distinguished group's
tail out of a `Pre 0` state leaves `Align (R - 1)`. Consumer: the start of `SrcAligned` after the
distinguished-tail phase. -/
theorem srcAlignOfDistinguished (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat)
    (h : Pre R 0 s.out) (B : Bool) (hex : Exported R s k B ∧
      srcWord R s.out = B :: srcWord R (cohortEdge R s k).out) :
    B = true ∧ SrcAligned R (cohortEdge R s k) := by
  rcases preStep R 0 hR s k h with ⟨_, hno⟩ | ⟨B', hex', hw, h0, _⟩
  · exact absurd hex (hno B)
  · have hBB : B = B' := by
      have := hex.2; rw [hw] at this
      exact (List.cons.inj this).1.symm
    obtain ⟨hB', hA⟩ := h0 rfl
    exact ⟨hBB ▸ hB', ⟨_, hA⟩⟩

/-- The aligned source on the coupled chain. Consumer: the distinguished-tail and inherited-work
phases up to the mobile-free cut (`winAlignedOfMobileFree`). -/
theorem srcAlignCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : CohortLayout ring hbank root src R y.1 ∧
      SrcAligned R (laneOfState ring hbank root lane src R y)) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) y e).1 ∧
      SrcAligned R (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) y e)) := by
  obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y h.1 e
  rw [h2]
  exact ⟨h1, srcAlignKeep R hR _ _ h.2⟩

/-! ### The aligned queue with the window invariants -/

/-- **The aligned queue with the window invariants.** Consumer: `prepMomentCoupled`. -/
def WinAligned (R : Nat) (s : CohortLane) : Prop :=
  (∃ a, AlignExt R a s) ∧ Inv R (winOf R s) ∧ Barrier R (winOf R s)

/-- Kept by every lane letter. Consumer: `winAlignedCoupled`. -/
theorem winAlignedKeep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (o : Option Nat)
    (h : WinAligned R s) : WinAligned R (cohortLaneStep R s o) := by
  refine ⟨?_, winKeep R hR s o h.2⟩
  cases o with
  | none => exact h.1
  | some k => exact alignKeep R hR s k h.1 h.2

/-- **At a mobile-free cut an aligned source aligns the queue**: no packet is pending, so the
queue is the source word. Consumer: `prepMomentCoupled` (start after the inherited-work phase). -/
theorem winAlignedOfMobileFree (R : Nat) (s : CohortLane) (hs : SrcAligned R s)
    (h : ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (s.inp q = .E ∨ ∃ T, s.inp q = .S T)) :
    WinAligned R s := by
  obtain ⟨a, ha⟩ := hs
  refine ⟨⟨a, alignExtOfSrc R a s ha fun q h1 h2 => ?_⟩, winStartMobileFree R s h⟩
  rcases (h q h1 h2).2 with hE | ⟨T, hS⟩
  · rw [hE]; rfl
  · rw [hS]; rfl

/-- On the coupled chain. Consumer: `prepCutCoupled`, `prepMomentCoupled`. -/
theorem winAlignedCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : CohortLayout ring hbank root src R y.1 ∧
      WinAligned R (laneOfState ring hbank root lane src R y)) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) y e).1 ∧
      WinAligned R (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) y e)) := by
  obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y h.1 e
  rw [h2]
  exact ⟨h1, winAlignedKeep R hR _ _ h.2⟩

/-! ### The composed preparation -/

/-- **Phase U and the retirement in the aligned queue.** From a layout state with `WinAligned`
the packet-only cut is reached in `WinAligned` (`CZero`, aligned queue, window invariants) with
`E[z^T] ≤ w^{uBudget R + 2R}`. Consumer: `prepMomentCoupled`; the failure return of the renewal
trial (`U + r` back to an aligned packet-only cut). -/
theorem prepCutCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : WinAligned R (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => PacketOnly R (laneOfState ring hbank root lane src R y) ∧
        (CohortLayout ring hbank root src R y.1 ∧
          WinAligned R (laneOfState ring hbank root lane src R y))) N
      (N ^ uBudget R * N ^ (2 * R)) ((N - n) ^ uBudget R * (N - n) ^ (2 * R)) x := by
  let next := widthDigitAuditNext (bankWidthDigitReference ring hn hbank)
  let I : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => CohortLayout ring hbank root src R y.1 ∧
      WinAligned R (laneOfState ring hbank root lane src R y)
  have hI : ∀ y e, I y → I (next y e) := fun y e h =>
    winAlignedCoupled ring hn hbank root lane src R (by omega) hsrc hend y e h
  have hU := momentKeep next _ I N _ _ hI x ⟨hx, hs⟩
    (uMomentCoupled ring hn hbank root lane src R hR hsrc hend N hN x hx hs.2.1 hs.2.2)
  refine momentSeq next _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_) hU
  obtain ⟨hns, hl, hw⟩ := hy
  exact momentKeep next _ I N _ _ hI y ⟨hl, hw⟩
    (retMomentCoupled ring hn hbank root lane src R (by omega) hsrc hend N hN y hl
      (retStartOfU R _ hns hw.2.2))

/-- **Lemma e-packet, U, retirement and the renewal trial composed.** From a layout state with
the aligned queue and the window invariants (e.g. a mobile-free cut with an aligned source,
`winAlignedOfMobileFree`), a tail is settled carry-free at an offset `h ≤ R - 2` of the target
window (`h ≥ 1`: `RacePend`; `h = 0`: aligned settlement) with
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`, `w = N/(N-n)`, uniformly over source registers and
audit. Consumer: the per-pair moment (`E[z^{T_pair}] < 40`, Lemma e-max): the attempt before the
race. -/
theorem prepMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : WinAligned R (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VT R (laneOfState ring hbank root lane src R y)) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  refine momentSeq _ _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_)
    (prepCutCoupled ring hn hbank root lane src R hR hsrc hend N hN x hx hs)
  obtain ⟨hP, hl, ⟨a, hA⟩, _⟩ := hy
  exact vMomentCoupled ring hn hbank root lane src R hR hsrc hend N hN y hl
    (viOfPacketOnly R a _ hA hP)

end L3.PacketMomentPrep

#print axioms L3.PacketMomentPrep.momentKeep
#print axioms L3.PacketMomentPrep.srcAlignKeep
#print axioms L3.PacketMomentPrep.srcAlignOfDistinguished
#print axioms L3.PacketMomentPrep.srcAlignCoupled
#print axioms L3.PacketMomentPrep.winAlignedOfMobileFree
#print axioms L3.PacketMomentPrep.winAlignedCoupled
#print axioms L3.PacketMomentPrep.prepCutCoupled
#print axioms L3.PacketMomentPrep.prepMomentCoupled
