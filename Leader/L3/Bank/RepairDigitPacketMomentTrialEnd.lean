import Leader.L3.Bank.RepairDigitPacketMomentAfter
import Leader.L3.Bank.RepairDigitPacketMomentTrialLabels

/-!
# Lemma e-packet: the renewal trial ends at a group boundary of the queue

repair.tex, the renewal trial: "If the outgoing edge wins, the tail becomes a front before a
younger packet settles. That front erases only the older suffix; the intact younger prefix begins
at a group boundary."

The trial (`L3.PacketMomentVSerial.VIAt R m`) ends when its outcome tail settles
(`L3.PacketMomentVSerial.vStepIdx`, left alternative: queue index `a = 0`, settled run `i ≥ 1`,
outcome `VTAt R i`). That settlement removes the head of the aligned queue
`F^0 (T F^(R-1))^(b+1)`, which is a tail, so the queue after it is aligned at index `R - 1`
(`L3.PacketMomentPending.alignExtStep` at `a = 0`): the younger prefix begins at a group
boundary.

* `vtAtAlign`: the settlement that ends the trial is a removal, and the queue index becomes
  `R - 1` (no-removal letters keep the pending word of the two cells, `LocalSame`, but a pending
  packet became settled beside a settled cell);
* `vAlignAt` / `vAlignAtCoupled`: `vMomentAtCoupled` with the target strengthened to `VTA R m`:
  the outcome `VTAt R m` with `AlignExt R (R - 1)` and the window invariants, same budget
  `(R+2)(2R+2)`;
* `raceKeep` / `raceAlignStep`: at the misaligned outcome (`1 ≤ m ≤ R - 2`) every edge other
  than the two race edges keeps `VTA R m` (no packet settles: the only settled cell beside a
  pending packet is the tail, reached by the incoming race edge alone; no packet is removed);
* `afterRaceAligned` / `afterRaceDoneAligned`: `L3.PacketMomentAfter.afterRaceMoment` and
  `afterRaceDoneMoment` from the race class `VTA R m`, with no alignment premise left;
* `raceAlignPend`: the race inputs of `L3.PacketMomentWide.attemptLoopWide` from a trial
  outcome: distinct race edges, the class `VTA R m` kept off the race edges, and the post-race
  success bound after the outgoing edge.
-/

namespace L3.PacketMomentTrialEnd

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
open L3.DigitPacketOrder
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentPending
open L3.PacketMomentU
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentTrialLabels
open L3.PacketMomentAfter

/-- **The trial outcome at a group boundary**: the outcome `VTAt R m` with the queue aligned at
index `R - 1` and the window invariants. Consumer: `vAlignAt`, `raceKeep`, `afterRaceAligned`. -/
def VTA (R m : Nat) (s : CohortLane) : Prop :=
  VTAt R m s ∧ AlignExt R (R - 1) s ∧ Inv R (winOf R s) ∧ Barrier R (winOf R s)

/-- **The settlement that ends the trial is a removal of the queue head, a tail**: from a trial
state with queue index `0` and settled run `i ≥ 1`, a letter reaching the outcome `VTAt R i`
leaves the queue aligned at index `R - 1`. Consumer: `vAlignAt`. -/
theorem vtAtAlign (R i : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (hA : AlignExt R 0 s)
    (hS : VShape R i s) (hi : 1 ≤ i) (hT : VTAt R i (cohortEdge R s k)) :
    AlignExt R (R - 1) (cohortEdge R s k) := by
  have hiR := hT.1
  have hq : R ≤ 2 * R - 1 - i := by omega
  have hq2 : 2 * R - 1 - i < 2 * R := by omega
  have c0' : (cohortEdge R s k).inp (2 * R - 1 - i) = .S true := (hT.2 _ hq hq2).2.1 rfl
  have h1 : isSI ((cohortEdge R s k).inp (2 * R - 1 - i)) = true := by rw [c0']; rfl
  have h0 : isSI (s.inp (2 * R - 1 - i)) = false := by
    rcases (hS.2 _ hq hq2).2.2 (by omega) with he | hp
    · rw [he]; rfl
    · revert hp; cases s.inp (2 * R - 1 - i) <;> simp [isPI, isSI]
  obtain ⟨hqk, hPk, -⟩ := newSettled R s k _ hq hq2 h1 h0
  rcases alignExtStep R 0 hR s k hA (shapeWin R i s hS) with ⟨-, -, hls⟩ |
      ⟨B, -, -, hA', -⟩
  · exfalso
    have e := hls.1 (by omega) (by omega)
    have c1 : (cohortEdge R s k).inp (k + 1) = .S false :=
      (hT.2 (k + 1) (by omega) (by omega)).2.2.1 (by omega)
    have c0 : (cohortEdge R s k).inp k = .S true := hqk ▸ c0'
    have c2 : s.inp (k + 1) = .S false := (hS.2 (k + 1) (by omega) (by omega)).2.1 (by omega)
    rw [c0, c1, c2] at e
    revert e hPk
    cases s.inp k <;> simp [pwI, isPI]
  · rw [if_pos rfl] at hA'
    exact hA'

/-- A trial state is not yet its outcome. Consumer: `vAlignAt`. -/
theorem viNotVtAt (R m : Nat) (s : CohortLane) (h : VIAt R m s) : ¬ VTAt R m s := by
  rintro ⟨hm, hc⟩
  obtain ⟨a, i, hai, -, hS, hidx⟩ := h
  have him : i ≤ m := by rw [← hidx]; unfold vIdx; split <;> omega
  have hx := (hc (2 * R - 1 - m) (by omega) (by omega)).2.1 rfl
  rcases (hS.2 (2 * R - 1 - m) (by omega) (by omega)).2.2 (by omega) with he | hp
  · rw [hx] at he; cases he
  · rw [hx] at hp; simp [isPI] at hp

/-- **The renewal trial ends at a group boundary, on the lane**: `vMomentAt` with the target
`VTA R m`. Consumer: `vAlignAtCoupled`. -/
theorem vAlignAt {n : Nat} (R : Nat) (hR : 3 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (m : Nat) (s : CohortLane)
    (hs : VIAt R m s) :
    MomentBoundQ (releaseNext R edgeOf) (VTA R m) N (N ^ vPot R s) ((N - n) ^ vPot R s) s := by
  have hlane := vMomentAt R hR hn N hN site edgeOf hedge m s hs
  exact momentSimQ (releaseNext R edgeOf) (releaseNext R edgeOf)
    (fun x y => x = y ∧ (VTA R m x ∨ VIAt R m x)) (VTA R m) (VTAt R m) N _ _
    (fun x y e hxy hna => by
      obtain ⟨rfl, hx⟩ := hxy
      rcases hx with hx | ⟨a', i', hai', hA', hS', hm'⟩
      · exact absurd hx hna
      · refine ⟨rfl, ?_⟩
        show VTA R m (cohortLaneStep R x (edgeOf e)) ∨ VIAt R m (cohortLaneStep R x (edgeOf e))
        cases edgeOf e with
        | none => exact Or.inr ⟨a', i', hai', hA', hS', hm'⟩
        | some k =>
          rcases vStepIdx R hR x k a' i' hai' hA' hS' with ⟨ha0, hi1, ht⟩ | hv
          · left
            subst ha0
            have hidx : vIdx R 0 i' = i' := by
              unfold vIdx; rw [if_neg (by omega)]; omega
            have hw := winKeep R (by omega) x (some k) (shapeWin R i' x hS')
            refine ⟨?_, vtAtAlign R i' (by omega) x k hA' hS' hi1 ht, hw⟩
            show VTAt R m (cohortEdge R x k)
            rw [← hm', hidx]
            exact ht
          · right; rw [← hm']; exact hv)
    (fun x y hxy hg => by
      obtain ⟨rfl, hx⟩ := hxy
      rcases hx with hx | hx
      · exact hx
      · exact absurd hg (viNotVtAt R m x hx)) s s ⟨rfl, Or.inr hs⟩ hlane

/-- **The renewal trial ends at a group boundary, on the coupled chain.** From every layout state
whose lane is a trial state of index `m`, the outcome `VTAt R m` is reached with the queue aligned
at index `R - 1` and the window invariants, `E[z^{T_V}] ≤ w^{(R+2)(2R+2)}` (the budget of
`L3.PacketMomentVSerial.vMomentAtCoupled`). Consumer: the per-pair moment (the race class
`VTA R m` of `raceAlignPend`, and the aligned completion at `m = R - 1`). -/
theorem vAlignAtCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : VIAt R m (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VTA R m (laneOfState ring hbank root lane src R y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hvi : VI R (laneOfState ring hbank root lane src R x) := by
    obtain ⟨a, i, hai, hA, hS, _⟩ := hs
    exact ⟨a, i, hai, hA, hS⟩
  have hlane := vAlignAt R hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk) m
    (laneOfState ring hbank root lane src R x) hs
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => VTA R m (laneOfState ring hbank root lane src R y)) (VTA R m) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (vPotLe R _ hvi)

/-! ### The race class -/

/-- **Off the race edges the trial outcome persists**: at the misaligned outcome
(`1 ≤ m ≤ R - 2`, tail at `f = 2R - 1 - m`) every edge other than the incoming edge `f - 1` and the
outgoing edge `f` keeps `VTA R m`: moving packets left of the tail stay moving (no settled cell
beside them), the settled suffix and the terminal are unchanged, and no packet is removed.
Consumer: `raceAlignStep`. -/
theorem raceKeep (R m k : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (s : CohortLane)
    (h : VTA R m s) (hk1 : k ≠ 2 * R - 2 - m) (hk2 : k ≠ 2 * R - 1 - m) :
    VTA R m (cohortEdge R s k) := by
  obtain ⟨⟨hm, hc⟩, hA, hI, hB⟩ := h
  refine ⟨⟨hm, fun q h1 h2 => ?_⟩, ?_, winKeep R (by omega) s (some k) ⟨hI, hB⟩⟩
  · by_cases e1 : k + 1 < R
    · obtain ⟨hi, hl⟩ := edgePipe R k s e1
      rw [hi, hl]
      exact hc q h1 h2
    by_cases e2 : k + 1 = R
    · obtain ⟨hi, hl⟩ := edgeDel R k s e2
      rw [hi, hl]
      by_cases hq : q = k + 1
      · simp only [cohortUpd, hq, if_true]
        obtain ⟨hl0, -, -, hE⟩ := hc (k + 1) (by omega) (by omega)
        rw [hl0]
        obtain ⟨d1, -, d3⟩ := delRow (s.out k) (s.inp (k + 1))
        exact ⟨d1, fun h => absurd h (by omega), fun h => absurd h (by omega),
          fun _ => d3 (hE (by omega))⟩
      · simp only [cohortUpd, if_neg hq]
        exact hc q h1 h2
    by_cases e3 : k + 1 < 2 * R
    · have hk : R ≤ k := by omega
      obtain ⟨⟨ik, lk⟩, ⟨ik1, lk1⟩, hoth⟩ := finCells R k s hk e3
      obtain ⟨hl0, -, hS0, hE0⟩ := hc k hk (by omega)
      obtain ⟨hl1, -, hS1, hE1⟩ := hc (k + 1) (by omega) e3
      have hfin : finOf R s k = bankRepairDigitFinStep (decide (k = R)) (s.inp k) false
          (s.inp (k + 1)) false := by
        unfold finOf; rw [hl0, hl1]
      by_cases hqk : q = k
      · subst hqk
        rw [ik, lk]
        rcases Nat.lt_or_ge (q + 1) (2 * R - 1 - m) with hlt | hge
        · obtain ⟨r1, -, r3, -⟩ := finEP (decide (q = R)) (s.inp q) (s.inp (q + 1))
            (hE0 (by omega)) (hE1 hlt)
          rw [hfin]
          exact ⟨r1, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => r3⟩
        · rw [hfin, hS0 (by omega), hS1 (by omega), decide_eq_false (by omega : ¬ q = R), finSS]
          exact ⟨rfl, fun h => absurd h (by omega), fun _ => rfl, fun h => absurd h (by omega)⟩
      by_cases hqk1 : q = k + 1
      · subst hqk1
        rw [ik1, lk1]
        rcases Nat.lt_or_ge (k + 1) (2 * R - 1 - m) with hlt | hge
        · obtain ⟨-, r2, -, r4⟩ := finEP (decide (k = R)) (s.inp k) (s.inp (k + 1))
            (hE0 (by omega)) (hE1 hlt)
          rw [hfin]
          exact ⟨r2, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => r4⟩
        · rw [hfin, hS0 (by omega), hS1 (by omega), decide_eq_false (by omega : ¬ k = R), finSS]
          exact ⟨rfl, fun h => absurd h (by omega), fun _ => rfl, fun h => absurd h (by omega)⟩
      obtain ⟨a1, b1⟩ := hoth q (by omega)
      rw [a1, b1]
      exact hc q h1 h2
    by_cases e4 : k + 1 = 2 * R
    · obtain ⟨hi, hl⟩ := L3.DigitPacketRelease.edgeTerm R k s e4
      obtain ⟨hl0, -, hS0, -⟩ := hc k (by omega) (by omega)
      rw [hi, hl]
      by_cases hq : q = k
      · simp only [cohortUpd, hq, if_true]
        rw [hS0 (by omega), hl0]
        exact ⟨rfl, fun h => absurd h (by omega), fun _ => rfl, fun h => absurd h (by omega)⟩
      · simp only [cohortUpd, if_neg hq]
        exact hc q h1 h2
    · rw [cohortEdgeFar R k s (by omega)]
      exact hc q h1 h2
  · rcases alignExtStep R (R - 1) (by omega) s k hA ⟨hI, hB⟩ with ⟨hA', -, -⟩ |
        ⟨B, -, -, -, hkR, hk2R, hP, hS, -⟩
    · exact hA'
    · exfalso
      obtain ⟨-, hT0, hS0, -⟩ := hc k hkR hk2R
      by_cases hkf : k = 2 * R - 1 - m
      · exact absurd (hP.symm.trans (hT0 hkf)) (by simp)
      by_cases hgt : 2 * R - m ≤ k
      · exact absurd (hP.symm.trans (hS0 hgt)) (by simp)
      have hk3 : k + 1 < 2 * R := by omega
      have hsi := (hS hk3).1
      obtain ⟨-, -, -, hE1⟩ := hc (k + 1) (by omega) hk3
      rcases hE1 (by omega) with he | hp
      · rw [he] at hsi; simp [isSI] at hsi
      · revert hsi hp
        cases s.inp (k + 1) <;> simp [isSI, isPI]

/-- **The race class on the coupled chain**: a layout state at the misaligned outcome `VTA R m`
keeps the layout and `VTA R m` along every edge other than the two race edges
(`L3.DigitPacketRace.raceIn` / `raceOut` at offset `R - 1 - m`). Consumer: `raceAlignPend`. -/
theorem raceAlignStep {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hp : VTA R m (laneOfState ring hbank root lane src R x)) (e : Fin n)
    (h1 : e ≠ L3.DigitPacketRace.raceIn ring root src R (R - 1 - m))
    (h2 : e ≠ L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      VTA R m (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e)) := by
  obtain ⟨hl1, hl2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend x hx e
  refine ⟨hl1, ?_⟩
  rw [hl2]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin]
    have hk1 : j - src ≠ 2 * R - 2 - m := by
      intro hk
      exact h1 (by unfold L3.DigitPacketRace.raceIn; congr 1; omega)
    have hk2 : j - src ≠ 2 * R - 1 - m := by
      intro hk
      exact h2 (by unfold L3.DigitPacketRace.raceOut; congr 1; omega)
    exact raceKeep R m (j - src) hR hm1 hm2 _ hp hk1 hk2
  · rw [if_neg hin]
    exact hp

/-! ### The success continuation from the race class -/

/-- **`F_a` from the race class**: `L3.PacketMomentAfter.afterRaceMoment` with its alignment and
window premises read off `VTA R m`. Consumer: `raceAlignPend`. -/
theorem afterRaceAligned {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N)
    (P : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop)
    (Bs : Nat)
    (hP : ∀ y, CohortLayout ring hbank root src R y.1 →
      AGroup R (laneOfState ring hbank root lane src R y) →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
        (N ^ Bs) ((N - n) ^ Bs) y)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hp : VTA R m (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
      (N ^ (afterBudget R + Bs)) ((N - n) ^ (afterBudget R + Bs))
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) :=
  afterRaceMoment ring hn hbank root lane src R m hR hsrc hend hm1 hm2 N hN P Bs hP x hx
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- **`F_a` to the finished group from the race class**: `afterRaceDoneMoment` from `VTA R m`,
`E[z^T] ≤ w^{afterBudget R + (R + 1)}`. Consumer: the post-race success branch of
`L3.PacketMomentWide.attemptLoopWide` (budget checked by `afterBudgetShort`). -/
theorem afterRaceDoneAligned {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hp : VTA R m (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ADone R (laneOfState ring hbank root lane src R y) ∧
        CohortLayout ring hbank root src R y.1) N
      (N ^ (afterBudget R + (R + 1))) ((N - n) ^ (afterBudget R + (R + 1)))
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) :=
  afterRaceDoneMoment ring hn hbank root lane src R m hR hsrc hend hm1 hm2 N hN x hx
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- **The race inputs of the wide attempt loop at a trial outcome.** With the race class
`Pend y := CohortLayout ∧ VTA R m (lane y)` (`1 ≤ m ≤ R - 2`), success edge `ea = raceOut` and
failure edge `eb = raceIn` at offset `R - 1 - m`: the two edges are distinct, `Pend` is kept by
every other edge, and after the success edge the target `P` is reached with
`E[z^T] ≤ w^{afterBudget R + B_s}` whenever every layout aligned-group state reaches `P` within
`w^{B_s}`. These are the `Pend`, `ea ≠ eb`, keep and `F_a` clauses of the third alternative of
`L3.PacketMomentWide.attemptLoopWide`'s `hQ`; the failure clause (`Pend → A (next x eb)`) is the
other worker's. Consumer: the per-pair moment at the BANK pair. -/
theorem raceAlignPend {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N)
    (P : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop)
    (Bs : Nat)
    (hP : ∀ y, CohortLayout ring hbank root src R y.1 →
      AGroup R (laneOfState ring hbank root lane src R y) →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
        (N ^ Bs) ((N - n) ^ Bs) y) :
    L3.DigitPacketRace.raceOut ring root src R (R - 1 - m) ≠
        L3.DigitPacketRace.raceIn ring root src R (R - 1 - m) ∧
      (∀ x, CohortLayout ring hbank root src R x.1 →
        VTA R m (laneOfState ring hbank root lane src R x) →
        ∀ e, e ≠ L3.DigitPacketRace.raceOut ring root src R (R - 1 - m) →
          e ≠ L3.DigitPacketRace.raceIn ring root src R (R - 1 - m) →
          CohortLayout ring hbank root src R
              (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
            VTA R m (laneOfState ring hbank root lane src R
              (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e))) ∧
      (∀ x, CohortLayout ring hbank root src R x.1 →
        VTA R m (laneOfState ring hbank root lane src R x) →
        MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
          (N ^ (afterBudget R + Bs)) ((N - n) ^ (afterBudget R + Bs))
          (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
            (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)))) :=
  ⟨fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega) he.symm,
    fun x hx hp e ha hb => raceAlignStep ring hn hbank root lane src R m hR hsrc hend hm1 hm2 x hx
      hp e hb ha,
    fun x hx hp => afterRaceAligned ring hn hbank root lane src R m hR hsrc hend hm1 hm2 N hN P
      Bs hP x hx hp⟩

end L3.PacketMomentTrialEnd

#print axioms L3.PacketMomentTrialEnd.vtAtAlign
#print axioms L3.PacketMomentTrialEnd.vAlignAt
#print axioms L3.PacketMomentTrialEnd.vAlignAtCoupled
#print axioms L3.PacketMomentTrialEnd.raceKeep
#print axioms L3.PacketMomentTrialEnd.raceAlignStep
#print axioms L3.PacketMomentTrialEnd.afterRaceAligned
#print axioms L3.PacketMomentTrialEnd.afterRaceDoneAligned
#print axioms L3.PacketMomentTrialEnd.raceAlignPend
