import Leader.L3.Bank.RepairDigitPacketMomentPending
import Leader.L3.Bank.RepairDigitPacketMomentRetire
import Leader.L3.Bank.RepairDigitPacketRace

/-!
# Lemma e-packet, the renewal preparation `V` in moment form

From a packet-only cut whose pending queue is aligned (`L3.PacketMomentPending.AlignExt`,
`extWord = F^a (T F^(R-1))^(b+1)`), the trial runs in the class `VI`: the target window holds
a settled non-tail run `S false` on its top `i` cells, pending packets and empty cells below,
no carry, with `i + a + 1 ≤ R` (`VShape`). Each removal of the oldest pending packet either
extends the settled run by a non-tail (`a ≥ 1`), retires a tail at the terminal (`a = 0`,
`i = 0`: a group boundary, then `a = R - 1`), or settles the tail at offset
`h = R - 1 - i ≤ R - 2`: the target `VT` (`h ≥ 1` is the misaligned-tail cut `RacePend`,
`h = 0` the aligned settlement at the border).

The potential `vPot = rem * (2R + 2) + prog` counts the removals left (`rem ≤ R + 1`) and the
work of the next one (`prog`: the empty cells above the rightmost pending packet, plus the
source distance when no packet is pending). No letter raises it (`vLetter`) and a nominated
letter lowers it (`vDrop`), so `E[z^{T_V}] ≤ w^{(R+2)(2R+2)}` (`vMomentCoupled`); the paper's
`V = 2r^2 + 5r + 3`.
-/

namespace L3.PacketMomentV

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

/-! ### Runs -/

/-- The number of consecutive cells `top, top - 1, ...` (at most `m`) satisfying `p`.
Consumer: `sR`, `eR`. -/
def run (p : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | top, m + 1 => if p top then run p (top - 1) m + 1 else 0

/-- Reading a run. Consumer: `eRSpec`. -/
theorem runSpec (p : Nat → Bool) : ∀ m top,
    run p top m ≤ m ∧ (∀ d, d < run p top m → p (top - d) = true) ∧
      (run p top m < m → p (top - run p top m) = false)
  | 0, top => by simp [run]
  | m + 1, top => by
      obtain ⟨h1, h2, h3⟩ := runSpec p m (top - 1)
      simp only [run]
      by_cases hp : p top = true
      · rw [if_pos hp]
        refine ⟨by omega, fun d hd => ?_, fun hlt => ?_⟩
        · cases d with
          | zero => simpa using hp
          | succ d =>
              have := h2 d (by omega)
              rwa [show top - 1 - d = top - (d + 1) by omega] at this
        · have := h3 (by omega)
          rwa [show top - 1 - run p (top - 1) m = top - (run p (top - 1) m + 1) by omega] at this
      · rw [if_neg hp]
        refine ⟨by omega, fun d hd => by omega, fun _ => by simpa using hp⟩

/-- Computing a run. Consumer: `sROf`, the `eR` lemmas. -/
theorem runEq (p : Nat → Bool) : ∀ m top j, j ≤ m → (∀ d, d < j → p (top - d) = true) →
    (j < m → p (top - j) = false) → run p top m = j
  | 0, top, j, hj, _, _ => by simp [run]; omega
  | m + 1, top, j, hj, hall, hstop => by
      simp only [run]
      cases j with
      | zero =>
          have := hstop (by omega)
          simp at this
          rw [if_neg (by simp [this])]
      | succ j =>
          have h0 := hall 0 (by omega)
          simp at h0
          rw [if_pos h0]
          congr 1
          exact runEq p m (top - 1) j (by omega)
            (fun d hd => by
              have := hall (d + 1) (by omega)
              rwa [show top - (d + 1) = top - 1 - d by omega] at this)
            (fun hjm => by
              have := hstop (by omega)
              rwa [show top - (j + 1) = top - 1 - j by omega] at this)

/-- Runs read only their cells. Consumer: the `eR` lemmas. -/
theorem runCongr (p q : Nat → Bool) : ∀ m top, (∀ d, d < m → q (top - d) = p (top - d)) →
    run q top m = run p top m
  | 0, _, _ => rfl
  | m + 1, top, h => by
      simp only [run]
      rw [show q top = p top by simpa using h 0 (by omega),
        runCongr p q m (top - 1) (fun d hd => by
          have := h (d + 1) (by omega)
          rwa [show top - (d + 1) = top - 1 - d by omega] at this)]

/-! ### The trial class -/

/-- Empty, pending or non-tail settled. Consumer: `finRows`. -/
def shB : BankRepairDigitInSh → Bool
  | .E => true
  | .P _ => true
  | .S false => true
  | _ => false

/-- **The trial shape**: a settled non-tail run on the top `i` cells, empty or pending cells
below, no carry. Consumer: `VI`. -/
def VShape (R i : Nat) (s : CohortLane) : Prop :=
  i + 1 ≤ R ∧ ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧
    (2 * R - i ≤ q → s.inp q = .S false) ∧
    (q < 2 * R - i → s.inp q = .E ∨ isPI (s.inp q) = true)

/-- **The trial class.** Consumer: `vMoment`. -/
def VI (R : Nat) (s : CohortLane) : Prop :=
  ∃ a i, i + a + 1 ≤ R ∧ AlignExt R a s ∧ VShape R i s

/-- **The trial target**: a tail settled at an offset `h ≤ R - 2` (misaligned for `h ≥ 1`,
aligned at the border for `h = 0`). Consumer: `vMoment`. -/
def VT (R : Nat) (s : CohortLane) : Prop :=
  ∃ h, h + 1 < R ∧ s.inp (R + h) = .S true ∧ s.live (R + h) = false

/-- The window invariants of a trial state. Consumer: `vStep`. -/
theorem shapeWin (R i : Nat) (s : CohortLane) (h : VShape R i s) :
    Inv R (winOf R s) ∧ Barrier R (winOf R s) := by
  have hoff : ∀ j, j < R → (winOf R s j).c = .off := by
    intro j hj
    have := (h.2 (R + j) (by omega) (by omega)).1
    simp [winOf, liftC, this]
  refine ⟨⟨fun j hj hf => absurd hf (by rw [hoff j hj]; simp),
    fun j k hj _ hf _ => absurd hf (by rw [hoff j hj]; simp)⟩, ?_⟩
  intro p q hp hq hP hO
  have hpq := h.2 (R + p) (by omega) (by omega)
  have hqq := h.2 (R + q) (by omega) (by omega)
  have hPp : isPI (s.inp (R + p)) = true := by
    revert hP; simp only [winOf, liftC]
    cases s.inp (R + p) with
    | P T => intro _; rfl
    | E => intro h; simp [cellIn, Inp.isP] at h
    | X => intro h; simp [cellIn, Inp.isP] at h
    | S T => cases T <;> (intro h; simp [cellIn, Inp.isP] at h)
  have hp2 : R + p < 2 * R - i := by
    apply Classical.byContradiction
    intro hc
    rw [hpq.2.1 (by omega)] at hPp
    cases hPp
  have hq2 : 2 * R - i ≤ R + q := by
    apply Classical.byContradiction
    intro hc
    revert hO; simp only [winOf, liftC, obC, hqq.1, if_false]
    rcases hqq.2.2 (by omega) with he | hpi
    · rw [he]; simp [cellIn, Inp.isS]
    · revert hpi; cases s.inp (R + q) with
      | P T => cases T <;> (intro _; simp [cellIn, Inp.isS])
      | _ => intro h; cases h
  omega

/-! ### The potential -/

/-- Leading non-tails. Consumer: `rem`. -/
def lead : List Bool → Nat
  | [] => 0
  | false :: w => lead w + 1
  | true :: _ => 0

/-- The leading non-tails of an aligned word. Consumer: `vStep`. -/
theorem leadAlign (R a b : Nat) : lead (List.replicate a false ++ grp R (b + 1)) = a := by
  induction a with
  | zero => rw [grpCons]; simp [blk, lead]
  | succ a ih => simp [List.replicate_succ, lead, ih]

/-- The length of the settled run. Consumer: `rem`, `eR`. -/
def sR (R : Nat) (s : CohortLane) : Nat := run (fun q => isSI (s.inp q)) (2 * R - 1) R

/-- The settled run of a trial shape. Consumer: `vStep`. -/
theorem sROf (R i : Nat) (s : CohortLane) (h : VShape R i s) : sR R s = i := by
  have hi := h.1
  apply runEq _ R (2 * R - 1) i (by omega)
  · intro d hd
    rw [(h.2 (2 * R - 1 - d) (by omega) (by omega)).2.1 (by omega)]; rfl
  · intro hi
    rcases (h.2 (2 * R - 1 - i) (by omega) (by omega)).2.2 (by omega) with he | hp
    · rw [he]; rfl
    · revert hp; cases s.inp (2 * R - 1 - i) with
      | P T => intro _; rfl
      | _ => intro h; cases h

/-- The empty cells above the rightmost pending packet. Consumer: `prog`. -/
def eR (R : Nat) (s : CohortLane) : Nat :=
  run (fun q => decide (s.inp q = .E)) (2 * R - 1 - sR R s) (R - sR R s)

/-- The work of the next removal. Consumer: `vPot`. -/
def prog (R : Nat) (s : CohortLane) : Nat :=
  eR R s + (if eR R s = R - sR R s then dist R (srcLane s) else 0)

/-- The removals left. Consumer: `vPot`. -/
def rem (R : Nat) (s : CohortLane) : Nat :=
  if lead (extWord R s) = 0 ∧ sR R s = 0 then R + 1 else lead (extWord R s) + 1

/-- The level width. Consumer: `vPot`. -/
def vK (R : Nat) : Nat := 2 * R + 2

/-- **The potential of the trial.** Consumer: `vMoment`. -/
noncomputable def vPot (R : Nat) (s : CohortLane) : Nat :=
  if VT R s then 0 else rem R s * vK R + prog R s

/-- The work is below the level width. Consumer: `vStep`. -/
theorem progLt (R : Nat) (s : CohortLane) : prog R s + 1 ≤ vK R := by
  have h1 := (runSpec (fun q => decide (s.inp q = .E)) (R - sR R s) (2 * R - 1 - sR R s)).1
  have h2 := dist_le R (srcLane s)
  unfold prog vK
  change eR R s ≤ R - sR R s at h1
  split <;> omega

/-- The removals left are at most `R + 1`. Consumer: `vMomentCoupled`. -/
theorem remLe (R : Nat) (s : CohortLane) (a : Nat) (h : AlignExt R a s) : rem R s ≤ R + 1 := by
  obtain ⟨_, ha, b, hw⟩ := h
  unfold rem
  rw [hw, leadAlign]
  split <;> omega

/-- The empty run read off. Consumer: the `eR` lemmas. -/
theorem eRSpec (R i : Nat) (s : CohortLane) (hs : sR R s = i) :
    eR R s ≤ R - i ∧ (∀ d, d < eR R s → s.inp (2 * R - 1 - i - d) = .E) ∧
      (eR R s < R - i → s.inp (2 * R - 1 - i - eR R s) ≠ .E) := by
  have h := runSpec (fun q => decide (s.inp q = .E)) (R - i) (2 * R - 1 - i)
  unfold eR
  rw [hs]
  refine ⟨h.1, fun d hd => by simpa using h.2.1 d hd, fun hl => by simpa using h.2.2 hl⟩

/-- Computing the empty run. Consumer: the `eR` lemmas. -/
theorem eREq (R i j : Nat) (s : CohortLane) (hs : sR R s = i) (hj : j ≤ R - i)
    (hall : ∀ d, d < j → s.inp (2 * R - 1 - i - d) = .E)
    (hstop : j < R - i → s.inp (2 * R - 1 - i - j) ≠ .E) : eR R s = j := by
  unfold eR
  rw [hs]
  exact runEq _ _ _ _ hj (fun d hd => by simpa using hall d hd) (fun hl => by simpa using hstop hl)

/-! ### The rows on a trial shape -/

/-- An empty initiator. Consumer: `vStep`. -/
theorem finE (bx : Bool) (iy : BankRepairDigitInSh) :
    bankRepairDigitFinStep bx .E false iy false = (.E, false, iy, false) := by
  cases iy <;> rfl

/-- A non-border non-tail settled initiator. Consumer: `vStep`. -/
theorem finS (iy : BankRepairDigitInSh) :
    bankRepairDigitFinStep false (.S false) false iy false = (.S false, false, iy, false) := by
  cases iy <;> rfl

/-- A pending initiator on an empty responder moves. Consumer: `vStep`. -/
theorem finPE (bx B : Bool) :
    bankRepairDigitFinStep bx (.P B) false .E false = (.E, false, .P B, false) := rfl

/-- A pending initiator on a pending responder waits. Consumer: `vStep`. -/
theorem finPP (bx B B' : Bool) :
    bankRepairDigitFinStep bx (.P B) false (.P B') false = (.P B, false, .P B', false) := rfl

/-- A pending initiator on a settled responder settles. Consumer: `vStep`. -/
theorem finPS (bx B : Bool) :
    bankRepairDigitFinStep bx (.P B) false (.S false) false = (.S B, false, .S false, false) := rfl

/-! ### The empty run under one change -/

/-- The empty run reads only the inputs. Consumer: `vStep`. -/
theorem eRInp (R : Nat) (s s' : CohortLane) (h : s'.inp = s.inp) : eR R s' = eR R s := by
  unfold eR sR; rw [h]

/-- The settled run reads only the inputs. Consumer: `vStep`. -/
theorem sRInp (R : Nat) (s s' : CohortLane) (h : s'.inp = s.inp) : sR R s' = sR R s := by
  unfold sR; rw [h]

/-- **A pending packet moves up.** The empty run does not grow, and shrinks by one when the
rightmost pending packet moves. Consumer: `vStep`. -/
theorem eRMove (R i k : Nat) (B : Bool) (s s' : CohortLane) (hS : sR R s = i) (hS' : sR R s' = i)
    (hi : i + 1 ≤ R) (hk : R ≤ k) (hk1 : k + 1 < 2 * R - i) (hPk : s.inp k = .P B)
    (hEk : s.inp (k + 1) = .E) (_h'k : s'.inp k = .E) (h'k1 : s'.inp (k + 1) = .P B)
    (hoth : ∀ q, q ≠ k → q ≠ k + 1 → s'.inp q = s.inp q) :
    eR R s' < R - i ∧ eR R s' ≤ eR R s ∧ (k = 2 * R - 1 - i - eR R s → eR R s' + 1 = eR R s) := by
  obtain ⟨he1, he2, he3⟩ := eRSpec R i s hS
  generalize hE : eR R s = e at he1 he2 he3
  have hlt : e < R - i := by
    apply Classical.byContradiction
    intro hc
    have := he2 (2 * R - 1 - i - k) (by omega)
    rw [show 2 * R - 1 - i - (2 * R - 1 - i - k) = k by omega, hPk] at this
    cases this
  have hkle : k ≤ 2 * R - 1 - i - e := by
    apply Classical.byContradiction
    intro hc
    have := he2 (2 * R - 1 - i - k) (by omega)
    rw [show 2 * R - 1 - i - (2 * R - 1 - i - k) = k by omega, hPk] at this
    cases this
  by_cases hke : k = 2 * R - 1 - i - e
  · have he0 : 1 ≤ e := by omega
    have : eR R s' = e - 1 := by
      apply eREq R i (e - 1) s' hS' (by omega)
      · intro d hd
        rw [hoth _ (by omega) (by omega)]
        exact he2 d (by omega)
      · intro _
        rw [show 2 * R - 1 - i - (e - 1) = k + 1 by omega, h'k1]
        intro h; cases h
    refine ⟨by omega, by omega, fun _ => by omega⟩
  · have hk2 : k + 1 < 2 * R - 1 - i - e := by
      apply Classical.byContradiction
      intro hc
      have := he3 hlt
      rw [show 2 * R - 1 - i - e = k + 1 by omega, hEk] at this
      exact this rfl
    have : eR R s' = e := by
      apply eREq R i e s' hS' (by omega)
      · intro d hd
        rw [hoth _ (by omega) (by omega)]
        exact he2 d hd
      · intro hl
        rw [hoth _ (by omega) (by omega)]
        exact he3 hl
    refine ⟨by omega, by omega, fun h => absurd h hke⟩

/-- **An export into the empty border.** Consumer: `vStep`. -/
theorem eRExport (R i : Nat) (B : Bool) (s s' : CohortLane) (hS : sR R s = i)
    (hS' : sR R s' = i) (hi : i + 1 ≤ R) (hE : s.inp R = .E) (h' : s'.inp R = .P B)
    (hoth : ∀ q, q ≠ R → s'.inp q = s.inp q) :
    eR R s' < R - i ∧ (eR R s = R - i → eR R s' + 1 = R - i) ∧
      (eR R s < R - i → eR R s' = eR R s) := by
  obtain ⟨he1, he2, he3⟩ := eRSpec R i s hS
  generalize hEe : eR R s = e at he1 he2 he3
  by_cases hf : e = R - i
  · have : eR R s' = R - i - 1 := by
      apply eREq R i (R - i - 1) s' hS' (by omega)
      · intro d hd
        rw [hoth _ (by omega)]
        exact he2 d (by omega)
      · intro _
        rw [show 2 * R - 1 - i - (R - i - 1) = R by omega, h']
        intro h; cases h
    refine ⟨by omega, fun _ => by omega, fun h => by omega⟩
  · have hlt : e < R - i := by omega
    have hne : 2 * R - 1 - i - e ≠ R := by
      intro h
      have := he3 hlt
      rw [h, hE] at this
      exact this rfl
    have : eR R s' = e := by
      apply eREq R i e s' hS' (by omega)
      · intro d hd
        rw [hoth _ (by omega)]
        exact he2 d hd
      · intro hl
        rw [hoth _ hne]
        exact he3 hl
    refine ⟨by omega, fun h => absurd h hf, fun _ => this⟩

/-- No tail is settled in a trial shape. Consumer: `vStep`. -/
theorem shapeNoVT (R i : Nat) (s : CohortLane) (h : VShape R i s) : ¬ VT R s := by
  rintro ⟨hh, hh1, hS, _⟩
  have hq := h.2 (R + hh) (by omega) (by omega)
  by_cases h2 : 2 * R - i ≤ R + hh
  · rw [hq.2.1 h2] at hS; cases hS
  · rcases hq.2.2 (by omega) with he | hp
    · rw [he] at hS; cases hS
    · rw [hS] at hp; cases hp

/-- The removals left in a trial state. Consumer: `vStep`. -/
theorem remOf (R a i : Nat) (s : CohortLane) (hA : AlignExt R a s) (hS : VShape R i s) :
    rem R s = if a = 0 ∧ i = 0 then R + 1 else a + 1 := by
  obtain ⟨_, _, b, hw⟩ := hA
  unfold rem
  rw [hw, leadAlign, sROf R i s hS]

/-! ### Lane edge forms -/

/-- An internal window edge. Consumer: `vStep`. -/
theorem edgeInner (R : Nat) (s : CohortLane) (k : Nat) (hk : R ≤ k) (h3 : k + 1 < 2 * R) :
    cohortEdge R s k =
      { s with
        inp := cohortUpd (cohortUpd s.inp k (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
            (s.live k) (s.inp (k + 1)) (s.live (k + 1))).1) (k + 1)
          (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
            (s.live (k + 1))).2.2.1,
        live := cohortUpd (cohortUpd s.live k (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
            (s.live k) (s.inp (k + 1)) (s.live (k + 1))).2.1) (k + 1)
          (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
            (s.live (k + 1))).2.2.2 } := by
  unfold cohortEdge
  rw [if_neg (by omega), if_neg (by omega), if_pos h3]

/-- The terminal edge. Consumer: `vStep`. -/
theorem edgeTerm (R : Nat) (s : CohortLane) (k : Nat) (h4 : k + 1 = 2 * R) (_hR : 1 ≤ R) :
    cohortEdge R s k =
      { s with
        inp := cohortUpd s.inp k (cohortTermStep (s.inp k) (s.live k)).1,
        live := cohortUpd s.live k (cohortTermStep (s.inp k) (s.live k)).2 } := by
  unfold cohortEdge
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h4]

/-- Edges past the pair. Consumer: `vStep`. -/
theorem edgeFar (R : Nat) (s : CohortLane) (k : Nat) (h : 2 * R ≤ k) : cohortEdge R s k = s := by
  unfold cohortEdge
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Rewriting a lane with its own fields. Consumer: `vStep`. -/
theorem laneSame (s : CohortLane) (inp' : Nat → BankRepairDigitInSh) (live' : Nat → Bool)
    (hi : inp' = s.inp) (hl : live' = s.live) : { s with inp := inp', live := live' } = s := by
  subst hi; subst hl; rfl

/-- An update by the old values. Consumer: `vStep`. -/
theorem updSame {α : Type} (f : Nat → α) (k : Nat) (a b : α) (ha : a = f k) (hb : b = f (k + 1)) :
    cohortUpd (cohortUpd f k a) (k + 1) b = f := by
  funext q
  unfold cohortUpd
  by_cases h1 : q = k + 1
  · rw [if_pos h1, hb, h1]
  · rw [if_neg h1]
    by_cases h2 : q = k
    · rw [if_pos h2, ha, h2]
    · rw [if_neg h2]

/-- One update by the old value. Consumer: `vStep`. -/
theorem updOne {α : Type} (f : Nat → α) (k : Nat) (a : α) (ha : a = f k) : cohortUpd f k a = f := by
  funext q
  unfold cohortUpd
  by_cases h : q = k
  · rw [if_pos h, ha, h]
  · rw [if_neg h]

/-- Acceptance at the border of a trial window means an empty border. Consumer: `srcDist`. -/
theorem accBorder (R : Nat) (s : CohortLane) (hl : s.live R = false)
    (h : decide (winOf R s 0 = { i := .e, c := .off }) = true) : s.inp R = .E := by
  have h' := of_decide_eq_true h
  simp only [winOf, liftC, Nat.add_zero, hl] at h'
  revert h'
  cases s.inp R with
  | E => intro _; rfl
  | X => intro h; simp [cellIn] at h
  | P T => cases T <;> (intro h; simp [cellIn] at h)
  | S T => cases T <;> (intro h; simp [cellIn] at h)

/-- A sampled token at the source terminal and an empty carry-free border: the port letter
exports. Consumer: `vStep`. -/
theorem portExports (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (k : Nat) (h2 : k + 1 = R)
    (hl : s.live R = false) (hE : s.inp R = .E) (hd : dist R (srcLane s) = 0) :
    ∃ B, (cohortEdge R s k).inp R = .P B := by
  have hD := (dist_zero_iff R (by omega) (srcLane s)).1 hd
  have hk : R - 1 = k := by omega
  rw [hk] at hD
  obtain ⟨B, hB⟩ : ∃ B, s.out k = .D B := by
    revert hD
    show (tokOf (s.out k)).isD = true → _
    cases s.out k with
    | D T => intro _; exact ⟨T, rfl⟩
    | E => intro h; cases h
    | U => intro h; cases h
  refine ⟨B, ?_⟩
  unfold cohortEdge
  rw [if_neg (by omega), if_pos h2]
  show cohortUpd s.inp (k + 1) _ R = _
  simp only [cohortUpd, h2, if_true]
  rw [hB, ← h2, show k + 1 = R from h2, hE, hl]
  rfl

/-- **The source distance under a source letter.** Consumer: `vStep`. -/
theorem srcDist (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (k : Nat) (hk : k < R)
    (hnoexp : k + 1 = R → dist R (srcLane s) = 0 →
      decide (winOf R s 0 = { i := .e, c := .off }) = true → False) :
    dist R (srcLane (cohortEdge R s k)) ≤ dist R (srcLane s) ∧
      (dist R (srcLane s) ≠ 0 → k = srcIdx R (srcLane s) →
        dist R (srcLane (cohortEdge R s k)) + 1 ≤ dist R (srcLane s)) := by
  rw [laneSrc, if_pos hk]
  refine ⟨?_, fun hd hki => ?_⟩
  · by_cases hd : dist R (srcLane s) = 0
    · rcases dist_zero_step R hR (srcLane s)
        (decide (winOf R s 0 = { i := .e, c := .off })) k hk hd with h | ⟨h1, h2⟩
      · omega
      · exact absurd h2 (fun h => hnoexp h1 hd h)
    · exact dist_step_le R hR _ _ (SrcStep.edge k hk _) hd
  · rw [hki]
    exact (dist_step_drop R hR (srcLane s) _ hd).2

/-! ### One letter of the trial -/

/-- The nominated letters. Consumer: `vStep`, `vDrop`. -/
def Strict (R : Nat) (s : CohortLane) (k : Nat) : Prop :=
  (k + 1 < R ∧ eR R s = R - sR R s ∧ dist R (srcLane s) ≠ 0 ∧ k = srcIdx R (srcLane s)) ∨
  (k + 1 = R ∧ eR R s = R - sR R s ∧ (dist R (srcLane s) ≠ 0 → k = srcIdx R (srcLane s))) ∨
  (R ≤ k ∧ eR R s < R - sR R s ∧ k = 2 * R - 1 - sR R s - eR R s)

/-- The work of a trial state with fewer empty cells than the full run. Consumer: `vStep`. -/
theorem progPart (R : Nat) (s : CohortLane) (h : eR R s < R - sR R s) : prog R s = eR R s := by
  unfold prog; rw [if_neg (by omega)]; rfl

/-- The work is at least the empty run. Consumer: `vStep`. -/
theorem progGe (R : Nat) (s : CohortLane) : eR R s ≤ prog R s := by
  unfold prog; split <;> omega

/-- **One letter of the trial.** The successor is the target or again a trial state, the
potential does not rise, and it falls on a nominated letter. Consumer: `vMoment`. -/
theorem vStep (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (k : Nat) (hv : VI R s) :
    VT R (cohortEdge R s k) ∨
      (VI R (cohortEdge R s k) ∧
        rem R (cohortEdge R s k) * vK R + prog R (cohortEdge R s k) ≤ rem R s * vK R + prog R s ∧
        (Strict R s k → rem R (cohortEdge R s k) * vK R + prog R (cohortEdge R s k) + 1 ≤
          rem R s * vK R + prog R s)) := by
  obtain ⟨a, i, hai, hA, hS⟩ := hv
  have hsR := sROf R i s hS
  have hwin := shapeWin R i s hS
  have hrem := remOf R a i s hA hS
  have hcell := hS.2
  have hi1 := hS.1
  have hK := progLt R (cohortEdge R s k)
  have halign := alignExtStep R a (by omega) s k hA hwin
  have hgeK : rem R s * vK R ≥ vK R := by
    rw [hrem]
    have : 1 ≤ (if a = 0 ∧ i = 0 then R + 1 else a + 1) := by split <;> omega
    exact Nat.le_mul_of_pos_left _ this
  by_cases h1 : k + 1 < R
  · -- a source letter
    have hinp : (cohortEdge R s k).inp = s.inp := by unfold cohortEdge; rw [if_pos h1]
    have hlive : (cohortEdge R s k).live = s.live := by unfold cohortEdge; rw [if_pos h1]
    have hA' : AlignExt R a (cohortEdge R s k) := by
      rcases halign with ⟨h, _⟩ | ⟨B, _, _, _, hk, _⟩
      · exact h
      · omega
    have hS' : VShape R i (cohortEdge R s k) :=
      ⟨hS.1, fun q h1 h2 => by rw [hinp, hlive]; exact hS.2 q h1 h2⟩
    have hrem' := remOf R a i _ hA' hS'
    have heR := eRInp R s _ hinp
    have hsR' := sRInp R s _ hinp
    obtain ⟨hd, hds⟩ := srcDist R hR s k (by omega) (fun h => by omega)
    right
    refine ⟨⟨a, i, hai, hA', hS'⟩, ?_, ?_⟩
    · rw [hrem', ← hrem]
      unfold prog; rw [heR, hsR']
      split <;> omega
    · rintro (⟨_, hf, hd0, hki⟩ | ⟨h2, _⟩ | ⟨hk, _⟩)
      · have := hds hd0 hki
        rw [hrem', ← hrem]
        unfold prog; rw [heR, hsR', if_pos hf, if_pos hf]
        omega
      · omega
      · omega
  by_cases h2 : k + 1 = R
  · -- the port letter
    have hlR := (hcell R (by omega) (by omega)).1
    have hoth : ∀ q, q ≠ R → (cohortEdge R s k).inp q = s.inp q ∧
        (cohortEdge R s k).live q = s.live q := by
      intro q hq
      unfold cohortEdge; rw [if_neg h1, if_pos h2]
      exact ⟨by show cohortUpd s.inp (k + 1) _ q = _; simp [cohortUpd, show q ≠ k + 1 by omega],
        by show cohortUpd s.live (k + 1) _ q = _; simp [cohortUpd, show q ≠ k + 1 by omega]⟩
    have hA' : AlignExt R a (cohortEdge R s k) := by
      rcases halign with ⟨h, _⟩ | ⟨B, _, _, _, hk, _⟩
      · exact h
      · omega
    rcases srcStep R (by omega) s k hA.1 with ⟨_, hpw⟩ | ⟨hk0, _⟩ | ⟨B, ⟨_, hE, _, hP, hlP⟩, _⟩
    · obtain ⟨hiR, hlR'⟩ := hpw h2
      rw [hlR, if_neg (by simp)] at hiR
      have hinp : (cohortEdge R s k).inp = s.inp := by
        funext q; by_cases hq : q = R
        · rw [hq, hiR]
        · exact (hoth q hq).1
      have hlive : (cohortEdge R s k).live = s.live := by
        funext q; by_cases hq : q = R
        · rw [hq, hlR', hlR]
        · exact (hoth q hq).2
      have hS' : VShape R i (cohortEdge R s k) :=
        ⟨hS.1, fun q h1 h2 => by rw [hinp, hlive]; exact hS.2 q h1 h2⟩
      have hrem' := remOf R a i _ hA' hS'
      have heR := eRInp R s _ hinp
      have hsR' := sRInp R s _ hinp
      have hnoexp : k + 1 = R → dist R (srcLane s) = 0 →
          decide (winOf R s 0 = { i := .e, c := .off }) = true → False := by
        intro _ hd hacc
        have hE := accBorder R s hlR hacc
        obtain ⟨B, hB⟩ := portExports R (by omega) s k h2 hlR hE hd
        rw [hiR, hE] at hB
        cases hB
      obtain ⟨hd, hds⟩ := srcDist R hR s k (by omega) hnoexp
      right
      refine ⟨⟨a, i, hai, hA', hS'⟩, ?_, ?_⟩
      · rw [hrem', ← hrem]
        unfold prog; rw [heR, hsR']
        split <;> omega
      · rintro (⟨h1', _⟩ | ⟨_, hf, hdi⟩ | ⟨hk, _⟩)
        · omega
        · by_cases hd0 : dist R (srcLane s) = 0
          · exfalso
            have hE : s.inp R = .E := by
              obtain ⟨_, he2, _⟩ := eRSpec R i s hsR
              have := he2 (R - 1 - i) (by rw [hf] at *; omega)
              rwa [show 2 * R - 1 - i - (R - 1 - i) = R by omega] at this
            obtain ⟨B, hB⟩ := portExports R (by omega) s k h2 hlR hE hd0
            rw [hiR, hE] at hB
            cases hB
          · have := hds hd0 (hdi hd0)
            rw [hrem', ← hrem]
            unfold prog; rw [heR, hsR', if_pos hf, if_pos hf]
            omega
        · omega
    · omega
    · -- an export
      have hS' : VShape R i (cohortEdge R s k) := by
        refine ⟨hS.1, fun q hq1 hq2 => ?_⟩
        by_cases hq : q = R
        · subst hq
          refine ⟨hlP, fun h => by omega, fun _ => Or.inr (by rw [hP]; rfl)⟩
        · rw [(hoth q hq).1, (hoth q hq).2]; exact hS.2 q hq1 hq2
      have hrem' := remOf R a i _ hA' hS'
      have hsR' := sROf R i _ hS'
      obtain ⟨hx1, hx2, hx3⟩ := eRExport R i B s _ hsR hsR' (by omega) hE hP
        (fun q hq => (hoth q hq).1)
      have hp' := progPart R _ (by rw [hsR']; exact hx1)
      have hpg := progGe R s
      right
      refine ⟨⟨a, i, hai, hA', hS'⟩, ?_, ?_⟩
      · rw [hrem', ← hrem, hp']
        have hle := (eRSpec R i s hsR).1
        by_cases hf : eR R s = R - i
        · have := hx2 hf; omega
        · have := hx3 (by omega); omega
      · rintro (⟨h1', _⟩ | ⟨_, hf, _⟩ | ⟨hk, _⟩)
        · omega
        · rw [hsR] at hf
          have := hx2 hf
          rw [hrem', ← hrem, hp']
          omega
        · omega
  by_cases h3 : k + 1 < 2 * R
  · -- an internal window edge
    have hk : R ≤ k := by omega
    have hform := edgeInner R s k hk h3
    have hck := hcell k hk (by omega)
    have hck1 := hcell (k + 1) (by omega) h3
    rw [hck.1, hck1.1] at hform
    -- the identity case
    have hid : ∀ f : BankRepairDigitInSh × Bool × BankRepairDigitInSh × Bool,
        bankRepairDigitFinStep (decide (k = R)) (s.inp k) false (s.inp (k + 1)) false = f →
        f = (s.inp k, false, s.inp (k + 1), false) → cohortEdge R s k = s := by
      intro f hf hfe
      rw [hform, hf, hfe]
      exact laneSame s _ _ (updSame _ _ _ _ rfl rfl)
        (updSame _ _ _ _ hck.1.symm hck1.1.symm)
    have hidCase : cohortEdge R s k = s → ¬ Strict R s k →
        VT R (cohortEdge R s k) ∨
          (VI R (cohortEdge R s k) ∧
            rem R (cohortEdge R s k) * vK R + prog R (cohortEdge R s k) ≤ rem R s * vK R + prog R s ∧
            (Strict R s k → rem R (cohortEdge R s k) * vK R + prog R (cohortEdge R s k) + 1 ≤
              rem R s * vK R + prog R s)) := by
      intro he hns
      rw [he]
      exact Or.inr ⟨⟨a, i, hai, hA, hS⟩, Nat.le_refl _, fun h => absurd h hns⟩
    obtain ⟨he1, he2, he3⟩ := eRSpec R i s hsR
    by_cases hreg : 2 * R - i ≤ k
    · have hSk := hck.2.1 hreg
      have hkR : decide (k = R) = false := by simp; omega
      apply hidCase (hid _ rfl (by rw [hkR, hSk, finS])) 
      rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
      · omega
      · omega
      · rw [hsR] at hlt hke; omega
    · rcases hck.2.2 (by omega) with hEk | hPk
      · apply hidCase (hid _ rfl (by rw [hEk, finE]))
        rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
        · omega
        · omega
        · rw [hsR] at hlt hke
          exact he3 hlt (by rw [← hke]; exact hEk)
      · obtain ⟨B, hB⟩ : ∃ B, s.inp k = .P B := by
          revert hPk; cases s.inp k with
          | P T => intro _; exact ⟨T, rfl⟩
          | _ => intro h; cases h
        by_cases hreg1 : 2 * R - i ≤ k + 1
        · -- settlement beside the settled run: a removal
          have hSk1 := hck1.2.1 hreg1
          have hkt : k = 2 * R - 1 - i := by omega
          have hi0 : 1 ≤ i := by omega
          have hinpk : (cohortEdge R s k).inp k = .S B := by
            rw [hform, hB, hSk1, finPS]; simp [cohortUpd]
          have hinpk1 : (cohortEdge R s k).inp (k + 1) = .S false := by
            rw [hform, hB, hSk1, finPS]; simp [cohortUpd]
          have hlv : (cohortEdge R s k).live = s.live := by
            rw [hform, hB, hSk1, finPS]
            exact updSame _ _ _ _ hck.1.symm hck1.1.symm
          have hothI : ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).inp q = s.inp q := by
            intro q hq hq'
            rw [hform]; simp [cohortUpd, hq, hq']
          rcases halign with ⟨_, _, hls⟩ | ⟨B', _, hB', hA', _, _, hPk', _, _⟩
          · exfalso
            have := hls.1 hk h3
            rw [hinpk, hinpk1, hB, hSk1] at this
            simp [pwI] at this
          · rw [hB] at hPk'
            cases hPk'
            by_cases ha0 : a = 0
            · left
              refine ⟨R - 1 - i, by omega, ?_, ?_⟩
              · rw [show R + (R - 1 - i) = k by omega, hinpk, hB', ha0]
                rfl
              · rw [show R + (R - 1 - i) = k by omega, hlv]; exact hck.1
            · right
              have hBf : B = false := by rw [hB']; simp [ha0]
              rw [if_neg ha0] at hA'
              have hS' : VShape R (i + 1) (cohortEdge R s k) := by
                refine ⟨by omega, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, ?_, ?_⟩⟩
                · intro hq
                  by_cases hqk : q = k
                  · rw [hqk, hinpk, hBf]
                  · by_cases hqk1 : q = k + 1
                    · rw [hqk1, hinpk1]
                    · rw [hothI q hqk hqk1]; exact (hcell q hq1 hq2).2.1 (by omega)
                · intro hq
                  rw [hothI q (by omega) (by omega)]
                  exact (hcell q hq1 hq2).2.2 (by omega)
              have hrem' := remOf R (a - 1) (i + 1) _ hA' hS'
              refine ⟨⟨a - 1, i + 1, by omega, hA', hS'⟩, ?_, fun _ => ?_⟩
              · rw [hrem', hrem, if_neg (by omega), if_neg (by omega)]
                have : (a - 1 + 1) * vK R + vK R ≤ (a + 1) * vK R := by
                  rw [show a + 1 = a - 1 + 1 + 1 by omega, Nat.add_mul (a - 1 + 1) 1, Nat.one_mul]
                  exact Nat.le_refl _
                omega
              · rw [hrem', hrem, if_neg (by omega), if_neg (by omega)]
                have : (a - 1 + 1) * vK R + vK R ≤ (a + 1) * vK R := by
                  rw [show a + 1 = a - 1 + 1 + 1 by omega, Nat.add_mul (a - 1 + 1) 1, Nat.one_mul]
                  exact Nat.le_refl _
                omega
        · rcases hck1.2.2 (by omega) with hEk1 | hPk1
          · -- a move
            have hinpk : (cohortEdge R s k).inp k = .E := by
              rw [hform, hB, hEk1, finPE]; simp [cohortUpd]
            have hinpk1 : (cohortEdge R s k).inp (k + 1) = .P B := by
              rw [hform, hB, hEk1, finPE]; simp [cohortUpd]
            have hlv : (cohortEdge R s k).live = s.live := by
              rw [hform, hB, hEk1, finPE]
              exact updSame _ _ _ _ hck.1.symm hck1.1.symm
            have hothI : ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).inp q = s.inp q := by
              intro q hq hq'
              rw [hform]; simp [cohortUpd, hq, hq']
            have hA' : AlignExt R a (cohortEdge R s k) := by
              rcases halign with ⟨h, _⟩ | ⟨B', _, _, _, _, _, _, hset, _⟩
              · exact h
              · have := (hset h3).1; rw [hEk1] at this; cases this
            have hS' : VShape R i (cohortEdge R s k) := by
              refine ⟨hS.1, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, ?_, ?_⟩⟩
              · intro hq
                rw [hothI q (by omega) (by omega)]; exact (hcell q hq1 hq2).2.1 hq
              · intro hq
                by_cases hqk : q = k
                · rw [hqk, hinpk]; exact Or.inl rfl
                · by_cases hqk1 : q = k + 1
                  · rw [hqk1, hinpk1]; exact Or.inr rfl
                  · rw [hothI q hqk hqk1]; exact (hcell q hq1 hq2).2.2 hq
            have hrem' := remOf R a i _ hA' hS'
            have hsR' := sROf R i _ hS'
            obtain ⟨hm1, hm2, hm3⟩ := eRMove R i k B s _ hsR hsR' (by omega) hk (by omega) hB hEk1
              hinpk hinpk1 hothI
            have hp' := progPart R _ (by rw [hsR']; exact hm1)
            have hpg := progGe R s
            right
            refine ⟨⟨a, i, hai, hA', hS'⟩, ?_, ?_⟩
            · rw [hrem', ← hrem, hp']; omega
            · rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
              · omega
              · omega
              · rw [hsR] at hlt hke
                have := hm3 hke
                rw [hrem', ← hrem, hp']; omega
          · obtain ⟨B1, hB1⟩ : ∃ B1, s.inp (k + 1) = .P B1 := by
              revert hPk1; cases s.inp (k + 1) with
              | P T => intro _; exact ⟨T, rfl⟩
              | _ => intro h; cases h
            apply hidCase (hid _ rfl (by rw [hB, hB1, finPP]))
            rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
            · omega
            · omega
            · rw [hsR] at hlt hke
              by_cases he0 : eR R s = 0
              · omega
              · have := he2 (eR R s - 1) (by omega)
                rw [show 2 * R - 1 - i - (eR R s - 1) = k + 1 by omega, hB1] at this
                cases this
  by_cases h4 : k + 1 = 2 * R
  · -- the terminal edge
    have hform := edgeTerm R s k h4 (by omega)
    have hck := hcell k (by omega) (by omega)
    rw [hck.1] at hform
    have hid : (cohortTermStep (s.inp k) false) = (s.inp k, false) → cohortEdge R s k = s := by
      intro hf
      rw [hform, hf]
      exact laneSame s _ _ (updOne _ _ _ rfl) (updOne _ _ _ hck.1.symm)
    obtain ⟨he1, he2, he3⟩ := eRSpec R i s hsR
    by_cases hi0 : i = 0
    · subst hi0
      rcases hck.2.2 (by omega) with hEk | hPk
      · have he := hid (by rw [hEk]; rfl)
        rw [he]
        refine Or.inr ⟨⟨a, 0, hai, hA, hS⟩, Nat.le_refl _, ?_⟩
        rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
        · omega
        · omega
        · rw [hsR] at hlt hke
          exact absurd (by rw [show 2 * R - 1 - 0 - eR R s = k by omega]; exact hEk) (he3 hlt)
      · obtain ⟨B, hB⟩ : ∃ B, s.inp k = .P B := by
          revert hPk; cases s.inp k with
          | P T => intro _; exact ⟨T, rfl⟩
          | _ => intro h; cases h
        have hinpk : (cohortEdge R s k).inp k = retireOf (.P B) := by
          rw [hform, hB]; cases B <;> simp [cohortUpd, cohortTermStep, retireOf]
        have hlv : (cohortEdge R s k).live = s.live := by
          rw [hform, hB]
          exact updOne _ _ _ (by rw [hck.1]; cases B <;> rfl)
        have hothI : ∀ q, q ≠ k → (cohortEdge R s k).inp q = s.inp q := by
          intro q hq; rw [hform]; simp [cohortUpd, hq]
        rcases halign with ⟨_, _, hls⟩ | ⟨B', _, hB', hA', _, _, hPk', _, _⟩
        · exfalso
          have := hls.2 h4
          rw [hinpk, hB] at this
          cases B <;> simp [pwI, retireOf] at this
        · rw [hB] at hPk'
          cases hPk'
          right
          by_cases ha0 : a = 0
          · have hBt : B = true := by rw [hB', ha0]; rfl
            rw [if_pos ha0] at hA'
            have hS' : VShape R 0 (cohortEdge R s k) := by
              refine ⟨by omega, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1,
                fun h => by omega, fun _ => ?_⟩⟩
              by_cases hqk : q = k
              · rw [hqk, hinpk, hBt]; exact Or.inl rfl
              · rw [hothI q hqk]; exact (hcell q hq1 hq2).2.2 (by omega)
            have hrem' := remOf R (R - 1) 0 _ hA' hS'
            have hle : R * vK R + vK R ≤ (R + 1) * vK R := by
              rw [Nat.add_mul, Nat.one_mul]; exact Nat.le_refl _
            refine ⟨⟨R - 1, 0, by omega, hA', hS'⟩, ?_, fun _ => ?_⟩
            · rw [hrem', hrem, if_neg (by omega), if_pos ⟨ha0, rfl⟩,
                show R - 1 + 1 = R by omega]; omega
            · rw [hrem', hrem, if_neg (by omega), if_pos ⟨ha0, rfl⟩,
                show R - 1 + 1 = R by omega]; omega
          · have hBf : B = false := by rw [hB']; simp [ha0]
            rw [if_neg ha0] at hA'
            have hS' : VShape R 1 (cohortEdge R s k) := by
              refine ⟨by omega, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, ?_, ?_⟩⟩
              · intro hq
                rw [show q = k by omega, hinpk, hBf]; rfl
              · intro hq
                rw [hothI q (by omega)]; exact (hcell q hq1 hq2).2.2 (by omega)
            have hrem' := remOf R (a - 1) 1 _ hA' hS'
            have hle : (a - 1 + 1) * vK R + vK R ≤ (a + 1) * vK R := by
              rw [show a + 1 = a - 1 + 1 + 1 by omega, Nat.add_mul (a - 1 + 1) 1, Nat.one_mul]
              exact Nat.le_refl _
            have ha1 := hA.2.1
            refine ⟨⟨a - 1, 1, by omega, hA', hS'⟩, ?_, fun _ => ?_⟩
            · rw [hrem', hrem, if_neg (by omega), if_neg (by omega)]; omega
            · rw [hrem', hrem, if_neg (by omega), if_neg (by omega)]; omega
    · have hSk := hck.2.1 (by omega)
      have he := hid (by rw [hSk]; rfl)
      rw [he]
      refine Or.inr ⟨⟨a, i, hai, hA, hS⟩, Nat.le_refl _, ?_⟩
      rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
      · omega
      · omega
      · rw [hsR] at hlt hke; omega
  · -- past the pair
    rw [edgeFar R s k (by omega)]
    refine Or.inr ⟨⟨a, i, hai, hA, hS⟩, Nat.le_refl _, ?_⟩
    rintro (⟨h1', _⟩ | ⟨h2', _⟩ | ⟨_, hlt, hke⟩)
    · omega
    · omega
    · rw [hsR] at hlt hke; omega

/-! ### The nominated letter and the moment -/

/-- **A nominated letter of every trial state.** Consumer: `vMoment`. -/
theorem vDrop (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (hv : VI R s) :
    ∃ k, k < 2 * R ∧ Strict R s k := by
  obtain ⟨a, i, hai, _, hS⟩ := hv
  have hsR := sROf R i s hS
  have he1 := (eRSpec R i s hsR).1
  by_cases he : eR R s < R - sR R s
  · refine ⟨2 * R - 1 - sR R s - eR R s, by omega, Or.inr (Or.inr ⟨by omega, he, rfl⟩)⟩
  · have hf : eR R s = R - sR R s := by rw [hsR] at he ⊢; omega
    by_cases hd : dist R (srcLane s) = 0
    · exact ⟨R - 1, by omega, Or.inr (Or.inl ⟨by omega, hf, fun h => absurd hd h⟩)⟩
    · have hlt := (dist_step_drop R hR (srcLane s)
        (decide (winOf R s 0 = { i := .e, c := .off })) hd).1
      by_cases h1 : srcIdx R (srcLane s) + 1 < R
      · exact ⟨_, by omega, Or.inl ⟨h1, hf, hd, rfl⟩⟩
      · exact ⟨_, by omega, Or.inr (Or.inl ⟨by omega, hf, fun _ => rfl⟩)⟩

/-- The potential off the target. Consumer: `vMoment`. -/
theorem vPotOff (R : Nat) (s : CohortLane) (h : ¬ VT R s) : vPot R s = rem R s * vK R + prog R s := by
  unfold vPot; rw [if_neg h]

/-- The removals left are positive. Consumer: `vMoment`. -/
theorem remPos (R : Nat) (s : CohortLane) (hv : VI R s) : 1 ≤ rem R s := by
  obtain ⟨a, i, _, hA, hS⟩ := hv
  rw [remOf R a i s hA hS]; split <;> omega

/-- One letter of the trial on the potential. Consumer: `vMoment`. -/
theorem vLetter (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (k : Nat) (hv : VI R s) :
    (VT R (cohortEdge R s k) ∨ VI R (cohortEdge R s k)) ∧
      vPot R (cohortEdge R s k) ≤ vPot R s ∧
      (Strict R s k → vPot R (cohortEdge R s k) + 1 ≤ vPot R s) := by
  have hnt : ¬ VT R s := by obtain ⟨a, i, _, _, hS⟩ := hv; exact shapeNoVT R i s hS
  have hp := vPotOff R s hnt
  have hr := remPos R s hv
  have hK : 1 ≤ rem R s * vK R := Nat.le_trans hr (Nat.le_mul_of_pos_right _ (by unfold vK; omega))
  rcases vStep R hR s k hv with ht | ⟨hv', hle, hlt⟩
  · have : vPot R (cohortEdge R s k) = 0 := by unfold vPot; rw [if_pos ht]
    refine ⟨Or.inl ht, by omega, fun _ => by omega⟩
  · have hnt' : ¬ VT R (cohortEdge R s k) := by
      obtain ⟨a, i, _, _, hS⟩ := hv'; exact shapeNoVT R i _ hS
    rw [vPotOff R _ hnt', hp]
    exact ⟨Or.inr hv', hle, hlt⟩

/-- **The renewal preparation on the lane.** From every trial state the target (a tail settled
at an offset `h ≤ R - 2`, carry-free) is reached with `E[z^{T_V}] ≤ w^{vPot}`.
Consumer: `vMomentCoupled`. -/
theorem vMoment {n : Nat} (R : Nat) (hR : 3 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (s : CohortLane) (hs : VI R s) :
    MomentBoundQ (releaseNext R edgeOf) (VT R) N (N ^ vPot R s) ((N - n) ^ vPot R s) s := by
  let P' : CohortLane → Prop := fun y => VT R y ∨ ¬ VI R y
  have hopt : ∀ y, VI R y → ∀ o : Option Nat,
      (VT R (cohortLaneStep R y o) ∨ VI R (cohortLaneStep R y o)) ∧
        vPot R (cohortLaneStep R y o) ≤ vPot R y := by
    intro y hy o
    cases o with
    | none => exact ⟨Or.inr hy, Nat.le_refl _⟩
    | some k => exact ⟨(vLetter R hR y k hy).1, (vLetter R hR y k hy).2.1⟩
  have hex : ∀ y, ∃ e : Fin n, ¬ P' y → vPot R (releaseNext R edgeOf y e) + 1 ≤ vPot R y := by
    intro y
    by_cases hy : P' y
    · exact ⟨site 0, fun h => absurd hy h⟩
    · have h2 : VI R y := Classical.byContradiction fun h => hy (Or.inr h)
      obtain ⟨k, hk, hst⟩ := vDrop R hR y h2
      refine ⟨site k, fun _ => ?_⟩
      show vPot R (cohortLaneStep R y (edgeOf (site k))) + 1 ≤ _
      rw [hedge k hk]
      exact (vLetter R hR y k h2).2.2 hst
  have hP' := momentOfPotential (releaseNext R edgeOf) P' N (vPot R)
    (fun y => Classical.choose (hex y)) hn hN
    (fun y hy => Classical.choose_spec (hex y) hy)
    (fun y hy e => by
      have h2 : VI R y := Classical.byContradiction fun h => hy (Or.inr h)
      exact (hopt y h2 (edgeOf e)).2) s
  exact momentSimQ (releaseNext R edgeOf) (releaseNext R edgeOf)
    (fun a b => a = b ∧ (VT R a ∨ VI R a)) (VT R) P' N _ _
    (fun a b e hab hna => by
      obtain ⟨rfl, hi⟩ := hab
      rcases hi with hi | hi
      · exact absurd hi hna
      · exact ⟨rfl, (hopt a hi (edgeOf e)).1⟩)
    (fun a b hab hg => by
      obtain ⟨rfl, hi⟩ := hab
      rcases hg with hg | hg
      · exact hg
      · rcases hi with hi | hi
        · exact hi
        · exact absurd hi hg) s s ⟨rfl, Or.inr hs⟩ hP'

/-! ### Entry and the coupled chain -/

/-- **The alignment is kept** by every letter while the window invariants hold (phases U and
retirement keep them, `L3.PacketMomentU.winKeepCoupled`). Consumer: the entry of `V` at the
packet-only cut (`viOfPacketOnly`). -/
theorem alignKeep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : ∃ a, AlignExt R a s)
    (hw : Inv R (winOf R s) ∧ Barrier R (winOf R s)) :
    ∃ a, AlignExt R a (cohortEdge R s k) := by
  obtain ⟨a, ha⟩ := h
  rcases alignExtStep R a hR s k ha hw with ⟨h1, _⟩ | ⟨_, _, _, h1, _⟩
  · exact ⟨a, h1⟩
  · exact ⟨_, h1⟩

/-- **Entry of `V`**: an aligned packet-only cut is a trial state with an empty settled run.
Consumer: `vMomentCoupled` (start of the renewal preparation after `retMomentCoupled`). -/
theorem viOfPacketOnly (R a : Nat) (s : CohortLane) (hA : AlignExt R a s)
    (hP : L3.PacketMomentRetire.PacketOnly R s) : VI R s := by
  have ha := hA.2.1
  refine ⟨a, 0, by omega, hA, by omega, fun q hq1 hq2 => ?_⟩
  obtain ⟨h1, h2⟩ := hP (q - R) (by omega)
  have hq : R + (q - R) = q := by omega
  simp only [winOf, liftC, hq, L3.PacketMomentRetire.obW] at h1 h2
  have hl : s.live q = false := by
    cases hlq : s.live q with
    | false => rfl
    | true => rw [hlq] at h2; simp at h2
  refine ⟨hl, fun h => absurd h (by omega), fun _ => ?_⟩
  revert h1 h2
  cases s.inp q with
  | E => intro _ _; exact Or.inl rfl
  | P T => intro _ _; exact Or.inr rfl
  | X => intro _ h; simp [cellIn] at h
  | S T => cases T <;> (intro h _; simp [cellIn, Inp.isS] at h)

/-- The potential of a trial state is below the budget. Consumer: `vMomentCoupled`. -/
theorem vPotLe (R : Nat) (s : CohortLane) (hv : VI R s) : vPot R s ≤ (R + 2) * vK R := by
  unfold vPot
  split
  · exact Nat.zero_le _
  · obtain ⟨a, i, _, hA, _⟩ := hv
    have h1 := remLe R s a hA
    have h2 := progLt R s
    have h3 : rem R s * vK R ≤ (R + 1) * vK R := Nat.mul_le_mul_right _ h1
    have h4 : (R + 2) * vK R = (R + 1) * vK R + vK R := by rw [Nat.succ_mul]
    omega

/-- **Lemma e-packet, the renewal preparation `V`, on the coupled chain.** From every layout
state whose lane is a trial state (an aligned packet-only cut by `viOfPacketOnly`), a tail is
settled carry-free at an offset `h ≤ R - 2` of the target window (`h ≥ 1`: the misaligned cut
`RacePend`; `h = 0`: the aligned border settlement) with
`E[z^{T_V}] ≤ w^{(R+2)(2R+2)}`, `w = N/(N-n)`, uniformly over source registers and audit.
Consumer: the per-pair moment (`E[z^{T_pair}] < 40`, Lemma e-max), the `V` of the renewal. -/
theorem vMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : VI R (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VT R (laneOfState ring hbank root lane src R y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hlane := vMoment R hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (laneOfState ring hbank root lane src R x) hs
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => VT R (laneOfState ring hbank root lane src R y)) (VT R) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (vPotLe R _ hs)

/-- **The outcome of `V` read on the coupled chain**: the misaligned-tail cut `RacePend` at an
offset `h ≤ R - 2` (`h = 0` is the aligned border settlement). Consumer: the start of the fair
race (`L3.DigitPacketRace.misalignedRace`) after `vMomentCoupled`. -/
theorem vtRace {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : VT R (laneOfState ring hbank root lane src R y)) :
    ∃ h, h + 1 < R ∧ L3.DigitPacketRace.RacePend ring hbank root lane src R h y := by
  obtain ⟨h, hh, h1, h2⟩ := h
  exact ⟨h, hh, h1, h2⟩

end L3.PacketMomentV

#print axioms L3.PacketMomentV.vStep
#print axioms L3.PacketMomentV.vMoment
#print axioms L3.PacketMomentV.alignKeep
#print axioms L3.PacketMomentV.viOfPacketOnly
#print axioms L3.PacketMomentV.vMomentCoupled
#print axioms L3.PacketMomentV.vtRace
