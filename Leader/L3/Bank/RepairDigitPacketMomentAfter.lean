import Leader.L3.Bank.RepairDigitPacketMomentFinish

/-!
# Lemma e-packet: the success continuation after the outgoing race edge wins

repair.tex, the renewal trial: "If the outgoing edge wins, the tail becomes a front before a
younger packet settles. That front erases only the older suffix; the intact younger prefix begins
at a group boundary. At most `r` front services and the aligned preparation finish a strict
group."

At the misaligned-tail cut of the trial (`L3.PacketMomentVSerial.VTAt R m`, offset
`h = R - 1 - m`, `1 ≤ h ≤ R - 2`) the tail is settled at cell `f = R + h = 2R - 1 - m`, its older
suffix is settled non-tails on `f + 1, …, 2R - 1`, and only empty cells and moving packets are to
its left, carry-free.  When the outgoing edge `f` fires first:

* `frontOfRace`: the tail becomes a front `X` at `f` (`FrontAt R f`), the queue alignment index is
  unchanged (no packet is removed), and the window invariants are kept;
* `frontStep`: from `FrontAt R f`, the front's own edge `f` moves it into the settled non-tail at
  `f + 1` (erasing that operand) or, at `f = 2R - 1`, the terminal row deletes it; every other edge
  keeps `FrontAt R f`: a moving packet cannot settle behind the front (settlement needs a settled
  responder, and the front is not one), and the settled suffix is not touched;
* `frontWStep`: no packet is removed along the phase, so the queue alignment index is constant;
* `frontMomentCoupled`: from the front, the window is cleared (`ADone`: carry-free, empty cells
  and moving packets only) with the same alignment index, `E[z^T] ≤ w^R`;
* at the cleared window the queue begins at a group boundary (index `R - 1`, the index after the
  removal of a tail), so it is a trial state of index `R - 1` (`viAtOfCleared`) and the renewal
  trial ends in the aligned group (`VTAt R (R - 1)` = `L3.PacketMomentFinish.AGroup`) with
  `E[z^T] ≤ w^{(R+2)(2R+2)}` (`L3.PacketMomentVSerial.vMomentAtCoupled`);
* `afterRaceGroupMoment`: from the race state, after the outgoing edge, the aligned group is
  reached with `E[z^T] ≤ w^{R + (R+2)(2R+2)}`; `afterRaceMoment`: composed with any success
  target `P` whose moment from every layout aligned-group state is at most `w^{B_s}`, the
  continuation has `E[z^T] ≤ w^{afterBudget R + B_s}`, `afterBudget R = 2R² + 7R + 4`;
  `afterRaceDoneMoment`: with the aligned finish, `E[z^T] ≤ w^{2R² + 8R + 5}` to `ADone`;
* `afterBudgetShort`: `11 (2R² + 8R + 5) ≤ 2 C_R + 1` for `R ≥ 3`, the post-race hypothesis
  `11 B_a ≤ 2C + 1` of `L3.PacketMomentWide.attemptLoopWide`; the audit receipt has the room
  `4R⁴ + 16R³ - 16R² - 66R - 46` of `2 C_R + 1` left (divided by `11`).

The race class needs the alignment index `R - 1` at the misaligned cut (the removal that settles
the tail is a tail, `L3.PacketMomentPending.alignExtStep` with `a = 0`).
-/

namespace L3.PacketMomentAfter

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
open L3.PacketMomentPending
open L3.PacketMomentU
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentPrep
open L3.PacketMomentFinish
open L3.DigitPacketOrder

/-! ### The front phase on the lane -/

/-- One target cell of the front phase: carry-free; the front at `f`, settled non-tails to its
right, empty cells and moving packets to its left. Consumer: `FrontAt`. -/
def FrontCell (f q : Nat) (i : BankRepairDigitInSh) (l : Bool) : Prop :=
  l = false ∧ (q = f → i = .X) ∧ (f < q → i = .S false) ∧ (q < f → i = .E ∨ isPI i = true)

/-- **The front at `f`** erasing the older suffix of the outcome tail. Consumer: `frontStep`,
`FrontW`. -/
def FrontAt (R f : Nat) (s : CohortLane) : Prop :=
  R ≤ f ∧ f < 2 * R ∧ ∀ q, R ≤ q → q < 2 * R → FrontCell f q (s.inp q) (s.live q)

/-- The front with the aligned queue at index `a` and the window invariants. Consumer:
`frontMoment`. -/
def FrontW (R a f : Nat) (s : CohortLane) : Prop :=
  FrontAt R f s ∧ AlignExt R a s ∧ Inv R (winOf R s) ∧ Barrier R (winOf R s)

/-- The cleared window with the aligned queue at index `a` and the window invariants. Consumer:
`frontMoment`, `viAtOfCleared`. -/
def DoneW (R a : Nat) (s : CohortLane) : Prop :=
  ADone R s ∧ AlignExt R a s ∧ Inv R (winOf R s) ∧ Barrier R (winOf R s)

/-- A moving-or-empty cell left of the front. Consumer: `frontStep`. -/
theorem frontCellEP (f q : Nat) (i : BankRepairDigitInSh) (hq : q < f)
    (hi : i = .E ∨ isPI i = true) : FrontCell f q i false :=
  ⟨rfl, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => hi⟩

/-- The front cell. Consumer: `frontStep`, `frontOfRace`. -/
theorem frontCellX (f q : Nat) (hq : q = f) : FrontCell f q .X false :=
  ⟨rfl, fun _ => rfl, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- A settled non-tail right of the front. Consumer: `frontStep`, `frontOfRace`. -/
theorem frontCellS (f q : Nat) (hq : f < q) : FrontCell f q (.S false) false :=
  ⟨rfl, fun h => absurd h (by omega), fun _ => rfl, fun h => absurd h (by omega)⟩

/-! ### The literal rows on the phase -/

/-- Delivery into the border keeps a front or a moving-or-empty border, carry-free. Consumer:
`frontStep`. -/
theorem delRow (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) :
    (bankRepairDigitDelStep ox iy false).2.2 = false ∧
      (iy = .X → (bankRepairDigitDelStep ox iy false).2.1 = .X) ∧
      (iy = .E ∨ isPI iy = true →
        (bankRepairDigitDelStep ox iy false).2.1 = .E ∨
          isPI (bankRepairDigitDelStep ox iy false).2.1 = true) := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, isPI]

/-- Two moving-or-empty cells stay moving-or-empty and carry-free. Consumer: `frontStep`. -/
theorem finEP (bx : Bool) (ix iy : BankRepairDigitInSh) (hx : ix = .E ∨ isPI ix = true)
    (hy : iy = .E ∨ isPI iy = true) :
    (bankRepairDigitFinStep bx ix false iy false).2.1 = false ∧
      (bankRepairDigitFinStep bx ix false iy false).2.2.2 = false ∧
      ((bankRepairDigitFinStep bx ix false iy false).1 = .E ∨
        isPI (bankRepairDigitFinStep bx ix false iy false).1 = true) ∧
      ((bankRepairDigitFinStep bx ix false iy false).2.2.1 = .E ∨
        isPI (bankRepairDigitFinStep bx ix false iy false).2.2.1 = true) := by
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp_all [bankRepairDigitFinStep, isPI]

/-- A moving-or-empty cell behind the front leaves both unchanged. Consumer: `frontStep`. -/
theorem finEPX (bx : Bool) (ix : BankRepairDigitInSh) (hx : ix = .E ∨ isPI ix = true) :
    bankRepairDigitFinStep bx ix false .X false = (ix, false, .X, false) := by
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> simp_all [bankRepairDigitFinStep, isPI]

/-- The front moves into a settled operand and erases it. Consumer: `frontStep`. -/
theorem finXS (bx : Bool) :
    bankRepairDigitFinStep bx .X false (.S false) false = (.E, false, .X, false) := by
  cases bx <;> rfl

/-- Two settled non-tails off the border are kept. Consumer: `frontStep`. -/
theorem finSS : bankRepairDigitFinStep false (.S false) false (.S false) false =
    (.S false, false, .S false, false) := rfl

/-- The outcome tail off the border becomes a front. Consumer: `frontOfRace`. -/
theorem finTS : bankRepairDigitFinStep false (.S true) false (.S false) false =
    (.X, false, .S false, false) := rfl

/-! ### One letter of the front phase -/

/-- Unchanged cells keep their front class. Consumer: `frontStep`. -/
theorem frontKeepCell (f f' q : Nat) (i : BankRepairDigitInSh) (l : Bool)
    (h : FrontCell f q i l) (hq : q ≠ f) (hq' : q ≠ f + 1) (hf : f' = f ∨ f' = f + 1) :
    FrontCell f' q i l := by
  obtain ⟨hl, -, hS, hE⟩ := h
  refine ⟨hl, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · omega
  · exact hS (by omega)
  · exact hE (by omega)

/-- **One letter of the front phase**: the front's own edge moves it right (or, on the last cell,
the terminal row deletes it and the window is cleared); every other edge keeps the phase.
Consumer: `frontWStep`. -/
theorem frontStep (R f k : Nat) (s : CohortLane) (h : FrontAt R f s) :
    (k = f → f + 1 < 2 * R → FrontAt R (f + 1) (cohortEdge R s k)) ∧
      (k = f → f + 1 = 2 * R → ADone R (cohortEdge R s k)) ∧
      (k ≠ f → FrontAt R f (cohortEdge R s k)) := by
  obtain ⟨hf1, hf2, hc⟩ := h
  by_cases e1 : k + 1 < R
  · obtain ⟨hi, hl⟩ := edgePipe R k s e1
    refine ⟨fun hk => absurd hk (by omega), fun hk => absurd hk (by omega),
      fun _ => ⟨hf1, hf2, fun q h1 h2 => ?_⟩⟩
    rw [hi, hl]
    exact hc q h1 h2
  by_cases e2 : k + 1 = R
  · obtain ⟨hi, hl⟩ := edgeDel R k s e2
    refine ⟨fun hk => absurd hk (by omega), fun hk => absurd hk (by omega),
      fun _ => ⟨hf1, hf2, fun q h1 h2 => ?_⟩⟩
    rw [hi, hl]
    by_cases hq : q = k + 1
    · simp only [cohortUpd, hq, if_true]
      obtain ⟨hl0, hX, -, hE⟩ := hc (k + 1) (by omega) (by omega)
      rw [hl0]
      obtain ⟨d1, d2, d3⟩ := delRow (s.out k) (s.inp (k + 1))
      rw [d1]
      by_cases hqf : k + 1 = f
      · rw [d2 (hX hqf)]
        exact frontCellX f _ hqf
      · exact frontCellEP f _ _ (by omega) (d3 (hE (by omega)))
    · simp only [cohortUpd, if_neg hq]
      exact hc q h1 h2
  by_cases e3 : k + 1 < 2 * R
  · have hk : R ≤ k := by omega
    obtain ⟨⟨ik, lk⟩, ⟨ik1, lk1⟩, hoth⟩ := finCells R k s hk e3
    obtain ⟨hl0, hX0, hS0, hE0⟩ := hc k hk (by omega)
    obtain ⟨hl1, hX1, hS1, hE1⟩ := hc (k + 1) (by omega) e3
    have hfin : finOf R s k = bankRepairDigitFinStep (decide (k = R)) (s.inp k) false
        (s.inp (k + 1)) false := by
      unfold finOf; rw [hl0, hl1]
    -- the template: the two cells of the edge, the rest unchanged
    have tmpl : ∀ f', (f' = f ∨ f' = f + 1) →
        FrontCell f' k (finOf R s k).1 (finOf R s k).2.1 →
        FrontCell f' (k + 1) (finOf R s k).2.2.1 (finOf R s k).2.2.2 →
        (∀ q, R ≤ q → q < 2 * R → q ≠ k → q ≠ k + 1 →
          FrontCell f' q (s.inp q) (s.live q)) →
        ∀ q, R ≤ q → q < 2 * R →
          FrontCell f' q ((cohortEdge R s k).inp q) ((cohortEdge R s k).live q) := by
      intro f' _ hk0 hk1 hrest q h1 h2
      by_cases hqk : q = k
      · rw [hqk, ik, lk]; exact hk0
      by_cases hqk1 : q = k + 1
      · rw [hqk1, ik1, lk1]; exact hk1
      obtain ⟨a, b⟩ := hoth q (by omega)
      rw [a, b]
      exact hrest q h1 h2 hqk hqk1
    refine ⟨fun hkf hf3 => ⟨by omega, hf3, ?_⟩, fun hkf hf3 => absurd hf3 (by omega),
      fun hkf => ⟨hf1, hf2, ?_⟩⟩
    · -- the front's edge: X S → E X
      have hr : finOf R s k = (.E, false, .X, false) := by
        rw [hfin, hX0 hkf, hS1 (by omega)]
        exact finXS _
      refine tmpl (f + 1) (Or.inr rfl) ?_ ?_ ?_
      · rw [hr]; exact frontCellEP _ _ _ (by omega) (Or.inl rfl)
      · rw [hr]; exact frontCellX _ _ (by omega)
      · intro q h1 h2 hqk hqk1
        exact frontKeepCell f (f + 1) q _ _ (hc q h1 h2) (by omega) (by omega) (Or.inr rfl)
    · refine tmpl f (Or.inl rfl) ?_ ?_ (fun q h1 h2 _ _ => hc q h1 h2)
      · rcases Nat.lt_or_ge (k + 1) f with hlt | hge
        · obtain ⟨r1, -, r3, -⟩ := finEP (decide (k = R)) (s.inp k) (s.inp (k + 1))
            (hE0 (by omega)) (hE1 hlt)
          rw [hfin, r1]
          exact frontCellEP _ _ _ (by omega) r3
        · by_cases hk1 : k + 1 = f
          · rw [hfin, hX1 hk1, finEPX _ _ (hE0 (by omega))]
            exact frontCellEP _ _ _ (by omega) (hE0 (by omega))
          · have hgt : f < k := by omega
            rw [hfin, hS0 hgt, hS1 (by omega), decide_eq_false (by omega : ¬ k = R), finSS]
            exact frontCellS _ _ hgt
      · rcases Nat.lt_or_ge (k + 1) f with hlt | hge
        · obtain ⟨-, r2, -, r4⟩ := finEP (decide (k = R)) (s.inp k) (s.inp (k + 1))
            (hE0 (by omega)) (hE1 hlt)
          rw [hfin, r2]
          exact frontCellEP _ _ _ hlt r4
        · by_cases hk1 : k + 1 = f
          · rw [hfin, hX1 hk1, finEPX _ _ (hE0 (by omega))]
            exact frontCellX _ _ hk1
          · have hgt : f < k := by omega
            rw [hfin, hS0 hgt, hS1 (by omega), decide_eq_false (by omega : ¬ k = R), finSS]
            exact frontCellS _ _ (by omega)
  by_cases e4 : k + 1 = 2 * R
  · obtain ⟨hi, hl⟩ := L3.DigitPacketRelease.edgeTerm R k s e4
    obtain ⟨hl0, hX0, hS0, -⟩ := hc k (by omega) (by omega)
    refine ⟨fun hkf hf3 => absurd hf3 (by omega), fun hkf _ => fun q h1 h2 => ?_,
      fun hkf => ⟨hf1, hf2, fun q h1 h2 => ?_⟩⟩
    · rw [hi, hl]
      by_cases hq : q = k
      · simp only [cohortUpd, hq, if_true]
        rw [hX0 hkf, hl0]
        exact ⟨rfl, Or.inl rfl⟩
      · simp only [cohortUpd, if_neg hq]
        obtain ⟨hlq, -, -, hEq⟩ := hc q h1 h2
        exact ⟨hlq, hEq (by omega)⟩
    · rw [hi, hl]
      by_cases hq : q = k
      · simp only [cohortUpd, hq, if_true]
        rw [hS0 (by omega), hl0]
        exact frontCellS _ _ (by omega)
      · simp only [cohortUpd, if_neg hq]
        exact hc q h1 h2
  · rw [cohortEdgeFar R k s (by omega)]
    exact ⟨fun hkf => absurd hkf (by omega), fun hkf => absurd hkf (by omega),
      fun _ => ⟨hf1, hf2, hc⟩⟩

/-- **No packet is removed along the front phase**: the alignment index is constant, and the
window invariants are kept. Consumer: `frontWStep`. -/
theorem frontAlignKeep (R a f k : Nat) (hR : 2 ≤ R) (s : CohortLane) (h : FrontW R a f s) :
    AlignExt R a (cohortEdge R s k) ∧ Inv R (winOf R (cohortEdge R s k)) ∧
      Barrier R (winOf R (cohortEdge R s k)) := by
  obtain ⟨⟨hf1, hf2, hc⟩, hA, hI, hB⟩ := h
  refine ⟨?_, winKeep R hR s (some k) ⟨hI, hB⟩⟩
  rcases alignExtStep R a hR s k hA ⟨hI, hB⟩ with ⟨hA', _, _⟩ |
      ⟨B, _, _, _, hk1, hk2, hP, hS, hT⟩
  · exact hA'
  · exfalso
    obtain ⟨-, hX, hSf, hE⟩ := hc k hk1 hk2
    by_cases hkf : k = f
    · rw [hX hkf] at hP; cases hP
    by_cases hgt : f < k
    · rw [hSf hgt] at hP; cases hP
    have hlt : k < f := by omega
    have hk3 : k + 1 < 2 * R := by omega
    obtain ⟨-, hX1, -, hE1⟩ := hc (k + 1) (by omega) hk3
    have hsi := (hS hk3).1
    by_cases hk1f : k + 1 = f
    · rw [hX1 hk1f] at hsi; simp [isSI] at hsi
    · rcases hE1 (by omega) with he | hp
      · rw [he] at hsi; simp [isSI] at hsi
      · revert hsi hp
        cases s.inp (k + 1) <;> simp [isSI, isPI]

/-- One letter on the front phase with the aligned queue. Consumer: `frontStepO`. -/
theorem frontWStep (R a f k : Nat) (hR : 2 ≤ R) (s : CohortLane) (h : FrontW R a f s) :
    (k = f → f + 1 < 2 * R → FrontW R a (f + 1) (cohortEdge R s k)) ∧
      (k = f → f + 1 = 2 * R → DoneW R a (cohortEdge R s k)) ∧
      (k ≠ f → FrontW R a f (cohortEdge R s k)) := by
  obtain ⟨s1, s2, s3⟩ := frontStep R f k s h.1
  have hk := frontAlignKeep R a f k hR s h
  exact ⟨fun a b => ⟨s1 a b, hk⟩, fun a b => ⟨s2 a b, hk⟩, fun a => ⟨s3 a, hk⟩⟩

/-! ### The potential and the moment -/

/-- The front position is unique. Consumer: `fPotFront`. -/
theorem frontUnique (R f f' : Nat) (s : CohortLane) (h : FrontAt R f s) (h' : FrontAt R f' s) :
    f = f' := by
  rcases Nat.lt_trichotomy f f' with hlt | heq | hgt
  · exfalso
    have hx := (h.2.2 f h.1 h.2.1).2.1 rfl
    rcases (h'.2.2 f h.1 h.2.1).2.2.2 hlt with he | hp
    · rw [hx] at he; cases he
    · rw [hx] at hp; simp [isPI] at hp
  · exact heq
  · exfalso
    have hx := (h'.2.2 f' h'.1 h'.2.1).2.1 rfl
    rcases (h.2.2 f' h'.1 h'.2.1).2.2.2 hgt with he | hp
    · rw [hx] at he; cases he
    · rw [hx] at hp; simp [isPI] at hp

/-- A cleared window has no front. Consumer: `fPotDone`. -/
theorem doneNoFront (R : Nat) (s : CohortLane) (h : ADone R s) : ¬ ∃ f, FrontAt R f s := by
  rintro ⟨f, hf⟩
  have hx := (hf.2.2 f hf.1 hf.2.1).2.1 rfl
  rcases (h f hf.1 hf.2.1).2 with he | hp
  · rw [hx] at he; cases he
  · rw [hx] at hp; simp [isPI] at hp

/-- **The potential**: the cells from the front to the terminal, `0` without a front.
Consumer: `frontMoment`. -/
noncomputable def fPot (R : Nat) (s : CohortLane) : Nat :=
  if h : ∃ f, FrontAt R f s then 2 * R - Classical.choose h else 0

/-- Consumer: `frontLetter`, `frontMomentCoupled`. -/
theorem fPotFront (R f : Nat) (s : CohortLane) (h : FrontAt R f s) : fPot R s = 2 * R - f := by
  unfold fPot
  rw [dif_pos ⟨f, h⟩]
  have hc := Classical.choose_spec (⟨f, h⟩ : ∃ f, FrontAt R f s)
  rw [frontUnique R _ f s hc h]

/-- Consumer: `frontLetter`. -/
theorem fPotDone (R : Nat) (s : CohortLane) (h : ADone R s) : fPot R s = 0 := by
  unfold fPot
  rw [dif_neg (doneNoFront R s h)]

/-- The class of the phase. Consumer: `frontMoment`. -/
def FI (R a : Nat) (s : CohortLane) : Prop := ∃ f, FrontW R a f s

/-- One letter of the phase on the potential. Consumer: `frontMoment`. -/
theorem frontLetter (R a : Nat) (hR : 2 ≤ R) (s : CohortLane) (o : Option Nat) (h : FI R a s) :
    (DoneW R a (cohortLaneStep R s o) ∨ FI R a (cohortLaneStep R s o)) ∧
      fPot R (cohortLaneStep R s o) ≤ fPot R s := by
  obtain ⟨f, hf⟩ := h
  have hp := fPotFront R f s hf.1
  cases o with
  | none => exact ⟨Or.inr ⟨f, hf⟩, Nat.le_refl _⟩
  | some k =>
    show (DoneW R a (cohortEdge R s k) ∨ FI R a (cohortEdge R s k)) ∧
      fPot R (cohortEdge R s k) ≤ fPot R s
    obtain ⟨r1, r2, r3⟩ := frontWStep R a f k hR s hf
    by_cases hk : k = f
    · by_cases hf3 : f + 1 < 2 * R
      · have h' := r1 hk hf3
        rw [hp, fPotFront R _ _ h'.1]
        exact ⟨Or.inr ⟨_, h'⟩, by omega⟩
      · have h' := r2 hk (by have := hf.1.2.1; omega)
        rw [fPotDone R _ h'.1]
        exact ⟨Or.inl h', Nat.zero_le _⟩
    · have h' := r3 hk
      rw [hp, fPotFront R _ _ h'.1]
      exact ⟨Or.inr ⟨f, h'⟩, Nat.le_refl _⟩

/-- The nominated letter of the phase: the front's own edge. Consumer: `frontMoment`. -/
theorem frontDrop (R a : Nat) (hR : 2 ≤ R) (s : CohortLane) (h : FI R a s) :
    ∃ k, k < 2 * R ∧ fPot R (cohortEdge R s k) + 1 ≤ fPot R s := by
  obtain ⟨f, hf⟩ := h
  have hf2 := hf.1.2.1
  refine ⟨f, hf2, ?_⟩
  obtain ⟨r1, r2, _⟩ := frontWStep R a f f hR s hf
  rw [fPotFront R f s hf.1]
  by_cases hf3 : f + 1 < 2 * R
  · rw [fPotFront R _ _ (r1 rfl hf3).1]; omega
  · rw [fPotDone R _ (r2 rfl (by omega)).1]; omega

/-- The potential is at most `R`. Consumer: `frontMomentCoupled`. -/
theorem fPotLe (R : Nat) (s : CohortLane) : fPot R s ≤ R := by
  unfold fPot
  split
  · have h := Classical.choose_spec (‹∃ f, FrontAt R f s›)
    have := h.1
    omega
  · exact Nat.zero_le _

/-- **The front phase on the lane.** From a front with the aligned queue, the window is cleared
with the same queue with `E[z^T] ≤ w^{fPot}`. Consumer: `frontMomentCoupled`. -/
theorem frontMoment {n : Nat} (R a : Nat) (hR : 2 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (s : CohortLane) (hs : FI R a s) :
    MomentBoundQ (releaseNext R edgeOf) (DoneW R a) N (N ^ fPot R s) ((N - n) ^ fPot R s) s := by
  let P' : CohortLane → Prop := fun y => DoneW R a y ∨ ¬ FI R a y
  have hex : ∀ y, ∃ e : Fin n, ¬ P' y → fPot R (releaseNext R edgeOf y e) + 1 ≤ fPot R y := by
    intro y
    by_cases hy : P' y
    · exact ⟨site 0, fun h => absurd hy h⟩
    · have h2 : FI R a y := Classical.byContradiction fun h => hy (Or.inr h)
      obtain ⟨k, hk, hd⟩ := frontDrop R a hR y h2
      refine ⟨site k, fun _ => ?_⟩
      show fPot R (cohortLaneStep R y (edgeOf (site k))) + 1 ≤ _
      rw [hedge k hk]
      exact hd
  have hP' := momentOfPotential (releaseNext R edgeOf) P' N (fPot R)
    (fun y => Classical.choose (hex y)) hn hN
    (fun y hy => Classical.choose_spec (hex y) hy)
    (fun y hy e => by
      have h2 : FI R a y := Classical.byContradiction fun h => hy (Or.inr h)
      exact (frontLetter R a hR y (edgeOf e) h2).2) s
  exact momentSimQ (releaseNext R edgeOf) (releaseNext R edgeOf)
    (fun x y => x = y ∧ (DoneW R a x ∨ FI R a x)) (DoneW R a) P' N _ _
    (fun x y e hxy hna => by
      obtain ⟨rfl, hi⟩ := hxy
      rcases hi with hi | hi
      · exact absurd hi hna
      · exact ⟨rfl, (frontLetter R a hR x (edgeOf e) hi).1⟩)
    (fun x y hxy hg => by
      obtain ⟨rfl, hi⟩ := hxy
      rcases hg with hg | hg
      · exact hg
      · rcases hi with hi | hi
        · exact hi
        · exact absurd hi hg) s s ⟨rfl, Or.inr hs⟩ hP'

/-! ### The coupled chain -/

/-- **The front phase on the coupled chain.** From every layout state whose lane is a front with
the aligned queue at index `a`, the window is cleared with the same queue (no packet removed) with
`E[z^T] ≤ w^R`, `w = N/(N-n)`, uniformly over source registers and audit. Consumer:
`afterRaceGroupMoment`. -/
theorem frontMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R a : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : FI R a (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => DoneW R a (laneOfState ring hbank root lane src R y)) N
      (N ^ R) ((N - n) ^ R) x := by
  have hlane := frontMoment R a hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (laneOfState ring hbank root lane src R x) hs
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => DoneW R a (laneOfState ring hbank root lane src R y)) (DoneW R a) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (fPotLe R _)

/-! ### Entry from the race, and exit into the aligned trial -/

/-- **The outgoing edge wins on the lane**: at the misaligned outcome `VTAt R m`
(`1 ≤ m ≤ R - 2`, offset `h = R - 1 - m ≥ 1`) with the aligned queue and the window invariants,
the outgoing edge `f = 2R - 1 - m` turns the tail into a front at `f`; nothing else changes and the
queue index is kept. Consumer: `frontOfRaceCoupled`. -/
theorem frontOfRace (R a m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (s : CohortLane)
    (hV : VTAt R m s) (hA : AlignExt R a s) (hI : Inv R (winOf R s))
    (hB : Barrier R (winOf R s)) :
    FrontW R a (2 * R - 1 - m) (cohortEdge R s (2 * R - 1 - m)) := by
  obtain ⟨-, hc⟩ := hV
  have hk : R ≤ 2 * R - 1 - m := by omega
  have hk3 : 2 * R - 1 - m + 1 < 2 * R := by omega
  obtain ⟨⟨ik, lk⟩, ⟨ik1, lk1⟩, hoth⟩ := finCells R (2 * R - 1 - m) s hk hk3
  obtain ⟨hl0, hT0, -, -⟩ := hc (2 * R - 1 - m) hk (by omega)
  obtain ⟨hl1, -, hS1, -⟩ := hc (2 * R - 1 - m + 1) (by omega) hk3
  have hr : finOf R s (2 * R - 1 - m) = (.X, false, .S false, false) := by
    unfold finOf
    rw [hl0, hl1, hT0 rfl, hS1 (by omega), decide_eq_false (by omega : ¬ 2 * R - 1 - m = R)]
    exact finTS
  refine ⟨⟨hk, by omega, fun q h1 h2 => ?_⟩, ?_, winKeep R (by omega) s (some _) ⟨hI, hB⟩⟩
  · by_cases hq : q = 2 * R - 1 - m
    · rw [hq, ik, lk, hr]; exact frontCellX _ _ rfl
    by_cases hq1 : q = 2 * R - 1 - m + 1
    · rw [hq1, ik1, lk1, hr]; exact frontCellS _ _ (by omega)
    obtain ⟨a1, b1⟩ := hoth q (by omega)
    rw [a1, b1]
    obtain ⟨hlq, -, hSq, hEq⟩ := hc q h1 h2
    refine ⟨hlq, fun h => absurd h hq, fun h => hSq (by omega), fun h => hEq (by omega)⟩
  · rcases alignExtStep R a (by omega) s (2 * R - 1 - m) hA ⟨hI, hB⟩ with ⟨hA', _, _⟩ |
        ⟨B, _, _, _, _, _, hP, _, _⟩
    · exact hA'
    · rw [hT0 rfl] at hP; cases hP

/-- **The outgoing edge wins on the coupled chain**: from a layout state at the misaligned
outcome with the aligned queue at index `a` and the window invariants, the outgoing race edge
`raceOut` (`L3.DigitPacketRace.raceOut`, offset `R - 1 - m`) leads to a front with the same queue.
Consumer: `afterRaceGroupMoment`. -/
theorem frontOfRaceCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R a m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hV : VTAt R m (laneOfState ring hbank root lane src R x))
    (hA : AlignExt R a (laneOfState ring hbank root lane src R x))
    (hI : Inv R (winOf R (laneOfState ring hbank root lane src R x)))
    (hB : Barrier R (winOf R (laneOfState ring hbank root lane src R x))) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
          (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))).1 ∧
      FI R a (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
          (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)))) := by
  obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend x hx
    (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))
  refine ⟨h1, 2 * R - 1 - m, ?_⟩
  rw [h2]
  unfold L3.DigitPacketRace.raceOut
  rw [cohortEdgeOfSite ring root src R hend (R + (R - 1 - m)) (by omega),
    show R + (R - 1 - m) = 2 * R - 1 - m by omega]
  exact frontOfRace R a m hR hm1 hm2 _ hV hA hI hB

/-- **The cleared window at a group boundary is a trial state of index `R - 1`.** Consumer:
`afterRaceGroupMoment`. -/
theorem viAtOfCleared (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (h : DoneW R (R - 1) s) :
    VIAt R (R - 1) s := by
  obtain ⟨hd, hA, -, -⟩ := h
  refine ⟨R - 1, 0, by omega, hA, ⟨by omega, fun q h1 h2 => ?_⟩, ?_⟩
  · obtain ⟨hl, he⟩ := hd q h1 h2
    exact ⟨hl, fun h => absurd h (by omega), fun _ => he⟩
  · unfold vIdx; split <;> omega

/-- **The budget of the continuation to the aligned group**: `R` front services and the aligned
trial, `R + (R+2)(2R+2) = 2R² + 7R + 4`. Consumer: `afterRaceMoment`, `afterBudgetShort`. -/
def afterBudget (R : Nat) : Nat := R + (R + 2) * vK R

/-- **Lemma e-packet, the continuation after the outgoing race edge, to the aligned group.**
From a layout state at the misaligned outcome `VTAt R m` (`1 ≤ m ≤ R - 2`) with the queue at the
group boundary (`AlignExt R (R - 1)`) and the window invariants, after the outgoing race edge the
front erases the older suffix (`frontMomentCoupled`, `E ≤ w^R`), the cleared window is a trial
state of index `R - 1` (`viAtOfCleared`), and the trial ends in the aligned group
(`vMomentAtCoupled`, `E ≤ w^{(R+2)(2R+2)}`): `E[z^T] ≤ w^{R + (R+2)(2R+2)}`. Consumer:
`afterRaceMoment`. -/
theorem afterRaceGroupMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hV : VTAt R m (laneOfState ring hbank root lane src R x))
    (hA : AlignExt R (R - 1) (laneOfState ring hbank root lane src R x))
    (hI : Inv R (winOf R (laneOfState ring hbank root lane src R x)))
    (hB : Barrier R (winOf R (laneOfState ring hbank root lane src R x))) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => AGroup R (laneOfState ring hbank root lane src R y) ∧
        CohortLayout ring hbank root src R y.1) N
      (N ^ R * N ^ ((R + 2) * vK R)) ((N - n) ^ R * (N - n) ^ ((R + 2) * vK R))
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  let next := widthDigitAuditNext (bankWidthDigitReference ring hn hbank)
  let I : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => CohortLayout ring hbank root src R y.1
  have hIs : ∀ y e, I y → I (next y e) := fun y e h =>
    (laneStep ring hn hbank root lane src R (by omega) hsrc hend y h e).1
  obtain ⟨hl0, hfi⟩ := frontOfRaceCoupled ring hn hbank root lane src R (R - 1) m hR hsrc hend
    hm1 hm2 x hx hV hA hI hB
  have hF := momentKeep next _ I N _ _ hIs _ hl0
    (frontMomentCoupled ring hn hbank root lane src R (R - 1) (by omega) hsrc hend N hN _ hl0 hfi)
  refine momentSeq next _ _ N _ _ _ _ _
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_) hF
  obtain ⟨hd, hly⟩ := hy
  exact momentKeep next _ I N _ _ hIs y hly
    (vMomentAtCoupled ring hn hbank root lane src R hR hsrc hend N hN (R - 1) y hly
      (viAtOfCleared R (by omega) _ hd))

/-- **Lemma e-packet, the success continuation `F_a` of the race.** For any success target `P`
whose moment from every layout aligned-group state is at most `w^{B_s}` (the aligned completion
and its audit receipt), the continuation after the outgoing race edge from the misaligned outcome
(as in `afterRaceGroupMoment`) has `E[z^T] ≤ w^{R + (R+2)(2R+2) + B_s}`: the post-race bound
`F_a / D` of `L3.PacketMomentHorizon.attemptLoop` with budget
`B_a = afterBudget R + B_s = 2R² + 7R + 4 + B_s`. Consumer: `afterRaceDoneMoment`, and the
post-race branch of `L3.PacketMomentWide.attemptLoopWide`. -/
theorem afterRaceMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
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
    (hV : VTAt R m (laneOfState ring hbank root lane src R x))
    (hA : AlignExt R (R - 1) (laneOfState ring hbank root lane src R x))
    (hI : Inv R (winOf R (laneOfState ring hbank root lane src R x)))
    (hB : Barrier R (winOf R (laneOfState ring hbank root lane src R x))) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
      (N ^ (afterBudget R + Bs)) ((N - n) ^ (afterBudget R + Bs))
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  have h := momentSeq (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P _ N _ _ _ _ _
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => hP y hy.2 hy.1)
    (afterRaceGroupMoment ring hn hbank root lane src R m hR hsrc hend hm1 hm2 N hN x hx hV hA
      hI hB)
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add] at h
  exact h

/-- **The continuation to the finished group**: after the outgoing race edge, the aligned group
is finished (`ADone`, `L3.PacketMomentFinish.finishMomentCoupled`, `E ≤ w^{R+1}`) with
`E[z^T] ≤ w^{afterBudget R + (R + 1)} = w^{2R² + 8R + 5}`. Consumer: the post-race success
branch `B_a` of `L3.PacketMomentWide.attemptLoopWide` (followed by the audit receipt). -/
theorem afterRaceDoneMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hV : VTAt R m (laneOfState ring hbank root lane src R x))
    (hA : AlignExt R (R - 1) (laneOfState ring hbank root lane src R x))
    (hI : Inv R (winOf R (laneOfState ring hbank root lane src R x)))
    (hB : Barrier R (winOf R (laneOfState ring hbank root lane src R x))) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ADone R (laneOfState ring hbank root lane src R y) ∧
        CohortLayout ring hbank root src R y.1) N
      (N ^ (afterBudget R + (R + 1))) ((N - n) ^ (afterBudget R + (R + 1)))
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) :=
  afterRaceMoment ring hn hbank root lane src R m hR hsrc hend hm1 hm2 N hN _ (R + 1)
    (fun y hy hg => momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
      (fun y => CohortLayout ring hbank root src R y.1) N _ _
      (fun z e hz => (laneStep ring hn hbank root lane src R (by omega) hsrc hend z hz e).1) y hy
      (finishMomentCoupled ring hn hbank root lane src R (by omega) hsrc hend N hN y hy hg))
    x hx hV hA hI hB

/-- **The finished-group budget passes the post-race test of the wide loop**:
`11 (afterBudget R + (R + 1)) = 11 (2R² + 8R + 5) ≤ 2 C_R + 1` for `R ≥ 3`, the hypothesis
`11 B_a ≤ 2C + 1` of `L3.PacketMomentWide.shortPow` / `attemptLoopWide` at the BANK pair
(`R = r`). The room left for the audit receipt is `(2 C_R + 1) - 11 (2R² + 8R + 5) =
4R⁴ + 16R³ - 16R² - 66R - 46`. Consumer: `attemptLoopWide` at the BANK pair. -/
theorem afterBudgetShort (R : Nat) (hR : 3 ≤ R) :
    11 * (afterBudget R + (R + 1)) ≤ 2 * bankRepairDigitPairClock R + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, R = t + 3 := ⟨R - 3, by omega⟩
  unfold afterBudget vK bankRepairDigitPairClock
  grind

end L3.PacketMomentAfter

#print axioms L3.PacketMomentAfter.frontStep
#print axioms L3.PacketMomentAfter.frontAlignKeep
#print axioms L3.PacketMomentAfter.frontMoment
#print axioms L3.PacketMomentAfter.frontMomentCoupled
#print axioms L3.PacketMomentAfter.frontOfRace
#print axioms L3.PacketMomentAfter.frontOfRaceCoupled
#print axioms L3.PacketMomentAfter.viAtOfCleared
#print axioms L3.PacketMomentAfter.afterRaceGroupMoment
#print axioms L3.PacketMomentAfter.afterRaceMoment
#print axioms L3.PacketMomentAfter.afterRaceDoneMoment
#print axioms L3.PacketMomentAfter.afterBudgetShort
