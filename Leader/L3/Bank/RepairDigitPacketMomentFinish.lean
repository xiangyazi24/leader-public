import Leader.L3.Bank.RepairDigitPacketMomentPrep

/-!
# Lemma e-packet, the aligned completion on the lane

repair.tex, the renewal trial: "If `h = 0`, the next group settles in alignment" and the trial
ends "with a final aligned carry". At the aligned outcome of the trial
(`L3.PacketMomentVSerial.VTAt R (R - 1)`: the tail settled at the border cell `R`, the non-tails
of its group settled on `R + 1, …, 2R - 1`, no carry) the border launch and the carry's walk
through its own group are the only changes of the target window:

* `AGroup` (the aligned group) is left only by the launch on edge `R`, to `ARun R`;
* `ARun j` (fresh carry on cell `j`, its group's non-tails on `(j, 2R)`, only empty cells and
  moving packets behind it) is left only by the carry's own edge `j`: to `ARun (j + 1)`, or at
  `j = 2R - 1` through the terminal to `ADone` (carry-free, no settled input);
* no third edge changes the group: exports enter behind the carry and moving packets cannot
  settle on empty cells.

So `E[z^{T}] ≤ w^{R+1}` from the aligned outcome to the terminal (`finishMomentCoupled`); the
carry leaves through the terminal edge exactly at the first `ADone` (`termFires`). This is the
lane half of the success completion; the audit half (the terminal's fresh ledger with the `R`
uses of the group's exports, i.e. `DigitCompletion`) is not here.
-/

namespace L3.PacketMomentFinish

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
open L3.PacketMomentPending
open L3.PacketMomentV
open L3.PacketMomentVSerial

/-! ### The phases -/

/-- **The aligned group**: the trial's aligned outcome. Consumer: `finishMoment`. -/
def AGroup (R : Nat) (s : CohortLane) : Prop := VTAt R (R - 1) s

/-- **The carry of the aligned group on cell `j`.** Consumer: `finishMoment`. -/
def ARun (R j : Nat) (s : CohortLane) : Prop :=
  R ≤ j ∧ j < 2 * R ∧ ∀ q, R ≤ q → q < 2 * R →
    (q = j → s.live q = true ∧ s.inp q = .E) ∧ (q ≠ j → s.live q = false) ∧
    (q < j → s.inp q = .E ∨ isPI (s.inp q) = true) ∧ (j < q → s.inp q = .S false)

/-- **The group is consumed**: carry-free, only empty cells and moving packets. Consumer:
`finishMoment`, `termFires`. -/
def ADone (R : Nat) (s : CohortLane) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (s.inp q = .E ∨ isPI (s.inp q) = true)

/-- The class of the phase. Consumer: `finishMoment`. -/
def AI (R : Nat) (s : CohortLane) : Prop := AGroup R s ∨ ∃ j, ARun R j s

/-- **The potential**: `R + 1` on the group, `2R - j` with the carry on `j`, `0` when done.
Consumer: `finishMoment`. -/
noncomputable def aPot (R : Nat) (s : CohortLane) : Nat :=
  if ADone R s then 0 else if h : ∃ j, ARun R j s then 2 * R - Classical.choose h else R + 1

/-- The carry cell is unique. Consumer: `aPotRun`. -/
theorem runUnique (R j j' : Nat) (s : CohortLane) (h : ARun R j s) (h' : ARun R j' s) : j = j' := by
  apply Classical.byContradiction
  intro hne
  have := ((h'.2.2 j h.1 h.2.1).2.1 hne)
  rw [((h.2.2 j h.1 h.2.1).1 rfl).1] at this
  cases this

/-- A carry is not done. Consumer: `aPotRun`. -/
theorem runNotDone (R j : Nat) (s : CohortLane) (h : ARun R j s) : ¬ ADone R s := by
  intro hd
  have := (hd j h.1 h.2.1).1
  rw [((h.2.2 j h.1 h.2.1).1 rfl).1] at this
  cases this

/-- The group is not done. Consumer: `aPotGroup`. -/
theorem groupNotDone (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (h : AGroup R s) : ¬ ADone R s := by
  intro hd
  have h1 := (h.2 R (Nat.le_refl _) (by omega)).2.1 (by omega)
  rcases (hd R (Nat.le_refl _) (by omega)).2 with he | hp
  · rw [h1] at he; cases he
  · rw [h1] at hp; cases hp

/-- The group has no carry. Consumer: `aPotGroup`. -/
theorem groupNotRun (R : Nat) (s : CohortLane) (h : AGroup R s) : ¬ ∃ j, ARun R j s := by
  rintro ⟨j, hj⟩
  have := (h.2 j hj.1 hj.2.1).1
  rw [((hj.2.2 j hj.1 hj.2.1).1 rfl).1] at this
  cases this

/-- Consumer: `finishMoment`. -/
theorem aPotRun (R j : Nat) (s : CohortLane) (h : ARun R j s) : aPot R s = 2 * R - j := by
  unfold aPot
  rw [if_neg (runNotDone R j s h), dif_pos ⟨j, h⟩]
  have := Classical.choose_spec (⟨j, h⟩ : ∃ j, ARun R j s)
  rw [runUnique R _ j s this h]

/-- Consumer: `finishMoment`. -/
theorem aPotGroup (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (h : AGroup R s) : aPot R s = R + 1 := by
  unfold aPot
  rw [if_neg (groupNotDone R hR s h), dif_neg (groupNotRun R s h)]

/-- Consumer: `finishMoment`. -/
theorem aPotDone (R : Nat) (s : CohortLane) (h : ADone R s) : aPot R s = 0 := by
  unfold aPot; rw [if_pos h]

/-! ### Edge forms on the cells -/

/-- A source edge leaves the window. Consumer: `groupStep`, `runStep`. -/
theorem cellsSrc (R k : Nat) (s : CohortLane) (h : k + 1 < R) :
    (cohortEdge R s k).inp = s.inp ∧ (cohortEdge R s k).live = s.live := by
  unfold cohortEdge; rw [if_pos h]; exact ⟨rfl, rfl⟩

/-- The port edge on the border cell. Consumer: `groupStep`, `runStep`. -/
theorem cellsPort (R k : Nat) (s : CohortLane) (h1 : ¬ k + 1 < R) (h : k + 1 = R) :
    (∀ q, q ≠ R → (cohortEdge R s k).inp q = s.inp q ∧ (cohortEdge R s k).live q = s.live q) ∧
      (s.live R = true → (cohortEdge R s k).inp R = .E ∧ (cohortEdge R s k).live R = true) ∧
      (s.live R = false → (cohortEdge R s k).live R = false ∧
        ((cohortEdge R s k).inp R = s.inp R ∨
          (s.inp R = .E ∧ ∃ T, (cohortEdge R s k).inp R = .P T))) := by
  have hf : cohortEdge R s k =
      { out := cohortUpd s.out k (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1,
        inp := cohortUpd s.inp (k + 1)
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1,
        live := cohortUpd s.live (k + 1)
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.2 } := by
    unfold cohortEdge; rw [if_neg h1, if_pos h]
  rw [hf]
  subst h
  refine ⟨fun q hq => by simp [cohortUpd, hq], fun hl => ?_, fun hl => ?_⟩
  · simp only [cohortUpd, if_true]
    rw [hl]
    cases s.out k with
    | D T => simp [bankRepairDigitDelStep]
    | U => simp [bankRepairDigitDelStep]
    | E => simp [bankRepairDigitDelStep]
  · simp only [cohortUpd, if_true]
    rw [hl]
    cases ho : s.out k with
    | D T =>
      cases hi : s.inp (k + 1) with
      | E => exact ⟨by simp [bankRepairDigitDelStep], Or.inr ⟨rfl, T, by simp [bankRepairDigitDelStep]⟩⟩
      | X => exact ⟨by simp [bankRepairDigitDelStep], Or.inl (by simp [bankRepairDigitDelStep])⟩
      | P B => exact ⟨by simp [bankRepairDigitDelStep], Or.inl (by simp [bankRepairDigitDelStep])⟩
      | S B => exact ⟨by simp [bankRepairDigitDelStep], Or.inl (by simp [bankRepairDigitDelStep])⟩
    | U => exact ⟨by simp [bankRepairDigitDelStep], Or.inl (by simp [bankRepairDigitDelStep])⟩
    | E => exact ⟨by simp [bankRepairDigitDelStep], Or.inl (by simp [bankRepairDigitDelStep])⟩

/-- An internal edge on its two cells. Consumer: `groupStep`, `runStep`. -/
theorem cellsInner (R k : Nat) (s : CohortLane) (hk : R ≤ k) (h3 : k + 1 < 2 * R) :
    (∀ q, q ≠ k → q ≠ k + 1 →
      (cohortEdge R s k).inp q = s.inp q ∧ (cohortEdge R s k).live q = s.live q) ∧
    ((cohortEdge R s k).inp k, (cohortEdge R s k).live k, (cohortEdge R s k).inp (k + 1),
        (cohortEdge R s k).live (k + 1)) =
      bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
        (s.live (k + 1)) := by
  rw [edgeInner R s k hk h3]
  refine ⟨fun q hq hq' => by simp [cohortUpd, hq, hq'], ?_⟩
  simp [cohortUpd]

/-- The terminal edge on its cell. Consumer: `groupStep`, `runStep`. -/
theorem cellsTerm (R k : Nat) (hR : 1 ≤ R) (s : CohortLane) (h4 : k + 1 = 2 * R) :
    (∀ q, q ≠ k → (cohortEdge R s k).inp q = s.inp q ∧ (cohortEdge R s k).live q = s.live q) ∧
    ((cohortEdge R s k).inp k, (cohortEdge R s k).live k) = cohortTermStep (s.inp k) (s.live k) := by
  rw [edgeTerm R s k h4 hR]
  refine ⟨fun q hq => by simp [cohortUpd, hq], ?_⟩
  simp [cohortUpd]

/-! ### The steps -/

/-- **The group is left only by the launch.** Consumer: `aStep`. -/
theorem groupStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : AGroup R s) :
    (k = R → ARun R R (cohortEdge R s k)) ∧ (k ≠ R → AGroup R (cohortEdge R s k)) := by
  obtain ⟨_, hc⟩ := h
  have hR1 : 2 * R - 1 - (R - 1) = R := by omega
  have hR2 : 2 * R - (R - 1) = R + 1 := by omega
  have cR := hc R (Nat.le_refl _) (by omega)
  rw [hR1, hR2] at cR
  have hc' : ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (q = R → s.inp q = .S true) ∧
      (R + 1 ≤ q → s.inp q = .S false) := by
    intro q h1 h2
    have := hc q h1 h2
    rw [hR1, hR2] at this
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have keep : ∀ s' : CohortLane, (∀ q, R ≤ q → q < 2 * R → s'.inp q = s.inp q ∧
      s'.live q = s.live q) → AGroup R s' := by
    intro s' hs'
    refine ⟨by omega, fun q h1 h2 => ?_⟩
    rw [(hs' q h1 h2).1, (hs' q h1 h2).2]
    exact hc q h1 h2
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk
    obtain ⟨hoth, hf⟩ := cellsInner k k s (Nat.le_refl _) (by omega)
    have h0 := hc' k (Nat.le_refl _) (by omega)
    have h1 := hc' (k + 1) (by omega) (by omega)
    rw [h0.1, h1.1, h0.2.1 rfl, h1.2.2 (Nat.le_refl _)] at hf
    simp [bankRepairDigitFinStep] at hf
    obtain ⟨f1, f2, f3, f4⟩ := hf
    refine ⟨Nat.le_refl _, by omega, fun q h1' h2' => ?_⟩
    by_cases hq : q = k
    · subst hq
      exact ⟨fun _ => ⟨f2, f1⟩, fun h => absurd rfl h, fun h => absurd h (by omega),
        fun h => absurd h (by omega)⟩
    · by_cases hq1 : q = k + 1
      · subst hq1
        exact ⟨fun h => absurd h (by omega), fun _ => f4, fun h => absurd h (by omega),
          fun _ => f3⟩
      · rw [(hoth q hq hq1).1, (hoth q hq hq1).2]
        have := hc' q h1' h2'
        exact ⟨fun h => absurd h hq, fun _ => this.1, fun h => absurd h (by omega),
          fun _ => this.2.2 (by omega)⟩
  · by_cases h1 : k + 1 < R
    · obtain ⟨hi, hl⟩ := cellsSrc R k s h1
      exact keep _ fun q _ _ => ⟨by rw [hi], by rw [hl]⟩
    by_cases h2 : k + 1 = R
    · obtain ⟨hoth, _, hfree⟩ := cellsPort R k s h1 h2
      obtain ⟨hl', hi'⟩ := hfree (hc' R (Nat.le_refl _) (by omega)).1
      refine keep _ fun q h1' h2' => ?_
      by_cases hq : q = R
      · subst hq
        rcases hi' with hi' | ⟨hE, _⟩
        · exact ⟨hi', by rw [hl', (hc' q h1' h2').1]⟩
        · rw [(hc' q h1' h2').2.1 rfl] at hE; cases hE
      · exact hoth q hq
    by_cases h3 : k + 1 < 2 * R
    · obtain ⟨hoth, hf⟩ := cellsInner R k s (by omega) h3
      have h0 := hc' k (by omega) (by omega)
      have h1' := hc' (k + 1) (by omega) h3
      have hkR : decide (k = R) = false := by simp; omega
      rw [hkR, h0.1, h1'.1, h0.2.2 (by omega), h1'.2.2 (by omega)] at hf
      simp [bankRepairDigitFinStep] at hf
      obtain ⟨f1, f2, f3, f4⟩ := hf
      refine keep _ fun q _ _ => ?_
      by_cases hq : q = k
      · subst hq; exact ⟨by rw [f1, h0.2.2 (by omega)], by rw [f2, h0.1]⟩
      · by_cases hq1 : q = k + 1
        · subst hq1; exact ⟨by rw [f3, h1'.2.2 (by omega)], by rw [f4, h1'.1]⟩
        · exact hoth q hq hq1
    by_cases h4 : k + 1 = 2 * R
    · obtain ⟨hoth, hf⟩ := cellsTerm R k (by omega) s h4
      have h0 := hc' k (by omega) (by omega)
      rw [h0.1, h0.2.2 (by omega)] at hf
      simp [cohortTermStep] at hf
      obtain ⟨f1, f2⟩ := hf
      refine keep _ fun q _ _ => ?_
      by_cases hq : q = k
      · subst hq; exact ⟨by rw [f1, h0.2.2 (by omega)], by rw [f2, h0.1]⟩
      · exact hoth q hq
    · rw [edgeFar R s k (by omega)]
      exact keep s fun _ _ _ => ⟨rfl, rfl⟩

/-- **The carry is moved only by its own edge.** Consumer: `aStep`. -/
theorem runStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (j k : Nat) (h : ARun R j s) :
    (k = j → j + 1 < 2 * R → ARun R (j + 1) (cohortEdge R s k)) ∧
      (k = j → j + 1 = 2 * R → ADone R (cohortEdge R s k)) ∧
      (k ≠ j → ARun R j (cohortEdge R s k)) := by
  obtain ⟨hj1, hj2, hc⟩ := h
  have keep : ∀ s' : CohortLane, (∀ q, R ≤ q → q < 2 * R → q ≠ j →
      s'.live q = false ∧ (q < j → s'.inp q = .E ∨ isPI (s'.inp q) = true) ∧
        (j < q → s'.inp q = .S false)) → s'.live j = true → s'.inp j = .E → ARun R j s' := by
    intro s' hs' hl hi
    refine ⟨hj1, hj2, fun q h1 h2 => ?_⟩
    by_cases hq : q = j
    · subst hq
      exact ⟨fun _ => ⟨hl, hi⟩, fun h => absurd rfl h, fun h => absurd h (by omega),
        fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h hq, fun _ => (hs' q h1 h2 hq).1, (hs' q h1 h2 hq).2.1,
        (hs' q h1 h2 hq).2.2⟩
  have same : ∀ s' : CohortLane, (∀ q, R ≤ q → q < 2 * R → s'.inp q = s.inp q ∧
      s'.live q = s.live q) → ARun R j s' := by
    intro s' hs'
    refine keep s' (fun q h1 h2 hq => ?_) ?_ ?_
    · rw [(hs' q h1 h2).1, (hs' q h1 h2).2]
      have := hc q h1 h2
      exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
    · rw [(hs' j hj1 hj2).2]; exact ((hc j hj1 hj2).1 rfl).1
    · rw [(hs' j hj1 hj2).1]; exact ((hc j hj1 hj2).1 rfl).2
  have cj := (hc j hj1 hj2).1 rfl
  refine ⟨fun hk hj => ?_, fun hk hj => ?_, fun hk => ?_⟩
  · subst hk
    obtain ⟨hoth, hf⟩ := cellsInner R k s hj1 hj
    have c1 := hc (k + 1) (by omega) hj
    rw [cj.1, cj.2, (c1.2.1 (by omega)), c1.2.2.2 (by omega)] at hf
    simp [bankRepairDigitFinStep] at hf
    obtain ⟨f1, f2, f3, f4⟩ := hf
    refine ⟨by omega, hj, fun q h1 h2 => ?_⟩
    by_cases hq : q = k
    · subst hq
      exact ⟨fun h => absurd h (by omega), fun _ => f2, fun _ => Or.inl f1,
        fun h => absurd h (by omega)⟩
    · by_cases hq1 : q = k + 1
      · subst hq1
        exact ⟨fun _ => ⟨f4, f3⟩, fun h => absurd rfl h, fun h => absurd h (by omega),
          fun h => absurd h (by omega)⟩
      · rw [(hoth q hq hq1).1, (hoth q hq hq1).2]
        have := hc q h1 h2
        exact ⟨fun h => absurd h hq1, fun _ => this.2.1 hq, fun h => this.2.2.1 (by omega),
          fun h => this.2.2.2 (by omega)⟩
  · subst hk
    obtain ⟨hoth, hf⟩ := cellsTerm R k (by omega) s hj
    rw [cj.1, cj.2] at hf
    simp [cohortTermStep] at hf
    obtain ⟨f1, f2⟩ := hf
    intro q h1 h2
    by_cases hq : q = k
    · subst hq; exact ⟨f2, Or.inl f1⟩
    · rw [(hoth q hq).1, (hoth q hq).2]
      have := hc q h1 h2
      exact ⟨this.2.1 hq, this.2.2.1 (by omega)⟩
  · by_cases h1 : k + 1 < R
    · obtain ⟨hi, hl⟩ := cellsSrc R k s h1
      exact same _ fun q _ _ => ⟨by rw [hi], by rw [hl]⟩
    by_cases h2 : k + 1 = R
    · obtain ⟨hoth, hlive, hfree⟩ := cellsPort R k s h1 h2
      by_cases hjR : j = R
      · subst hjR
        obtain ⟨hi', hl'⟩ := hlive cj.1
        refine same _ fun q h1' h2' => ?_
        by_cases hq : q = j
        · subst hq; exact ⟨by rw [hi', cj.2], by rw [hl', cj.1]⟩
        · exact hoth q hq
      · have cR := hc R (Nat.le_refl _) (by omega)
        obtain ⟨hl', hi'⟩ := hfree (cR.2.1 (by omega))
        refine keep _ (fun q h1' h2' hq => ?_) ?_ ?_
        · by_cases hqR : q = R
          · subst hqR
            refine ⟨hl', fun _ => ?_, fun h => absurd h (by omega)⟩
            rcases hi' with hi' | ⟨_, T, hT⟩
            · rw [hi']; exact cR.2.2.1 (by omega)
            · rw [hT]; exact Or.inr rfl
          · rw [(hoth q hqR).1, (hoth q hqR).2]
            have := hc q h1' h2'
            exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
        · rw [(hoth j (by omega)).2]; exact cj.1
        · rw [(hoth j (by omega)).1]; exact cj.2
    by_cases h3 : k + 1 < 2 * R
    · obtain ⟨hoth, hf⟩ := cellsInner R k s (by omega) h3
      have ck := hc k (by omega) (by omega)
      have ck1 := hc (k + 1) (by omega) h3
      by_cases hlo : k + 1 = j
      · -- the cell behind the carry
        subst hlo
        rw [ck.2.1 (by omega), cj.1, cj.2] at hf
        rcases ck.2.2.1 (by omega) with hE | hP
        · rw [hE] at hf
          simp [bankRepairDigitFinStep] at hf
          obtain ⟨f1, f2, f3, f4⟩ := hf
          refine keep _ (fun q h1' h2' hq => ?_) ?_ ?_
          · by_cases hqk : q = k
            · subst hqk; exact ⟨f2, fun _ => Or.inl f1, fun h => absurd h (by omega)⟩
            · rw [(hoth q hqk (by omega)).1, (hoth q hqk (by omega)).2]
              have := hc q h1' h2'
              exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
          · exact f4
          · exact f3
        · obtain ⟨T, hT⟩ : ∃ T, s.inp k = .P T := by
            revert hP; cases s.inp k with
            | P T => intro _; exact ⟨T, rfl⟩
            | _ => intro h; cases h
          rw [hT] at hf
          simp [bankRepairDigitFinStep] at hf
          obtain ⟨f1, f2, f3, f4⟩ := hf
          refine keep _ (fun q h1' h2' hq => ?_) ?_ ?_
          · by_cases hqk : q = k
            · subst hqk; exact ⟨f2, fun _ => Or.inr (by rw [f1]; rfl), fun h => absurd h (by omega)⟩
            · rw [(hoth q hqk (by omega)).1, (hoth q hqk (by omega)).2]
              have := hc q h1' h2'
              exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
          · exact f4
          · exact f3
      by_cases hbelow : k + 1 < j
      · -- behind the carry: empty cells and moving packets
        rw [ck.2.1 (by omega), ck1.2.1 (by omega)] at hf
        have hk' : ∀ (x y : BankRepairDigitInSh), (x = .E ∨ isPI x = true) →
            (y = .E ∨ isPI y = true) →
            ((bankRepairDigitFinStep (decide (k = R)) x false y false).1 = .E ∨
              isPI (bankRepairDigitFinStep (decide (k = R)) x false y false).1 = true) ∧
            (bankRepairDigitFinStep (decide (k = R)) x false y false).2.1 = false ∧
            ((bankRepairDigitFinStep (decide (k = R)) x false y false).2.2.1 = .E ∨
              isPI (bankRepairDigitFinStep (decide (k = R)) x false y false).2.2.1 = true) ∧
            (bankRepairDigitFinStep (decide (k = R)) x false y false).2.2.2 = false := by
          intro x y hx hy
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · subst hx hy; simp [bankRepairDigitFinStep]
          · subst hx
            revert hy; cases y with
            | P T => intro _; simp [bankRepairDigitFinStep, isPI]
            | _ => intro h; cases h
          · subst hy
            revert hx; cases x with
            | P T => intro _; simp [bankRepairDigitFinStep, isPI]
            | _ => intro h; cases h
          · revert hx hy; cases x with
            | P T => cases y with
              | P T' => intro _ _; simp [bankRepairDigitFinStep, isPI]
              | _ => intro _ h; cases h
            | _ => intro h; cases h
        have hcl := hk' (s.inp k) (s.inp (k + 1)) (ck.2.2.1 (by omega)) (ck1.2.2.1 (by omega))
        rw [← hf] at hcl
        obtain ⟨g1, g2, g3, g4⟩ := hcl
        refine keep _ (fun q h1' h2' hq => ?_) ?_ ?_
        · by_cases hqk : q = k
          · subst hqk; exact ⟨g2, fun _ => g1, fun h => absurd h (by omega)⟩
          · by_cases hqk1 : q = k + 1
            · subst hqk1; exact ⟨g4, fun _ => g3, fun h => absurd h (by omega)⟩
            · rw [(hoth q hqk hqk1).1, (hoth q hqk hqk1).2]
              have := hc q h1' h2'
              exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
        · rw [(hoth j (by omega) (by omega)).2]; exact cj.1
        · rw [(hoth j (by omega) (by omega)).1]; exact cj.2
      · -- ahead of the carry: the group's non-tails
        have hkj : j < k := by omega
        have hkR : decide (k = R) = false := by simp; omega
        rw [hkR, ck.2.1 (by omega), ck1.2.1 (by omega), ck.2.2.2 hkj,
          ck1.2.2.2 (by omega)] at hf
        simp [bankRepairDigitFinStep] at hf
        obtain ⟨f1, f2, f3, f4⟩ := hf
        refine keep _ (fun q h1' h2' hq => ?_) ?_ ?_
        · by_cases hqk : q = k
          · subst hqk; exact ⟨f2, fun h => absurd h (by omega), fun _ => f1⟩
          · by_cases hqk1 : q = k + 1
            · subst hqk1; exact ⟨f4, fun h => absurd h (by omega), fun _ => f3⟩
            · rw [(hoth q hqk hqk1).1, (hoth q hqk hqk1).2]
              have := hc q h1' h2'
              exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
        · rw [(hoth j (by omega) (by omega)).2]; exact cj.1
        · rw [(hoth j (by omega) (by omega)).1]; exact cj.2
    by_cases h4 : k + 1 = 2 * R
    · obtain ⟨hoth, hf⟩ := cellsTerm R k (by omega) s h4
      have ck := hc k (by omega) (by omega)
      rw [ck.2.1 hk, ck.2.2.2 (by omega)] at hf
      simp [cohortTermStep] at hf
      obtain ⟨f1, f2⟩ := hf
      refine keep _ (fun q h1' h2' hq => ?_) ?_ ?_
      · by_cases hqk : q = k
        · subst hqk; exact ⟨f2, fun h => absurd h (by omega), fun _ => f1⟩
        · rw [(hoth q hqk).1, (hoth q hqk).2]
          have := hc q h1' h2'
          exact ⟨this.2.1 hq, this.2.2.1, this.2.2.2⟩
      · rw [(hoth j (by omega)).2]; exact cj.1
      · rw [(hoth j (by omega)).1]; exact cj.2
    · rw [edgeFar R s k (by omega)]
      exact same s fun _ _ _ => ⟨rfl, rfl⟩

/-! ### The moment -/

/-- One letter of the phase on the potential. Consumer: `finishMoment`. -/
theorem aStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (o : Option Nat) (h : AI R s) :
    (ADone R (cohortLaneStep R s o) ∨ AI R (cohortLaneStep R s o)) ∧
      aPot R (cohortLaneStep R s o) ≤ aPot R s := by
  cases o with
  | none => exact ⟨Or.inr h, Nat.le_refl _⟩
  | some k =>
    show (ADone R (cohortEdge R s k) ∨ AI R (cohortEdge R s k)) ∧
      aPot R (cohortEdge R s k) ≤ aPot R s
    rcases h with hg | ⟨j, hj⟩
    · have hp := aPotGroup R (by omega) s hg
      by_cases hk : k = R
      · have h' := (groupStep R hR s k hg).1 hk
        rw [hp, aPotRun R R _ h']
        exact ⟨Or.inr (Or.inr ⟨R, h'⟩), by omega⟩
      · have h' := (groupStep R hR s k hg).2 hk
        rw [hp, aPotGroup R (by omega) _ h']
        exact ⟨Or.inr (Or.inl h'), Nat.le_refl _⟩
    · have hp := aPotRun R j s hj
      obtain ⟨r1, r2, r3⟩ := runStep R hR s j k hj
      by_cases hk : k = j
      · by_cases hj2 : j + 1 < 2 * R
        · have h' := r1 hk hj2
          rw [hp, aPotRun R _ _ h']
          exact ⟨Or.inr (Or.inr ⟨_, h'⟩), by omega⟩
        · have h' := r2 hk (by have := hj.2.1; omega)
          rw [aPotDone R _ h']
          exact ⟨Or.inl h', Nat.zero_le _⟩
      · have h' := r3 hk
        rw [hp, aPotRun R j _ h']
        exact ⟨Or.inr (Or.inr ⟨j, h'⟩), Nat.le_refl _⟩

/-- The nominated letter of the phase. Consumer: `finishMoment`. -/
theorem aDrop (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (h : AI R s) :
    ∃ k, k < 2 * R ∧ aPot R (cohortEdge R s k) + 1 ≤ aPot R s := by
  rcases h with hg | ⟨j, hj⟩
  · refine ⟨R, by omega, ?_⟩
    rw [aPotGroup R (by omega) s hg, aPotRun R R _ ((groupStep R hR s R hg).1 rfl)]
    omega
  · refine ⟨j, hj.2.1, ?_⟩
    obtain ⟨r1, r2, _⟩ := runStep R hR s j j hj
    rw [aPotRun R j s hj]
    by_cases hj2 : j + 1 < 2 * R
    · rw [aPotRun R _ _ (r1 rfl hj2)]; have := hj.1; omega
    · rw [aPotDone R _ (r2 rfl (by have := hj.2.1; omega))]; have := hj.2.1; omega

/-- The potential is at most `R + 1`. Consumer: `finishMomentCoupled`. -/
theorem aPotLe (R : Nat) (s : CohortLane) : aPot R s ≤ R + 1 := by
  unfold aPot
  split
  · exact Nat.zero_le _
  · split
    · have h := Classical.choose_spec (‹∃ j, ARun R j s›)
      have := h.1
      omega
    · exact Nat.le_refl _

/-- **The aligned completion on the lane.** From the aligned group or its carry, the group is
consumed with `E[z^T] ≤ w^{aPot}`. Consumer: `finishMomentCoupled`. -/
theorem finishMoment {n : Nat} (R : Nat) (hR : 2 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (s : CohortLane) (hs : AI R s) :
    MomentBoundQ (releaseNext R edgeOf) (ADone R) N (N ^ aPot R s) ((N - n) ^ aPot R s) s := by
  let P' : CohortLane → Prop := fun y => ADone R y ∨ ¬ AI R y
  have hex : ∀ y, ∃ e : Fin n, ¬ P' y → aPot R (releaseNext R edgeOf y e) + 1 ≤ aPot R y := by
    intro y
    by_cases hy : P' y
    · exact ⟨site 0, fun h => absurd hy h⟩
    · have h2 : AI R y := Classical.byContradiction fun h => hy (Or.inr h)
      obtain ⟨k, hk, hd⟩ := aDrop R hR y h2
      refine ⟨site k, fun _ => ?_⟩
      show aPot R (cohortLaneStep R y (edgeOf (site k))) + 1 ≤ _
      rw [hedge k hk]
      exact hd
  have hP' := momentOfPotential (releaseNext R edgeOf) P' N (aPot R)
    (fun y => Classical.choose (hex y)) hn hN
    (fun y hy => Classical.choose_spec (hex y) hy)
    (fun y hy e => by
      have h2 : AI R y := Classical.byContradiction fun h => hy (Or.inr h)
      exact (aStep R hR y (edgeOf e) h2).2) s
  exact momentSimQ (releaseNext R edgeOf) (releaseNext R edgeOf)
    (fun a b => a = b ∧ (ADone R a ∨ AI R a)) (ADone R) P' N _ _
    (fun a b e hab hna => by
      obtain ⟨rfl, hi⟩ := hab
      rcases hi with hi | hi
      · exact absurd hi hna
      · exact ⟨rfl, (aStep R hR a (edgeOf e) hi).1⟩)
    (fun a b hab hg => by
      obtain ⟨rfl, hi⟩ := hab
      rcases hg with hg | hg
      · exact hg
      · rcases hi with hi | hi
        · exact hi
        · exact absurd hi hg) s s ⟨rfl, Or.inr hs⟩ hP'

/-- **The aligned completion on the coupled chain.** From every layout state whose lane is the
aligned outcome of the renewal trial (`VTAt R (R - 1)`, e.g. from `vMomentAtCoupled` at index
`R - 1`), the border launch and the carry's walk consume the group with `E[z^T] ≤ w^{R+1}`,
`w = N/(N-n)`, uniformly over source registers and audit. Consumer: the per-pair moment (the
success completion after the aligned trial and after a won race). -/
theorem finishMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : AGroup R (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ADone R (laneOfState ring hbank root lane src R y)) N
      (N ^ (R + 1)) ((N - n) ^ (R + 1)) x := by
  have hlane := finishMoment R hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (laneOfState ring hbank root lane src R x) (Or.inl hs)
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => ADone R (laneOfState ring hbank root lane src R y)) (ADone R) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (aPotLe R _)

/-- **The group leaves through the terminal**: a letter from the phase into `ADone` is the
terminal edge with the carry on the last cell, which the terminal row clears. Consumer: the audit
half of the success completion (the terminal receipt of the group's carry). -/
theorem termFires (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : AI R s)
    (hd : ADone R (cohortEdge R s k)) :
    k + 1 = 2 * R ∧ ARun R k s := by
  rcases h with hg | ⟨j, hj⟩
  · by_cases hk : k = R
    · exact absurd hd (runNotDone R R _ ((groupStep R hR s k hg).1 hk))
    · exact absurd hd (groupNotDone R (by omega) _ ((groupStep R hR s k hg).2 hk))
  · obtain ⟨r1, _, r3⟩ := runStep R hR s j k hj
    by_cases hk : k = j
    · by_cases hj2 : j + 1 < 2 * R
      · exact absurd hd (runNotDone R _ _ (r1 hk hj2))
      · subst hk; exact ⟨by have := hj.2.1; omega, hj⟩
    · exact absurd hd (runNotDone R j _ (r3 hk))

end L3.PacketMomentFinish

#print axioms L3.PacketMomentFinish.groupStep
#print axioms L3.PacketMomentFinish.runStep
#print axioms L3.PacketMomentFinish.finishMoment
#print axioms L3.PacketMomentFinish.finishMomentCoupled
#print axioms L3.PacketMomentFinish.termFires
