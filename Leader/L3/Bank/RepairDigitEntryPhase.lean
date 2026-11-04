import Leader.L3.Bank.RepairDigitRearm

/-!
# R10c group 6: the lane phase of the strict cohort, from its tail sample to the cycle class

One interior complete pair and one lane, as in `BankRepairDigitRearm`. This module is the
lane-level half of group 6 of the BANK digit entry (`StructuralCut → EntryCut 0`): it follows
the cohort of a strict completion physically, from the moment its tail is sampled at the
source border to its terminal, and shows that from then on the lane is in the settled cycle
class `CohortCyc` (the `Rearm.CohortCycIn` class with any cycle counter).

The strict cohort is tracked by one cell `p` (`strictTrack`):

* **source phase** (`p < R`, `TailSweep`): the tail packet (`D true`) sits at source cell `p`,
  and every cell behind it is a younger slot (`CohortYounger R s p`). This is closed under
  every letter with no hypothesis (`tailSweepEdge`): the tail stays, hops one cell (leaving the
  unread slot behind it), or is exported by the delimiter row into target cell `R`.
* **target phase** (`R ≤ p < 2R`, `StrictLane`): `p` is the bottom of the strict cohort's
  region: target cell `R` while the tail operand waits there (any non-empty shape), afterwards
  the live carry. Below `p` the chosen (next) cohort is in the generated class
  (`CohortChosen R s lam p`, T24) with the younger slots behind its tail. On export the class
  starts with `lam = 0` (`strictLaneOfExport`). Under a letter (`strictLaneEdge`) the bottom
  either stays non-empty, or empties and moves up by one; the only hypothesis is that an
  emptied bottom is followed by the live carry or by the end of the pair (`hgo`). This is the
  one fact the audit history supplies (the strict carry is not lost before its terminal, and
  the tail operand is consumed where it settled); it is not true for an arbitrary lane.
* **after the terminal** (`p = 2R`): `strictLaneTop` gives `CohortCyc` (old phase `2R + 1`),
  and `cycClassStep` / `cycClassRun` carry it along every later letter (the `Rearm` closure).

`strictTraceRun` is the run statement: along any lane trace from a state where the tail
was just sampled (`tailSampleStart`), the tracked phase holds at every time, provided the
target-phase hypothesis holds at every letter; `strictPhaseCyc` reads off the cycle class once
the track has reached `2R`.

Consumer: the group 6 bridge (step 4 of the R10c worker notes, 2026-11-01 group 6 Lean plan)
from the recorded `DigitFirstStrictCompletion` of a complete pair to `CohortCycIn` on the
current lane at the structural cut, which feeds `BlockEntry.PairPin` / `EntryCut 0`.
-/

namespace L3.DigitEntryPhase

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! ### The cycle class with any counter -/

/-- The settled cycle class of `Rearm` without its counters: some old phase, the chosen cohort
in the generated class with its ghost, the younger slots behind its tail, the chosen grid not
complete. -/
def CohortCyc (R : Nat) (s : CohortLane) : Prop :=
  ∃ lam o, CohortGen R s lam o ∧ CohortYounger R s (lam (R - 1)) ∧ ¬ gridDone R R lam

section Cyc

variable {R : Nat}

/-- `CohortCyc` is `CohortCycIn` at some counter. Consumer: the group 6 bridge, which hands
`CohortCycIn R j s g o` to `BlockEntry.PairPin`. -/
theorem cycClassIn {s : CohortLane} (h : CohortCyc R s) (j : Nat) :
    ∃ g o, CohortCycIn R j s g o := by
  obtain ⟨lam, o, hg, hY, hnd⟩ := h
  exact ⟨(lam, j), o, rfl, hg, hY, hnd⟩

/-- Step 3 of group 6: the cycle class is closed under every lane letter (the `Rearm` closure,
with the hand-over to the next cohort when the chosen grid completes). Consumer:
`cycClassRun`, `strictPhaseStep`. -/
theorem cycClassStep {s : CohortLane} (h : CohortCyc R s) (ke : Option Nat) :
    CohortCyc R (cohortLaneStep R s ke) := by
  obtain ⟨lam, o, hg, hY, hnd⟩ := h
  obtain ⟨o', -, hg', hY', -⟩ := cohortGenStepClosed hg hY hnd ke
  by_cases hd : gridDone R R (cohortGenStep R s lam ke)
  · obtain ⟨a, b, c⟩ := cohortGenDoneStart hg' hY' hd
    exact ⟨_, 0, a, b, c⟩
  · exact ⟨_, o', hg', hY', hd⟩

/-- Step 3 of group 6 along a word: the cycle class persists to the structural cut. Consumer:
the group 6 bridge (from the strict terminal to the structural cut). -/
theorem cycClassRun (word : List (Option Nat)) :
    ∀ s : CohortLane, CohortCyc R s → CohortCyc R (word.foldl (cohortLaneStep R) s) := by
  induction word with
  | nil => intro s h; exact h
  | cons ke rest ih => intro s h; exact ih _ (cycClassStep h ke)

end Cyc

/-! ### Source phase: the tail sweep -/

/-- The strict tail packet at source cell `p`, with younger slots behind it. -/
def TailSweep (R : Nat) (s : CohortLane) (p : Nat) : Prop :=
  p < R ∧ cohortTok R s p = .pkt true ∧ CohortYounger R s p

theorem tailPipeStay (bx : Bool) (ox oy : BankRepairDigitOutSh) (T : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokOut oy ≠ .empty) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .pkt T := by
  cases bx <;> cases ox <;> cases oy <;> simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem tailDelStay (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokIn iy ky ≠ .empty) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .pkt T := by
  cases ox <;> cases iy <;> cases ky <;> simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

section Sweep

variable {R : Nat} {s : CohortLane}

/-- The tail sample at the source border starts the sweep. Consumer: `strictTraceRun`'s start,
at the frame after the strict tail's `DigitRecordedSample`. -/
theorem tailSampleStart (hR : 2 ≤ R) (h : cohortTok R s 0 = .pkt true) : TailSweep R s 0 :=
  ⟨by omega, h, cohortRearmInit 0 rfl⟩

/-- Every letter keeps the sweep: the tail stays (still `pkt true`), or it leaves its cell
(which becomes the unread slot) and either sits at the next source cell or has been exported
into target cell `R` with every source cell a younger slot. No hypothesis. Consumer:
`strictPhaseStep`. -/
theorem tailSweepEdge (hR : 2 ≤ R) {p : Nat} (h : TailSweep R s p) (k : Nat) :
    (cohortTok R (cohortEdge R s k) p = .pkt true ∧ TailSweep R (cohortEdge R s k) p) ∨
    (cohortTok R (cohortEdge R s k) p = .other ∧
      ((p + 1 < R ∧ TailSweep R (cohortEdge R s k) (p + 1)) ∨
        (p + 1 = R ∧ CohortYounger R (cohortEdge R s k) R ∧
          cohortTok R (cohortEdge R s k) R = .pkt true))) := by
  obtain ⟨hp, ht, hY⟩ := h
  have hocc : cohortTok R s p ≠ .empty := by rw [ht]; intro hc; cases hc
  have hx : cohortTokOut (s.out p) = .pkt true := by rw [← cohortTokSrc s hp]; exact ht
  by_cases hk : k = p
  · subst hk
    by_cases he : cohortTok R s (k + 1) = .empty
    · have hY' := youngerHop hY hp ht he
      right
      by_cases h1 : k + 1 < R
      · obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
        have hy : cohortTokOut (s.out (k + 1)) = .empty := by
          rw [← cohortTokSrc s h1]; exact he
        obtain ⟨m1, m2⟩ := cohortPipeMove (decide (k = 0)) _ _ true hx hy
        refine ⟨by simp [e1, m1], Or.inl ⟨h1, h1, by rw [e2, m2], hY'⟩⟩
      · have hkR : k + 1 = R := by omega
        obtain ⟨e1, e2⟩ := cohortTokDel R k s hkR
        have hy : cohortTokIn (s.inp (k + 1)) (s.live (k + 1)) = .empty := by
          rw [← cohortTokTgt s (by omega : R ≤ k + 1)]; exact he
        obtain ⟨m1, m2⟩ := cohortDelMove _ _ _ true hx hy
        have key : cohortTok R (cohortEdge R s k) (k + 1) = .pkt true := by rw [e2, m2]
        have cY := congrArg (CohortYounger R (cohortEdge R s k)) hkR
        have cT := congrArg (cohortTok R (cohortEdge R s k)) hkR
        refine ⟨by simp [e1, m1], Or.inr ⟨hkR, ?_, ?_⟩⟩
        · rw [← cY]; exact hY'
        · rw [← cT]; exact key
    · left
      have ht' : cohortTok R (cohortEdge R s k) k = .pkt true := by
        by_cases h1 : k + 1 < R
        · obtain ⟨e1, -⟩ := cohortTokPipe R k s h1
          have hy : cohortTokOut (s.out (k + 1)) ≠ .empty := by
            rw [← cohortTokSrc s h1]; exact he
          rw [e1, tailPipeStay _ _ _ true hx hy]
        · have hkR : k + 1 = R := by omega
          obtain ⟨e1, -⟩ := cohortTokDel R k s hkR
          have hy : cohortTokIn (s.inp (k + 1)) (s.live (k + 1)) ≠ .empty := by
            rw [← cohortTokTgt s (by omega : R ≤ k + 1)]; exact he
          rw [e1, tailDelStay _ _ _ true hx hy]
      exact ⟨ht', hp, ht', youngerEdge hR hY (Nat.le_of_lt hp) hocc k⟩
  · left
    have ht' : cohortTok R (cohortEdge R s k) p = .pkt true := by
      by_cases hk1 : p = k + 1
      · have h1 : k + 1 < R := by omega
        obtain ⟨-, e2⟩ := cohortTokPipe R k s h1
        have hxk := hY k (by omega) (by omega)
        rw [cohortTokSrc s (by omega : k < R)] at hxk
        have hy : cohortTokOut (s.out (k + 1)) ≠ .empty := by
          rw [← cohortTokSrc s h1, ← hk1]; exact hocc
        rw [hk1, e2, (rearmPipeKeep (decide (k = 0)) _ _ hxk hy).2, ← cohortTokSrc s h1, ← hk1]
        exact ht
      · rw [cohortTokFrame R k p s (fun h => hk h.symm) hk1]
        exact ht
    exact ⟨ht', hp, ht', youngerEdge hR hY (Nat.le_of_lt hp) hocc k⟩

end Sweep

/-! ### Target phase: the strict cohort's bottom -/

/-- The bottom of the strict cohort's region: the end of the pair, target cell `R` while it is
not empty (the waiting tail operand, then the launched carry), or a target cell above `R`
holding the live carry. -/
def StrictBottom (R : Nat) (s : CohortLane) (c : Nat) : Prop :=
  c = 2 * R ∨ (c = R ∧ cohortTok R s R ≠ .empty) ∨ (R < c ∧ c < 2 * R ∧ s.live c = true)

/-- The target phase: the chosen cohort in the generated class strictly below the bottom `c`
of the strict cohort, with the younger slots behind the chosen tail. -/
def StrictLane (R : Nat) (s : CohortLane) (lam : Nat → Nat) (c : Nat) : Prop :=
  R ≤ c ∧ CohortChosen R s lam c ∧ CohortYounger R s (lam (R - 1)) ∧ StrictBottom R s c

section Lane

variable {R : Nat} {s : CohortLane} {lam : Nat → Nat} {c : Nat}

theorem strictBottomOk (h : StrictBottom R s c) :
    c < 2 * R → cohortTok R s c ≠ .empty ∧ ∀ T, cohortTok R s c = .settled T → c ≤ R := by
  intro hc
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · omega
  · subst h1
    exact ⟨h2, fun _ _ => Nat.le_refl _⟩
  · rw [cohortTokTgt s (by omega : R ≤ c), h3]
    exact ⟨by simp [cohortTokIn], fun T hT => by simp [cohortTokIn] at hT⟩

/-- While the bottom is below the end of the pair the chosen tail is short of its
destination. -/
theorem strictLanePre (h : StrictLane R s lam c) (hc : c < 2 * R) : lam (R - 1) < R := by
  have hR := h.2.1.two
  have hl := h.2.1.low 0 (by omega)
  have hch := chosenChain h.2.1 0 (R - 1) (by omega) (by omega)
  unfold cohortPos at hl
  omega

/-- A live carry above `R` stays live under a letter, or leaves its cell empty. -/
theorem liveBottomEdge (hRc : R ≤ c) (hc : c < 2 * R) (hl : s.live c = true) (k : Nat) :
    (cohortEdge R s k).live c = true ∨ cohortTok R (cohortEdge R s k) c = .empty := by
  by_cases hck : c = k
  · subst hck
    right
    by_cases h2 : c + 1 < 2 * R
    · rw [(cohortTokFin R c s hRc h2).1, hl]
      generalize decide (c = R) = b
      generalize s.inp (c + 1) = iy
      generalize s.live (c + 1) = ky
      cases ky <;> cases iy <;> simp [bankRepairDigitFinStep, cohortTokIn]
    · rw [cohortTokTerm R c s (by omega), hl]
      simp [cohortTermStep, cohortTokIn]
  · left
    by_cases hck1 : c = k + 1
    · by_cases hkR : k + 1 = R
      · have e := cohortEdgeDelLive R k s hkR
        rw [← hck1] at e
        rw [e, hl]
        exact cohortDelLiveY _ _
      · have e := (cohortEdgeFinParts R k s (by omega) (by omega)).1
        rw [← hck1] at e
        rw [e, hl]
        exact cohortFinLiveY _ _ _ _
    · rw [cohortEdgeLiveFrame R k c s hck hck1]
      exact hl

/-- **Step 1 of group 6.** One letter on the target phase: the chosen cohort follows its ghost
`cohortGenGhost`, the younger slots follow its tail, and the bottom stays (if its cell is still
non-empty) or moves up by one cell (if it emptied). Hypothesis `hgo`: an emptied bottom is
followed by the live carry or by the end of the pair. Consumer: `strictLaneStep`. -/
theorem strictLaneEdge (h : StrictLane R s lam c) (hc : c < 2 * R) (k : Nat)
    (hgo : cohortTok R (cohortEdge R s k) c = .empty →
      c + 1 = 2 * R ∨ (cohortEdge R s k).live (c + 1) = true) :
    StrictLane R (cohortEdge R s k) (cohortGenGhost R s lam k)
      (if cohortTok R (cohortEdge R s k) c = .empty then c + 1 else c) := by
  obtain ⟨hRc, hch, hY, hb⟩ := h
  have hR := hch.two
  have hpre := strictLanePre ⟨hRc, hch, hY, hb⟩ hc
  obtain ⟨hch', -⟩ := chosenEdge hch hpre (strictBottomOk hb) k
  have hY' := youngerGen hch hpre hY k
  by_cases hv : cohortTok R (cohortEdge R s k) c = .empty
  · rw [if_pos hv]
    refine ⟨by omega, chosenExtend hch' (by omega) (by omega) (fun q h1 h2 => by
      have : q = c := by omega
      rw [this]; exact hv), hY', ?_⟩
    rcases hgo hv with h1 | h1
    · exact Or.inl h1
    · by_cases h2 : c + 1 = 2 * R
      · exact Or.inl h2
      · exact Or.inr (Or.inr ⟨by omega, by omega, h1⟩)
  · rw [if_neg hv]
    refine ⟨hRc, hch', hY', ?_⟩
    rcases hb with h1 | ⟨h1, -⟩ | ⟨h1, h2, h3⟩
    · omega
    · subst h1
      exact Or.inr (Or.inl ⟨rfl, hv⟩)
    · rcases liveBottomEdge hRc hc h3 k with h4 | h4
      · exact Or.inr (Or.inr ⟨h1, h2, h4⟩)
      · exact absurd h4 hv

/-- Step 1 on a lane letter (`none`: outside the pair). Consumer: `strictPhaseStep`. -/
theorem strictLaneStep (h : StrictLane R s lam c) (hc : c < 2 * R) (ke : Option Nat)
    (hgo : cohortTok R (cohortLaneStep R s ke) c = .empty →
      c + 1 = 2 * R ∨ (cohortLaneStep R s ke).live (c + 1) = true) :
    StrictLane R (cohortLaneStep R s ke) (cohortGenStep R s lam ke)
      (if cohortTok R (cohortLaneStep R s ke) c = .empty then c + 1 else c) := by
  cases ke with
  | none =>
    have hne := (strictBottomOk h.2.2.2 hc).1
    show StrictLane R s lam (if cohortTok R s c = .empty then c + 1 else c)
    rw [if_neg hne]
    exact h
  | some k => exact strictLaneEdge h hc k hgo

/-- Entry of the target phase at the tail's export: every source cell is a younger slot and
target cell `R` is occupied; the chosen cohort is the rearmed source with no hop. Consumer:
`strictPhaseStep` (exit of the source phase). -/
theorem strictLaneOfExport (hR : 2 ≤ R) (hY : CohortYounger R s R)
    (hocc : cohortTok R s R ≠ .empty) : StrictLane R s (fun _ => 0) R := by
  refine ⟨Nat.le_refl R, ⟨hR, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.le_refl _,
    ?_, ?_, ?_, ?_⟩, cohortRearmInit _ rfl, Or.inr (Or.inl ⟨rfl, hocc⟩)⟩
  · intro i hi
    rw [cohortPosZero]
    omega
  · intro i hi
    rw [cohortPosZero]
    rcases hY (R - 1 - i) (by omega) (by omega) with h1 | h1
    · exact Or.inr (Or.inr ⟨h1, rfl⟩)
    · left
      rw [h1]
      congr 1
      unfold cohortTail
      by_cases hi0 : R - 1 - i = 0
      · rw [decide_eq_true hi0, decide_eq_true (show i + 1 = R by omega)]
      · rw [decide_eq_false hi0, decide_eq_false (show ¬ (i + 1 = R) by omega)]
  · intro i _ hi hs
    rw [cohortPosZero, cohortTokSrc s (by omega)] at hs
    exact absurd hs (cohortTokOutNe _ _)
  · intro q hq _ hnq
    exfalso
    exact hnq (R - 1 - q) (by omega) (by rw [cohortPosZero]; omega)

/-- **Step 2 of group 6.** Once the bottom has reached the end of the pair (the strict
terminal has fired) the lane is in the cycle class, at old phase `2R + 1` (or at the start of
the next cycle if the chosen grid is already complete). Consumer: `strictPhaseCyc`,
`strictLaneTerminal`. -/
theorem strictLaneTop (h : StrictLane R s lam (2 * R)) : CohortCyc R s := by
  obtain ⟨-, hch, hY, -⟩ := h
  have hR := hch.two
  have hg : CohortGen R s lam (2 * R + 1) := by
    refine ⟨by rw [cohortOldDone (by omega)], ?_⟩
    rw [cohortBottomCarry (by omega), show 2 * R + 1 - 1 = 2 * R by omega]
    exact hch
  by_cases hd : gridDone R R lam
  · obtain ⟨a, b, c⟩ := cohortGenDoneStart hg hY hd
    exact ⟨_, 0, a, b, c⟩
  · exact ⟨lam, _, hg, hY, hd⟩

/-- Step 2 at the terminal letter: the live carry at the last target cell retires and the lane
is in the cycle class. Consumer: the group 6 bridge at the recorded strict terminal frame. -/
theorem strictLaneTerminal (h : StrictLane R s lam (2 * R - 1))
    (hl : s.live (2 * R - 1) = true) : CohortCyc R (cohortEdge R s (2 * R - 1)) := by
  have hR := h.2.1.two
  have hv := cohortCarryLast hR hl
  have h' := strictLaneEdge h (by omega) (2 * R - 1) (fun _ => Or.inl (by omega))
  rw [if_pos hv, show 2 * R - 1 + 1 = 2 * R by omega] at h'
  exact strictLaneTop h'

end Lane

/-! ### The tracked phase along a lane trace -/

/-- The phase of the strict cohort with its tracked cell `p`. -/
def StrictPhase (R : Nat) (s : CohortLane) (p : Nat) : Prop :=
  if p < R then TailSweep R s p
  else if p < 2 * R then ∃ lam, StrictLane R s lam p
  else CohortCyc R s

/-- The tracked cell after a letter, read off the new lane: in the source the tail moves when
its cell no longer holds it; in the target the bottom moves when its cell empties. -/
def strictNext (R : Nat) (s' : CohortLane) (p : Nat) : Nat :=
  if p < R then (if cohortTok R s' p = .pkt true then p else p + 1)
  else if p < 2 * R ∧ cohortTok R s' p = .empty then p + 1 else p

/-- The tracked cell along a lane trace `st`, from the cell `p0` at time `0`. -/
def strictTrack (R : Nat) (st : Nat → CohortLane) (p0 : Nat) : Nat → Nat
  | 0 => p0
  | t + 1 => strictNext R (st (t + 1)) (strictTrack R st p0 t)

/-- The target-phase hypothesis at one letter: when the bottom empties, the next cell holds
the live carry or is the end of the pair. -/
def StrictGo (R : Nat) (s' : CohortLane) (p : Nat) : Prop :=
  R ≤ p → p < 2 * R → cohortTok R s' p = .empty → p + 1 = 2 * R ∨ s'.live (p + 1) = true

section Trace

variable {R : Nat}

/-- One letter on the tracked phase. Consumer: `strictTraceRun`. -/
theorem strictPhaseStep (hR : 2 ≤ R) {s : CohortLane} {p : Nat} (h : StrictPhase R s p)
    (ke : Option Nat) (hgo : StrictGo R (cohortLaneStep R s ke) p) :
    StrictPhase R (cohortLaneStep R s ke) (strictNext R (cohortLaneStep R s ke) p) := by
  unfold StrictPhase at h
  unfold strictNext
  by_cases hp : p < R
  · rw [if_pos hp] at h
    rw [if_pos hp]
    cases ke with
    | none =>
      show StrictPhase R s (if cohortTok R s p = .pkt true then p else p + 1)
      rw [if_pos h.2.1]
      unfold StrictPhase
      rw [if_pos hp]
      exact h
    | some k =>
      show StrictPhase R (cohortEdge R s k)
        (if cohortTok R (cohortEdge R s k) p = .pkt true then p else p + 1)
      rcases tailSweepEdge hR h k with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1]
        unfold StrictPhase
        rw [if_pos hp]
        exact h2
      · rw [if_neg (by rw [h1]; intro hc; cases hc)]
        unfold StrictPhase
        rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
        · rw [if_pos h3]
          exact h4
        · rw [if_neg (by omega), if_pos (by omega), h3]
          exact ⟨_, strictLaneOfExport hR h4 (by rw [h5]; intro hc; cases hc)⟩
  · rw [if_neg hp] at h
    rw [if_neg hp]
    by_cases hp2 : p < 2 * R
    · rw [if_pos hp2] at h
      obtain ⟨lam, hl⟩ := h
      have h' := strictLaneStep hl hp2 ke (hgo (by omega) hp2)
      by_cases hv : cohortTok R (cohortLaneStep R s ke) p = .empty
      · rw [if_pos hv] at h'
        rw [if_pos ⟨hp2, hv⟩]
        unfold StrictPhase
        rw [if_neg (by omega)]
        by_cases hq : p + 1 < 2 * R
        · rw [if_pos hq]
          exact ⟨_, h'⟩
        · rw [if_neg hq]
          have he : p + 1 = 2 * R := by omega
          rw [he] at h'
          exact strictLaneTop h'
      · rw [if_neg hv] at h'
        rw [if_neg (fun hc => hv hc.2)]
        unfold StrictPhase
        rw [if_neg hp, if_pos hp2]
        exact ⟨_, h'⟩
    · rw [if_neg hp2] at h
      rw [if_neg (fun hc => hp2 hc.1)]
      unfold StrictPhase
      rw [if_neg hp, if_neg hp2]
      exact cycClassStep h ke

/-- **Run statement of group 6 (lane level).** Along a lane trace `st` (each state the lane
letter of the previous one), from a tracked phase at time `0` (e.g. the tail just sampled,
`tailSampleStart`), the tracked phase holds at every time, provided the target-phase
hypothesis `StrictGo` holds at every letter. Consumer: the group 6 bridge, which instantiates
`st` with the masked lane `cohortProj` of the coupled BANK run and supplies `StrictGo` from the
recorded strict completion. -/
theorem strictTraceRun (hR : 2 ≤ R) (st : Nat → CohortLane) (ke : Nat → Option Nat)
    (hst : ∀ t, st (t + 1) = cohortLaneStep R (st t) (ke t)) (p0 : Nat)
    (h0 : StrictPhase R (st 0) p0)
    (hgo : ∀ t, StrictGo R (st (t + 1)) (strictTrack R st p0 t)) :
    ∀ t, StrictPhase R (st t) (strictTrack R st p0 t) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    have e : strictTrack R st p0 (t + 1) = strictNext R (st (t + 1)) (strictTrack R st p0 t) :=
      rfl
    rw [e]
    have hgo' := hgo t
    rw [hst t] at hgo' ⊢
    exact strictPhaseStep hR ih (ke t) hgo'

/-- Read-off: once the tracked cell has reached the end of the pair, the lane is in the cycle
class. Consumer: the group 6 bridge at the structural cut. -/
theorem strictPhaseCyc {s : CohortLane} {p : Nat} (h : StrictPhase R s p) (hp : 2 * R ≤ p) :
    CohortCyc R s := by
  unfold StrictPhase at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  exact h

/-- The tracked cell never decreases and moves by at most one cell per letter. Consumer: the
group 6 bridge (it locates the terminal letter as the step from `2R - 1` to `2R`). -/
theorem strictNextBound (s' : CohortLane) (p : Nat) :
    p ≤ strictNext R s' p ∧ strictNext R s' p ≤ p + 1 := by
  unfold strictNext
  split
  · split <;> omega
  · split <;> omega

/-- The terminal letter moves the tracked cell from `2R - 1` to `2R`. Consumer: the group 6
bridge at the recorded strict terminal frame. -/
theorem strictNextTerminal (hR : 2 ≤ R) (s : CohortLane) (hl : s.live (2 * R - 1) = true) :
    strictNext R (cohortEdge R s (2 * R - 1)) (2 * R - 1) = 2 * R := by
  unfold strictNext
  rw [if_neg (by omega), if_pos ⟨by omega, cohortCarryLast hR hl⟩]
  omega

end Trace

end L3.DigitEntryPhase

#print axioms L3.DigitEntryPhase.cycClassStep
#print axioms L3.DigitEntryPhase.cycClassRun
#print axioms L3.DigitEntryPhase.cycClassIn
#print axioms L3.DigitEntryPhase.tailSweepEdge
#print axioms L3.DigitEntryPhase.liveBottomEdge
#print axioms L3.DigitEntryPhase.strictLaneEdge
#print axioms L3.DigitEntryPhase.strictLaneStep
#print axioms L3.DigitEntryPhase.strictLaneOfExport
#print axioms L3.DigitEntryPhase.strictLaneTop
#print axioms L3.DigitEntryPhase.strictLaneTerminal
#print axioms L3.DigitEntryPhase.strictPhaseStep
#print axioms L3.DigitEntryPhase.strictTraceRun
#print axioms L3.DigitEntryPhase.strictPhaseCyc
#print axioms L3.DigitEntryPhase.strictNextTerminal
