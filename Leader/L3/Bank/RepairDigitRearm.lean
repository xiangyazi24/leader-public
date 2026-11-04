import Leader.L3.Bank.RepairDigitCohortStages

/-!
# T25 items 1-2: the rearm (younger-cohort) class and chained cohort cycles

One interior complete pair and one lane, as in `BankRepairDigitPacketClass`.

**The rearm class.** While the chosen cohort is in flight its tail sits in the source, at cell
`t = lam (R - 1)`. Every cell behind it is a younger slot: unread (`U`) or read but not moved
(`D` with the border bit of its cell). This is `CohortYounger R s t`. The younger slots never move
behind the chosen tail: the cell ahead of each is a younger slot or the tail, never empty. When
the tail hops it leaves `U` behind (`bankRepairDigitPipeStep _ (.D true) .E = (.U, .D true)`, and
the delimiter row with an empty target), which is the vacated cell becoming the younger unread
slot at its source position. So the younger ghost is identically `0`, and `Y R s lam' t` of the
T24 notes is `CohortYounger R s t` with `lam' = 0`.

* (a) closure: `youngerGen` (generated phase, ghost `cohortGenGhost`) and `youngerPost` (T22
  transport, ghost `cohortGhost`); `cohortGenStepClosed` combines both with `cohortGenEdge` and
  T22's step into one closure lemma for `CohortGen ∧ CohortYounger` under every letter.
* (b) hand-over: `cohortRearmHandOver`: `CohortSettling R 0 s ∧ CohortYounger R s R` gives
  `CohortGen R s 0 0`; `cohortGenDoneStart`: from the class with a complete grid.
* (c) initialization: `cohortRearmInit`, the trivial younger cohort at `t = 0`.

**Chained cycles.** The lane cannot tell the start of a cycle (old cohort arrived, chosen cohort
rearmed) from its end (chosen cohort arrived, younger cohort rearmed): both are `CohortGen … 0`.
The arrivals are therefore counted by a proof-only ghost: `cohortCycleGhost` advances the chosen
cohort's hop counter by `cohortGenGhost` and, when its grid completes (the chosen cohort has
arrived), resets it to `0` (the younger cohort becomes the chosen one) and increments the arrival
counter. On the BANK chain paired with this ghost (`cohortCycleNext`), `cohortCycleStageCharge`
charges one cycle `≤ 39 n R` (doubled) and `cohortCycleChainCharge` the `K`-th arrival
`≤ K · 39 n R`; `cohortCycleFiveCharge` is `K = 5`.
-/

namespace L3.Rearm

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! ### Rows -/

theorem rearmPipeKeep (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (hx : cohortTokOut ox = .other ∨ cohortTokOut ox = .pkt bx)
    (hy : cohortTokOut oy ≠ .empty) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .pkt bx ∧
      (bankRepairDigitPipeStep bx ox oy).2 = oy := by
  cases bx <;> cases ox <;> cases oy <;> simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem rearmDelKeep (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (hx : cohortTokOut ox = .other ∨ cohortTokOut ox = .pkt false)
    (hy : cohortTokIn iy ky ≠ .empty) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .pkt false := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem rearmPipeHop (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (hx : cohortTokOut ox = .pkt true) (hy : cohortTokOut oy = .empty) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .other := by
  cases bx <;> cases ox <;> cases oy <;> simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem rearmDelHop (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (hx : cohortTokOut ox = .pkt true) (hy : cohortTokIn iy ky = .empty) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .other := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

/-! ### The rearm class -/

/-- The younger slots behind the chosen tail at cell `t`: every source cell below `t` is unread
or a read packet that has not moved. -/
def CohortYounger (R : Nat) (s : CohortLane) (t : Nat) : Prop :=
  ∀ q, q < t → q < R → cohortTok R s q = .other ∨ cohortTok R s q = .pkt (decide (q = 0))

section Younger

variable {R : Nat} {s : CohortLane}

/-- Every letter keeps the younger slots behind an occupied tail cell. -/
theorem youngerEdge (hR : 2 ≤ R) {t : Nat} (hY : CohortYounger R s t) (ht : t ≤ R)
    (hocc : cohortTok R s t ≠ .empty) (k : Nat) : CohortYounger R (cohortEdge R s k) t := by
  intro q hq hqR
  by_cases hkt : t ≤ k
  · rw [cohortTokFrame R k q s (by omega) (by omega)]
    exact hY q hq hqR
  · have hk1 : k + 1 ≤ t := by omega
    have hyocc : cohortTok R s (k + 1) ≠ .empty := by
      by_cases he : k + 1 = t
      · rw [he]
        exact hocc
      · rcases hY (k + 1) (by omega) (by omega) with h1 | h1 <;> rw [h1] <;> intro hc <;>
          cases hc
    by_cases h1 : k + 1 < R
    · obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
      have hx := hY k (by omega) (by omega)
      rw [cohortTokSrc s (by omega : k < R)] at hx
      rw [cohortTokSrc s h1] at hyocc
      obtain ⟨m1, m2⟩ := rearmPipeKeep (decide (k = 0)) _ _ hx hyocc
      by_cases hqk : q = k
      · subst hqk
        rw [e1, m1]
        exact Or.inr rfl
      · by_cases hqk1 : q = k + 1
        · subst hqk1
          rw [e2, m2, ← cohortTokSrc s h1]
          exact hY (k + 1) hq hqR
        · rw [cohortTokFrame R k q s hqk hqk1]
          exact hY q hq hqR
    · have hkR : k + 1 = R := by omega
      by_cases hqk : q = k
      · subst hqk
        obtain ⟨e1, -⟩ := cohortTokDel R q s hkR
        have hx := hY q (by omega) (by omega)
        have hd : decide (q = 0) = false := decide_eq_false (by omega)
        rw [hd, cohortTokSrc s (by omega : q < R)] at hx
        rw [cohortTokTgt s (by omega : R ≤ q + 1)] at hyocc
        rw [e1, rearmDelKeep _ _ _ hx hyocc, hd]
        exact Or.inr rfl
      · rw [cohortTokFrame R k q s hqk (by omega)]
        exact hY q hq hqR

/-- The tail's hop leaves an unread slot behind: the younger class grows by one cell. -/
theorem youngerHop {t : Nat} (hY : CohortYounger R s t) (ht : t < R)
    (hp : cohortTok R s t = .pkt true) (he : cohortTok R s (t + 1) = .empty) :
    CohortYounger R (cohortEdge R s t) (t + 1) := by
  intro q hq hqR
  by_cases hqt : q = t
  · subst hqt
    left
    by_cases h1 : q + 1 < R
    · obtain ⟨e1, -⟩ := cohortTokPipe R q s h1
      rw [cohortTokSrc s ht] at hp
      rw [cohortTokSrc s h1] at he
      rw [e1, rearmPipeHop _ _ _ hp he]
    · obtain ⟨e1, -⟩ := cohortTokDel R q s (by omega)
      rw [cohortTokSrc s ht] at hp
      rw [cohortTokTgt s (by omega : R ≤ q + 1)] at he
      rw [e1, rearmDelHop _ _ _ hp he]
  · rw [cohortTokFrame R t q s (by omega) (by omega)]
    exact hY q (by omega) hqR

theorem cohortTailLast (hR : 2 ≤ R) : cohortTail R (R - 1) = true := by
  unfold cohortTail
  exact decide_eq_true (by omega)

theorem cohortPosLast (R : Nat) (lam : Nat → Nat) : cohortPos R lam (R - 1) = lam (R - 1) := by
  unfold cohortPos
  omega

/-- (a), generated phase: the younger class follows the chosen tail's ghost. -/
theorem youngerGen {lam : Nat → Nat} {c : Nat} (h : CohortChosen R s lam c)
    (hpre : lam (R - 1) < R) (hY : CohortYounger R s (lam (R - 1))) (k : Nat) :
    CohortYounger R (cohortEdge R s k) (cohortGenGhost R s lam k (R - 1)) := by
  have hR := h.two
  have hpT := cohortPosLast R lam
  have htok : cohortTok R s (lam (R - 1)) = .pkt true ∨
      cohortTok R s (lam (R - 1)) = .other := by
    rcases h.pkt (R - 1) (by omega) with h1 | ⟨-, h1⟩ | ⟨h1, -⟩
    · rw [hpT, cohortTailLast hR] at h1
      exact Or.inl h1
    · omega
    · rw [hpT] at h1
      exact Or.inr h1
  have hocc : cohortTok R s (lam (R - 1)) ≠ .empty := by
    rcases htok with h1 | h1 <;> rw [h1] <;> intro hc <;> cases hc
  unfold cohortGenGhost
  by_cases hc : R - 1 < R ∧ lam (R - 1) < R ∧ cohortPos R lam (R - 1) = k ∧
      cohortTok R s k ≠ .other ∧ cohortTok R s (k + 1) = .empty
  · rw [if_pos hc]
    obtain ⟨-, -, hk, hno, he⟩ := hc
    rw [hpT] at hk
    subst hk
    have hp : cohortTok R s (lam (R - 1)) = .pkt true := htok.resolve_right hno
    exact youngerHop hY hpre hp he
  · rw [if_neg hc]
    exact youngerEdge hR hY (by omega) hocc k

/-- (a), transport phase (T22's ghost). -/
theorem youngerPost {lam : Nat → Nat} (h : CohortPostStrict R s lam)
    (hY : CohortYounger R s (lam (R - 1))) (ke : Option Nat) :
    CohortYounger R (cohortLaneStep R s ke) (cohortGhost R s lam ke (R - 1)) := by
  have hR := h.two
  have hpT := cohortPosLast R lam
  cases ke with
  | none =>
    have : cohortGhost R s lam none (R - 1) = lam (R - 1) := by simp [cohortGhost]
    rw [this]
    exact hY
  | some k =>
    have hle := h.le (R - 1) (by omega)
    have htok : cohortTok R s (lam (R - 1)) = .pkt true ∨
        (cohortTok R s (lam (R - 1)) = .settled true ∧ lam (R - 1) = R) := by
      rcases h.pkt (R - 1) (by omega) with h1 | ⟨h1, h2⟩
      · rw [hpT, cohortTailLast hR] at h1
        exact Or.inl h1
      · rw [hpT, cohortTailLast hR] at h1
        exact Or.inr ⟨h1, h2⟩
    have hocc : cohortTok R s (lam (R - 1)) ≠ .empty := by
      rcases htok with h1 | ⟨h1, -⟩ <;> rw [h1] <;> intro hc <;> cases hc
    show CohortYounger R (cohortEdge R s k) _
    unfold cohortGhost
    by_cases hc : R - 1 < R ∧ lam (R - 1) < R ∧ some k = some (cohortPos R lam (R - 1)) ∧
        cohortTok R s (cohortPos R lam (R - 1) + 1) = .empty
    · rw [if_pos hc]
      obtain ⟨-, hlt, hk, he⟩ := hc
      rw [hpT] at hk he
      have hk' : k = lam (R - 1) := Option.some.inj hk
      subst hk'
      have hp : cohortTok R s (lam (R - 1)) = .pkt true := by
        rcases htok with h1 | ⟨-, h2⟩
        · exact h1
        · omega
      exact youngerHop hY hlt hp he
    · rw [if_neg hc]
      exact youngerEdge hR hY hle hocc k

/-- (c) initialization: the trivial younger cohort. -/
theorem cohortRearmInit (t : Nat) (ht : t = 0) : CohortYounger R s t := by
  intro q hq _
  omega

/-- (b) hand-over: the arrived chosen cohort with the rearmed younger cohort behind it is the
next cycle's entry. -/
theorem cohortRearmHandOver (hR : 2 ≤ R) (hS : CohortSettling R 0 s)
    (hY : CohortYounger R s R) : CohortGen R s (fun _ => 0) 0 :=
  cohortGenEntry hR hS (fun q hq => hY q hq hq)

end Younger

/-! ### The generated class with the younger cohort, under every letter -/

/-- The chosen cohort's ghost on a letter (`none`: outside the pair). -/
def cohortGenStep (R : Nat) (s : CohortLane) (lam : Nat → Nat) : Option Nat → Nat → Nat
  | none => lam
  | some k => cohortGenGhost R s lam k

section Closed

variable {R o : Nat} {s : CohortLane} {lam : Nat → Nat}

/-- On the post-strict class the generated ghost is T22's ghost. -/
theorem cohortGenStepPost (h : CohortPostStrict R s lam) (ke : Option Nat) :
    cohortGenStep R s lam ke = cohortGhost R s lam ke := by
  funext i
  cases ke with
  | none => simp [cohortGenStep, cohortGhost]
  | some k =>
    show cohortGenGhost R s lam k i = cohortGhost R s lam (some k) i
    unfold cohortGenGhost cohortGhost
    by_cases hc : i < R ∧ lam i < R ∧ some k = some (cohortPos R lam i) ∧
        cohortTok R s (cohortPos R lam i + 1) = .empty
    · obtain ⟨hi, hl, hk, he⟩ := hc
      have hk' : cohortPos R lam i = k := (Option.some.inj hk).symm
      have hno : cohortTok R s k ≠ .other := by
        rw [← hk']
        rcases h.pkt i hi with h1 | ⟨h1, -⟩ <;> rw [h1] <;> intro hc <;> cases hc
      rw [if_pos ⟨hi, hl, hk', hno, by rw [← hk']; exact he⟩, if_pos ⟨hi, hl, hk, he⟩]
    · rw [if_neg hc, if_neg]
      intro hc'
      obtain ⟨hi, hl, hk, -, he⟩ := hc'
      exact hc ⟨hi, hl, by rw [hk], by rw [hk]; exact he⟩

/-- The post-strict class with its settled top run is the generated class with the old cohort
gone. -/
theorem cohortPostToGen (h : CohortPostStrict R s lam) (ht : CohortSettledTop R s) :
    CohortGen R s lam (2 * R + 1) := by
  have hR := h.two
  refine ⟨by rw [cohortOldDone (by omega)], ?_⟩
  rw [cohortBottomCarry (by omega), show 2 * R + 1 - 1 = 2 * R by omega]
  refine ⟨hR, Nat.le_refl _, h.le, h.mono, ?_, ?_, ?_, h.gap⟩
  · intro i hi
    have := h.le i hi
    unfold cohortPos
    omega
  · intro i hi
    rcases h.pkt i hi with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · intro i hi0 hi hs
    have hli : lam i = R := by
      rcases h.pkt i hi with h1 | ⟨-, h2⟩
      · rw [h1] at hs
        cases hs
      · exact h2
    have hl1 : lam (i - 1) = R := by
      have := cohortChain h (i - 1) i (by omega) hi
      have := h.le (i - 1) (by omega)
      omega
    have hp1 : cohortPos R lam (i - 1) = cohortPos R lam i + 1 := by
      unfold cohortPos
      omega
    obtain ⟨T, hT⟩ := ht (cohortPos R lam i) (by unfold cohortPos; omega)
      (by unfold cohortPos; omega) ⟨_, hs⟩
    rw [← hp1] at hT
    rcases h.pkt (i - 1) (by omega) with h1 | ⟨h1, -⟩
    · rw [h1] at hT
      cases hT
    · exact h1

/-- Once the chosen tail has arrived the old cohort is gone and every chosen slot has
materialized. -/
theorem cohortGenArrived (h : CohortGen R s lam o) (hR1 : ¬ lam (R - 1) < R) :
    o = 2 * R + 1 ∧ ∀ i, i < R → cohortTok R s (cohortPos R lam i) ≠ .other := by
  have hR := h.2.two
  refine ⟨?_, ?_⟩
  · have := cohortOldLe h.1
    by_cases ho : o ≤ 2 * R
    · exact absurd (cohortGenPre h ho) hR1
    · omega
  · intro i hi hu
    rcases h.2.pkt i hi with h1 | ⟨h1, -⟩ | ⟨-, h1⟩
    · rw [h1] at hu
      cases hu
    · rw [h1] at hu
      cases hu
    · have := chosenChain h.2 i (R - 1) (by omega) (by omega)
      omega

/-- (a) closure of the generated class with the younger cohort under every letter, in both
phases; materialized slots stay materialized and the drawn slot materializes. -/
theorem cohortGenStepClosed (h : CohortGen R s lam o) (hY : CohortYounger R s (lam (R - 1)))
    (hnd : ¬ gridDone R R lam) (ke : Option Nat) :
    ∃ o', o ≤ o' ∧ CohortGen R (cohortLaneStep R s ke) (cohortGenStep R s lam ke) o' ∧
      CohortYounger R (cohortLaneStep R s ke) (cohortGenStep R s lam ke (R - 1)) ∧
      ∀ i, i < R → (ke = some (cohortPos R lam i) ∨ cohortTok R s (cohortPos R lam i) ≠ .other) →
        cohortTok R (cohortLaneStep R s ke) (cohortPos R (cohortGenStep R s lam ke) i) ≠
          .other := by
  have hR := h.2.two
  by_cases hpre : lam (R - 1) < R
  · cases ke with
    | none =>
      refine ⟨o, Nat.le_refl _, h, hY, fun i _ hor => ?_⟩
      rcases hor with h1 | h1
      · cases h1
      · exact h1
    | some k =>
      obtain ⟨o', ho, hg, hm⟩ := cohortGenEdge h hpre k
      refine ⟨o', ho, hg, youngerGen h.2 hpre hY k, fun i hi hor => hm i hi ?_⟩
      rcases hor with h1 | h1
      · exact Or.inl (Option.some.inj h1).symm
      · exact Or.inr h1
  · obtain ⟨ho, hmat⟩ := cohortGenArrived h hpre
    subst ho
    obtain ⟨hP, ht⟩ := cohortGenPost h hmat
    have hP' := cohortPostStrictStep hP hnd ke
    have ht' := cohortTopPostStep hP hnd ht ke
    have hY' := youngerPost hP hY ke
    rw [cohortGenStepPost hP ke]
    refine ⟨2 * R + 1, Nat.le_refl _, cohortPostToGen hP' ht', hY', fun i hi _ => ?_⟩
    rcases hP'.pkt i hi with h1 | ⟨h1, -⟩ <;> rw [h1] <;> intro hc <;> cases hc

/-- (b) hand-over from a complete grid: the chosen cohort has arrived, and the rearmed younger
cohort is the next chosen cohort. -/
theorem cohortGenDoneStart (h : CohortGen R s lam o) (hY : CohortYounger R s (lam (R - 1)))
    (hd : gridDone R R lam) :
    CohortGen R s (fun _ => 0) 0 ∧ CohortYounger R s ((fun _ => 0 : Nat → Nat) (R - 1)) ∧
      ¬ gridDone R R (fun _ => 0) := by
  have hR := h.2.two
  have hlR : lam (R - 1) = R := by
    have := hd (R - 1) (by omega)
    have := h.2.le (R - 1) (by omega)
    omega
  obtain ⟨ho, hmat⟩ := cohortGenArrived h (by omega)
  subst ho
  obtain ⟨hP, ht⟩ := cohortGenPost h hmat
  have hS : CohortSettling R 0 s :=
    ⟨fun i hi => cohortDonePacked hP hd hi, ht, fun i hi _ => absurd hi (Nat.not_lt_zero _)⟩
  rw [hlR] at hY
  refine ⟨cohortRearmHandOver hR hS hY, cohortRearmInit _ rfl, fun hd' => ?_⟩
  have h0 : R ≤ 0 := hd' 0 (by omega)
  omega

end Closed

/-! ### The counted cycle ghost -/

/-- The cycle ghost: the chosen cohort's hop counter and the number of arrivals so far. When
the chosen grid completes, the younger cohort becomes the chosen one (counter reset) and the
arrival counter advances. -/
noncomputable def cohortCycleGhost (R : Nat) (s : CohortLane) (g : (Nat → Nat) × Nat)
    (ke : Option Nat) : (Nat → Nat) × Nat :=
  open Classical in
  if gridDone R R (cohortGenStep R s g.1 ke) then ((fun _ => 0), g.2 + 1)
  else (cohortGenStep R s g.1 ke, g.2)

/-- In cycle `j` (after `j` arrivals), the old cohort in phase `o`, the chosen cohort with its
ghost, the younger cohort behind it. -/
def CohortCycIn (R j : Nat) (s : CohortLane) (g : (Nat → Nat) × Nat) (o : Nat) : Prop :=
  g.2 = j ∧ CohortGen R s g.1 o ∧ CohortYounger R s (g.1 (R - 1)) ∧ ¬ gridDone R R g.1

/-- The start of cycle `j`. -/
def CohortCycStart (R j : Nat) (s : CohortLane) (g : (Nat → Nat) × Nat) : Prop :=
  CohortCycIn R j s g 0

/-- Old-cohort stage `o` of cycle `j` (or the cycle already over). -/
def CohortCycOld (R j o : Nat) (s : CohortLane) (g : (Nat → Nat) × Nat) : Prop :=
  (∃ o', (o ≤ o' ∨ 2 * R + 1 ≤ o') ∧ CohortCycIn R j s g o') ∨ CohortCycStart R (j + 1) s g

/-- Materialization stage `a` of cycle `j`. -/
def CohortCycMat (R j a : Nat) (s : CohortLane) (g : (Nat → Nat) × Nat) : Prop :=
  (CohortCycIn R j s g (2 * R + 1) ∧
    ∀ i, i < a → i < R → cohortTok R s (cohortPos R g.1 i) ≠ .other) ∨
  CohortCycStart R (j + 1) s g

section Cycle

variable {R : Nat}

/-- One letter on the cycle class: stay in cycle `j` (phase up, materialization monotone) or
complete the arrival and start cycle `j + 1`. -/
theorem cohortCycStep {j o : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat}
    (h : CohortCycIn R j s g o) (ke : Option Nat) :
    (∃ o', o ≤ o' ∧ CohortCycIn R j (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) o' ∧
      ∀ i, i < R → (ke = some (cohortPos R g.1 i) ∨
          cohortTok R s (cohortPos R g.1 i) ≠ .other) →
        cohortTok R (cohortLaneStep R s ke)
          (cohortPos R (cohortCycleGhost R s g ke).1 i) ≠ .other) ∨
    CohortCycStart R (j + 1) (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) := by
  obtain ⟨hm, hg, hY, hnd⟩ := h
  obtain ⟨o', ho, hg', hY', hmm⟩ := cohortGenStepClosed hg hY hnd ke
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R s g.1 ke)
  · rw [if_pos hd]
    right
    obtain ⟨a, b, c⟩ := cohortGenDoneStart hg' hY' hd
    exact ⟨by rw [hm], a, b, c⟩
  · rw [if_neg hd]
    left
    exact ⟨o', ho, ⟨hm, hg', hY', hd⟩, hmm⟩

theorem cohortCycOldExact {j o : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat}
    (h : CohortCycOld R j o s g) (hn : ¬ CohortCycOld R j (o + 1) s g) :
    o ≤ 2 * R ∧ CohortCycIn R j s g o := by
  rcases h with ⟨o', ho, hin⟩ | hs
  · have ho2 : o ≤ 2 * R := by
      rcases Nat.lt_or_ge (2 * R) o with hl | hl
      · exact (hn (Or.inl ⟨o', Or.inr (by omega), hin⟩)).elim
      · exact hl
    have he : o' = o := by
      rcases Nat.lt_or_ge o o' with hl | hl
      · exact (hn (Or.inl ⟨o', Or.inl (by omega), hin⟩)).elim
      · omega
    rw [he] at hin
    exact ⟨ho2, hin⟩
  · exact (hn (Or.inr hs)).elim

/-- Old-cohort stage `o` of cycle `j`. -/
theorem cohortCycOldStage (j o : Nat) :
    (∀ s g, CohortCycOld R j o s g → ¬ CohortCycOld R j (o + 1) s g → ∀ ke,
      CohortCycOld R j o (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) ∨
        CohortCycOld R j (o + 1) (cohortLaneStep R s ke) (cohortCycleGhost R s g ke)) ∧
    (∀ s g, CohortCycOld R j o s g → ¬ CohortCycOld R j (o + 1) s g →
      CohortCycOld R j (o + 1) (cohortLaneStep R s (some (cohortGenEdgeAt R o)))
        (cohortCycleGhost R s g (some (cohortGenEdgeAt R o)))) := by
  refine ⟨fun s g h hn ke => ?_, fun s g h hn => ?_⟩
  · obtain ⟨-, hin⟩ := cohortCycOldExact h hn
    rcases cohortCycStep hin ke with ⟨o', ho, hin', -⟩ | hs
    · exact Or.inl (Or.inl ⟨o', Or.inl ho, hin'⟩)
    · exact Or.inr (Or.inr hs)
  · obtain ⟨ho2, hm, hg, hY, hnd⟩ := cohortCycOldExact h hn
    have hR := hg.2.two
    have hnold : o < R → ¬ CohortOldAt R (o + 1) s := by
      intro hlt hold
      apply hn
      refine Or.inl ⟨o + 1, Or.inl (Nat.le_refl _), hm, ⟨hold, ?_⟩, hY, hnd⟩
      have hc := hg.2
      rw [cohortBottomSettle (by omega : o ≤ R)] at hc
      rw [cohortBottomSettle (by omega : o + 1 ≤ R)]
      exact hc
    have hadv := cohortGenAdvance hg ho2 hnold
    have hY' := youngerGen hg.2 (cohortGenPre hg ho2) hY (cohortOldEdge R o)
    have hk : cohortGenEdgeAt R o = cohortOldEdge R o := by
      unfold cohortGenEdgeAt
      rw [if_pos ho2]
    rw [hk]
    show CohortCycOld R j (o + 1) (cohortEdge R s (cohortOldEdge R o))
      (cohortCycleGhost R s g (some (cohortOldEdge R o)))
    unfold cohortCycleGhost
    by_cases hd : gridDone R R (cohortGenStep R s g.1 (some (cohortOldEdge R o)))
    · rw [if_pos hd]
      obtain ⟨a, b, c⟩ := cohortGenDoneStart hadv hY' hd
      exact Or.inr ⟨by rw [hm], a, b, c⟩
    · rw [if_neg hd]
      exact Or.inl ⟨o + 1, Or.inl (Nat.le_refl _), hm, hadv, hY', hd⟩

/-- Materialization stage `a` of cycle `j`: the slot `a` is read on its own edge. -/
theorem cohortCycMatStage (j a : Nat) :
    (∀ s g, CohortCycMat R j a s g → ¬ CohortCycMat R j (a + 1) s g → ∀ ke,
      CohortCycMat R j a (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) ∨
        CohortCycMat R j (a + 1) (cohortLaneStep R s ke) (cohortCycleGhost R s g ke)) ∧
    (∀ s g, CohortCycMat R j a s g → ¬ CohortCycMat R j (a + 1) s g →
      CohortCycMat R j (a + 1) (cohortLaneStep R s (some (R - 1 - a)))
        (cohortCycleGhost R s g (some (R - 1 - a)))) := by
  have key : ∀ s g, CohortCycMat R j a s g → ¬ CohortCycMat R j (a + 1) s g →
      CohortCycIn R j s g (2 * R + 1) ∧
        (∀ i, i < a → i < R → cohortTok R s (cohortPos R g.1 i) ≠ .other) ∧
        cohortPos R g.1 a = R - 1 - a := by
    intro s g h hn
    rcases h with ⟨hin, hmat⟩ | hs
    · have hR := hin.2.1.2.two
      have haR : a < R := by
        rcases Nat.lt_or_ge a R with hl | hl
        · exact hl
        · exact (hn (Or.inl ⟨hin, fun i _ hiR => hmat i (by omega) hiR⟩)).elim
      have hu : cohortTok R s (cohortPos R g.1 a) = .other := by
        refine Classical.byContradiction fun hne => hn (Or.inl ⟨hin, fun i hi hiR => ?_⟩)
        rcases Nat.lt_or_ge i a with hl | hl
        · exact hmat i hl hiR
        · have : i = a := by omega
          rw [this]
          exact hne
      have hl0 : g.1 a = 0 := by
        rcases hin.2.1.2.pkt a haR with h1 | ⟨h1, -⟩ | ⟨-, h1⟩
        · rw [hu] at h1
          cases h1
        · rw [hu] at h1
          cases h1
        · exact h1
      refine ⟨hin, hmat, ?_⟩
      unfold cohortPos
      omega
    · exact (hn (Or.inr hs)).elim
  have hfix : ∀ s g o', 2 * R + 1 ≤ o' → CohortCycIn R j s g o' → CohortCycIn R j s g (2 * R + 1) :=
    by
      intro s g o' ho hin
      have := cohortOldLe hin.2.1.1
      have he : o' = 2 * R + 1 := by omega
      rw [he] at hin
      exact hin
  refine ⟨fun s g h hn ke => ?_, fun s g h hn => ?_⟩
  · obtain ⟨hin, hmat, -⟩ := key s g h hn
    rcases cohortCycStep hin ke with ⟨o', ho, hin', hmm⟩ | hs
    · exact Or.inl (Or.inl ⟨hfix _ _ o' ho hin', fun i hi hiR => hmm i hiR (Or.inr (hmat i hi hiR))⟩)
    · exact Or.inr (Or.inr hs)
  · obtain ⟨hin, hmat, hpos⟩ := key s g h hn
    rcases cohortCycStep hin (some (R - 1 - a)) with ⟨o', ho, hin', hmm⟩ | hs
    · refine Or.inl ⟨hfix _ _ o' ho hin', fun i hi hiR => hmm i hiR ?_⟩
      rcases Nat.lt_or_ge i a with hl | hl
      · exact Or.inr (hmat i hl hiR)
      · have : i = a := by omega
        rw [this, hpos]
        exact Or.inl rfl
    · exact Or.inr hs

/-- (c) the first cycle starts at the T24 entry with no arrival yet. -/
theorem cohortCycEntry {s : CohortLane} (hR : 2 ≤ R) (h : CohortSettling R 0 s)
    (hsrc : ∀ q, q < R → cohortTok R s q = .other ∨ cohortTok R s q = .pkt (decide (q = 0))) :
    CohortCycStart R 0 s ((fun _ => 0), 0) := by
  refine ⟨rfl, cohortGenEntry hR h hsrc, cohortRearmInit _ rfl, fun hd => ?_⟩
  have h0 : R ≤ 0 := hd 0 (by omega)
  omega

/-- Any state of the generated class at phase `0` with its younger cohort starts a cycle. -/
theorem cohortCycleFromGen {s : CohortLane} {lam : Nat → Nat} (j : Nat)
    (h : CohortGen R s lam 0) (hY : CohortYounger R s (lam (R - 1))) :
    CohortCycStart R j s (lam, j) := by
  refine ⟨rfl, h, hY, fun hd => ?_⟩
  have hR := h.2.two
  have h1 := cohortGenPre h (Nat.zero_le _)
  have h2 : R ≤ lam (R - 1) := hd (R - 1) (by omega)
  omega

/-- The start of a cycle is physically the previous cohort's arrival (`CohortSettling R 0`) with
the rearmed cohort behind it. -/
theorem cohortCycStartSettling {j : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat}
    (h : CohortCycStart R j s g) :
    CohortSettling R 0 s ∧ ∃ lam, CohortGen R s lam 0 ∧ CohortYounger R s (lam (R - 1)) := by
  obtain ⟨-, hg, hY, -⟩ := h
  have h0 := hg.1
  rw [cohortOldSettle (Nat.zero_le _)] at h0
  exact ⟨h0, g.1, hg, hY⟩

theorem cohortCycOldToMat {j : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat}
    (h : CohortCycOld R j (2 * R + 1) s g) : CohortCycMat R j 0 s g := by
  rcases h with ⟨o', ho, hin⟩ | hs
  · have := cohortOldLe hin.2.1.1
    have he : o' = 2 * R + 1 := by rcases ho with ho | ho <;> omega
    rw [he] at hin
    exact Or.inl ⟨hin, fun i hi _ => absurd hi (Nat.not_lt_zero _)⟩
  · exact Or.inr hs

/-- Transport on the cycle class: while the chosen grid is incomplete the cycle ghost is T22's
ghost; on completion the next cycle starts. -/
theorem cohortCycTransportStep {j : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat}
    (hin : CohortCycIn R j s g (2 * R + 1))
    (hm : ∀ i, i < R → cohortTok R s (cohortPos R g.1 i) ≠ .other) (ke : Option Nat) :
    (cohortGhost R s g.1 ke = (cohortCycleGhost R s g ke).1 ∧
      CohortCycIn R j (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) (2 * R + 1) ∧
      ∀ i, i < R → cohortTok R (cohortLaneStep R s ke)
        (cohortPos R (cohortCycleGhost R s g ke).1 i) ≠ .other) ∨
    (CohortCycStart R (j + 1) (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) ∧
      gridDone R R (cohortGhost R s g.1 ke)) := by
  obtain ⟨hj, hg, hY, hnd⟩ := hin
  obtain ⟨hP, ht⟩ := cohortGenPost hg hm
  have hP' := cohortPostStrictStep hP hnd ke
  have ht' := cohortTopPostStep hP hnd ht ke
  have hY' := youngerPost hP hY ke
  have hgen' := cohortPostToGen hP' ht'
  unfold cohortCycleGhost
  rw [cohortGenStepPost hP ke]
  by_cases hd : gridDone R R (cohortGhost R s g.1 ke)
  · rw [if_pos hd]
    right
    obtain ⟨a, b, c⟩ := cohortGenDoneStart hgen' hY' hd
    exact ⟨⟨by rw [hj], a, b, c⟩, hd⟩
  · rw [if_neg hd]
    left
    refine ⟨rfl, ⟨hj, hgen', hY', hd⟩, fun i hi => ?_⟩
    rcases hP'.pkt i hi with h1 | ⟨h1, -⟩ <;> rw [h1] <;> intro hc <;> cases hc

end Cycle

/-! ### The BANK chain with the cycle ghost -/

/-- The BANK chain paired with the proof-only cycle ghost. -/
noncomputable def cohortCycleNext {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (lane : DigitLane) (src R : Nat)
    (w : BankReferenceState ring hbank × ((Nat → Nat) × Nat)) (e : Fin n) :
    BankReferenceState ring hbank × ((Nat → Nat) × Nat) :=
  (bankRepairNext ring hbank w.1 e,
    cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.val.1)) w.2
      (cohortEdgeOf root src R e))

/-- The transport simulation of cycle `j` by T22's model chain. -/
def CohortCycSim {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (lane : DigitLane) (src R j : Nat)
    (w : BankReferenceState ring hbank × ((Nat → Nat) × Nat)) (y : CohortLane × (Nat → Nat)) :
    Prop :=
  CohortLayout ring hbank root src R w.1 ∧
    ((y.1 = cohortProj ring root lane src R (piD w.1.val.1) ∧ y.2 = w.2.1 ∧
        CohortCycIn R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2 (2 * R + 1) ∧
        ∀ i, i < R → cohortTok R (cohortProj ring root lane src R (piD w.1.val.1))
          (cohortPos R w.2.1 i) ≠ .other) ∨
      (CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2 ∧
        gridDone R R y.2))

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- A one-letter lane stage on the BANK chain with the cycle ghost. -/
theorem cohortCycLaneStage (A B : CohortLane → (Nat → Nat) × Nat → Prop) (κ : Nat)
    (hκ : κ < 2 * R)
    (hcl : ∀ s g, A s g → ¬ B s g → ∀ ke,
      A (cohortLaneStep R s ke) (cohortCycleGhost R s g ke) ∨
        B (cohortLaneStep R s ke) (cohortCycleGhost R s g ke))
    (hch : ∀ s g, A s g → ¬ B s g →
      B (cohortLaneStep R s (some κ)) (cohortCycleGhost R s g (some κ))) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        A (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        B (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (2 * n) := by
  apply chargedOneStep _ _ _ (fun _ => digitSite ring root (src + κ))
  · intro w hw hnB e
    obtain ⟨hL, hA⟩ := hw
    have hnB' : ¬ B (cohortProj ring root lane src R (piD w.1.val.1)) w.2 :=
      fun hb => hnB ⟨hL, hb⟩
    obtain ⟨hL', hst⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend w.1 hL e
    have key := hcl _ _ hA hnB' (cohortEdgeOf root src R e)
    rw [← hst] at key
    rcases key with h1 | h1
    · exact Or.inl ⟨hL', h1⟩
    · exact Or.inr ⟨hL', h1⟩
  · intro w hw hnB
    obtain ⟨hL, hA⟩ := hw
    have hnB' : ¬ B (cohortProj ring root lane src R (piD w.1.val.1)) w.2 :=
      fun hb => hnB ⟨hL, hb⟩
    obtain ⟨hL', hst⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend w.1 hL
      (digitSite ring root (src + κ))
    have key := hch _ _ hA hnB'
    rw [← cohortEdgeOfSite ring root src R hend κ hκ, ← hst] at key
    exact ⟨hL', key⟩

include hn hR hsrc hend in
/-- Transport of cycle `j` on the BANK chain with the cycle ghost: T22's `32 n R`, through the
simulation by the model chain `cohortNext`. -/
theorem cohortCycTransportCharge (j : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycMat R j R (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (32 * n * R) := by
  intro w hw T
  obtain ⟨hL, hM⟩ := hw
  have hsim := L3.CohortTransfer.costNumeratorSimLe (cohortCycleNext ring hbank root lane src R)
    (cohortNext R (cohortEdgeOf root src R)) (CohortCycSim ring hbank root lane src R j)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (CohortDone R)
    (by
      intro w y e hs hng
      obtain ⟨hL, hc⟩ := hs
      rcases hc with ⟨hy1, hy2, hin, hm⟩ | ⟨hs, -⟩
      · obtain ⟨hL', hst⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend w.1 hL e
        have hy : y = (cohortProj ring root lane src R (piD w.1.val.1), w.2.1) := Prod.ext hy1 hy2
        subst hy
        have hst' : cohortProj ring root lane src R
            (piD (cohortCycleNext ring hbank root lane src R w e).1.val.1) =
            cohortLaneStep R (cohortProj ring root lane src R (piD w.1.val.1))
              (cohortEdgeOf root src R e) := hst
        unfold CohortCycSim
        refine ⟨hL', ?_⟩
        rw [hst']
        rcases cohortCycTransportStep hin hm (cohortEdgeOf root src R e) with
          ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨rfl, h1, h2, h3⟩
        · exact Or.inr ⟨h1, h2⟩
      · exact absurd ⟨hL, hs⟩ hng)
    (by
      intro w y hs hd
      obtain ⟨hL, hc⟩ := hs
      rcases hc with ⟨-, hy2, hin, -⟩ | ⟨hs, -⟩
      · exact (hin.2.2.2 (by rw [← hy2]; exact hd)).elim
      · exact ⟨hL, hs⟩)
  have hy : ∃ y, CohortCycSim ring hbank root lane src R j w y ∧ CohortClass R y := by
    rcases hM with ⟨hin, hm⟩ | hs
    · exact ⟨(cohortProj ring root lane src R (piD w.1.val.1), w.2.1),
        ⟨hL, Or.inl ⟨rfl, rfl, hin, fun i hi => hm i hi hi⟩⟩,
        Or.inl (cohortGenPost hin.2.1 (fun i hi => hm i hi hi)).1⟩
    · exact ⟨(cohortProj ring root lane src R (piD w.1.val.1), fun _ => R),
        ⟨hL, Or.inr ⟨hs, fun _ _ => Nat.le_refl R⟩⟩, Or.inr (fun _ _ => Nat.le_refl R)⟩
  obtain ⟨y, hwy, hcls⟩ := hy
  have hdom := cohortDominationCharge (n := n) (R := R) (by omega)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk) y hcls T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (hsim T w y hwy)) hdom

include hn hR hsrc hend in
/-- One cycle on the BANK chain with the cycle ghost: from the start of cycle `j` to the start
of cycle `j + 1` (the `j + 1`-st arrival), `≤ 39 n R` doubled. -/
theorem cohortCycleStageCharge (j : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (39 * n * R) := by
  have hold := bankRepairDigitChargedChain (cohortCycleNext ring hbank root lane src R)
    (fun o w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycOld R j o (cohortProj ring root lane src R (piD w.1.val.1)) w.2) (2 * n)
    (fun o => cohortCycLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortCycOld R j o) (CohortCycOld R j (o + 1)) (cohortGenEdgeAt R o)
      (cohortGenEdgeAtLt hR o) (cohortCycOldStage j o).1 (cohortCycOldStage j o).2) (2 * R + 1)
  have hmat := bankRepairDigitChargedChain (cohortCycleNext ring hbank root lane src R)
    (fun a w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycMat R j a (cohortProj ring root lane src R (piD w.1.val.1)) w.2) (2 * n)
    (fun a => cohortCycLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortCycMat R j a) (CohortCycMat R j (a + 1)) (R - 1 - a) (by omega)
      (cohortCycMatStage j a).1 (cohortCycMatStage j a).2) R
  have h1 := bankRepairDigitChargedWeaken (cohortCycleNext ring hbank root lane src R)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycOld R j 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycStart R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycOld R j (2 * R + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycMat R j 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    _ (fun _ hw => ⟨hw.1, Or.inl ⟨0, Or.inl (Nat.le_refl 0), hw.2⟩⟩)
    (fun _ hw => ⟨hw.1, cohortCycOldToMat hw.2⟩) hold
  have h2 := bankRepairDigitZeroCompose _ _ _ _ _ _ h1 hmat
  have h3 := bankRepairDigitZeroCompose _ _ _ _ _ _ h2
    (cohortCycTransportCharge ring hn hbank root lane src R hR hsrc hend j)
  have e1 : (2 * R + 1) * (2 * n) = 2 * (R * (2 * n)) + 2 * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : R * (2 * n) = 2 * (n * R) := by rw [Nat.mul_comm R, Nat.mul_assoc]
  have e3 : 32 * n * R = 32 * (n * R) := Nat.mul_assoc _ _ _
  have e4 : 39 * n * R = 39 * (n * R) := Nat.mul_assoc _ _ _
  have hnR : n * 2 ≤ n * R := Nat.mul_le_mul_left n hR
  have hle : (2 * R + 1) * (2 * n) + R * (2 * n) + 32 * n * R ≤ 39 * n * R := by
    rw [e1, e2, e3, e4]
    omega
  intro x hx T
  exact Nat.le_trans (h3 x hx T) (Nat.mul_le_mul_left _ hle)

include hn hR hsrc hend in
/-- Chained cycles: from the start of cycle `0`, the `K`-th arrival costs `≤ K · 39 n R`
doubled. -/
theorem cohortCycleChainCharge (K : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R K (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (K * (39 * n * R)) :=
  bankRepairDigitChargedChain (cohortCycleNext ring hbank root lane src R)
    (fun j w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycStart R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2) (39 * n * R)
    (fun j => cohortCycleStageCharge ring hn hbank root lane src R hR hsrc hend j) K

include hn hR hsrc hend in
/-- From a layout state in the generated class at phase `0` with its younger cohort, paired with
the ghost `(lam, 0)`: the `K`-th arrival costs `≤ K · 39 n R` doubled, and the arrival state is
physically `CohortSettling R 0` with the next rearmed cohort behind it. -/
theorem cohortCycleChainFromGen (K : Nat) (z : BankReferenceState ring hbank)
    (hz : CohortLayout ring hbank root src R z) (lam : Nat → Nat)
    (hg : CohortGen R (cohortProj ring root lane src R (piD z.val.1)) lam 0)
    (hY : CohortYounger R (cohortProj ring root lane src R (piD z.val.1)) (lam (R - 1))) :
    ∀ T, 2 * costNumerator (cohortCycleNext ring hbank root lane src R)
        (fun w => CohortLayout ring hbank root src R w.1 ∧
          CohortCycStart R K (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
        (z, (lam, 0)) T ≤ n ^ T * (K * (39 * n * R)) :=
  cohortCycleChainCharge ring hn hbank root lane src R hR hsrc hend K (z, (lam, 0))
    ⟨hz, cohortCycleFromGen 0 hg hY⟩

include hn hR hsrc hend in
/-- The five completions: the fifth arrival costs `≤ 5 · 39 n R` doubled. -/
theorem cohortCycleFiveCharge :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R 5 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (5 * (39 * n * R)) :=
  cohortCycleChainCharge ring hn hbank root lane src R hR hsrc hend 5

end Bank

end L3.Rearm

#print axioms L3.Rearm.cohortGenStepClosed
#print axioms L3.Rearm.cohortRearmHandOver
#print axioms L3.Rearm.cohortRearmInit
#print axioms L3.Rearm.cohortCycEntry
#print axioms L3.Rearm.cohortCycleStageCharge
#print axioms L3.Rearm.cohortCycleChainCharge
#print axioms L3.Rearm.cohortCycleChainFromGen
#print axioms L3.Rearm.cohortCycleFiveCharge
