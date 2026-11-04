import Leader.L3.Bank.RepairDigitPacketClass

/-!
# T24 items 2-3: the old-cohort stages and the materialization cover on the generated class

One interior complete pair, one lane, as in `BankRepairDigitCohortEntry`.

* `CohortGenFrom R o`: the generated class `CohortGen` (T24 item 1) at some old phase `≥ o`
  (capped at the terminal phase `2 R + 1`). `cohortGenFromStage`: every edge keeps it, and the
  nominated old-phase edge `cohortGenEdgeAt R o` (settlement `2 R - 1 - o`, launch `R`,
  consumption, terminal `2 R - 1`) moves it to `o + 1`. These are the rank arguments on
  `bankRepairDigitFinStep` / `cohortTermStep` for the arrived cohort, now run while the chosen
  cohort is in flight; `cohortOldCharge` lifts them to the BANK chain: `(2 R + 1) (2 n)`.
* `CohortGenMat R j`: the old cohort is gone and the chosen slots `0, …, j - 1` have
  materialized. Materialized slots stay materialized (`cohortGenEdge`, second conjunct), and the
  edge at the source cell `R - 1 - j` of the unread slot `j` materializes it
  (`cohortGenMatStage`); `cohortMatCharge`: `R (2 n)` (the `n H_r ≤ n r` cover).
* `cohortGenPostCharge`: from the class at phase `0` to (E) (post-strict + settled top),
  `(2 R + 1) (2 n) + R (2 n)`.
* `cohortCycleCharge` / `cohortCycleChargeLe`: one full cohort cycle, from the class at phase
  `0` (old cohort arrived, chosen cohort rearmed) to the chosen cohort's arrival
  (`CohortSettling R 0`), which is the next cycle's entry: `≤ 39 n R` doubled, inside the
  paper's `20 n r` per cohort.
* `cohortGenCompletionCharge`: to the chosen cohort's own terminal completion.
-/

namespace L3.CohortStages

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! ### Lane level -/

/-- The generated class at an old phase `≥ o` (or terminal). -/
def CohortGenFrom (R o : Nat) (s : CohortLane) : Prop :=
  ∃ lam o', (o ≤ o' ∨ 2 * R + 1 ≤ o') ∧ CohortGen R s lam o'

/-- The nominated old-phase edge (any cell once the phases are exhausted). -/
def cohortGenEdgeAt (R o : Nat) : Nat := if o ≤ 2 * R then cohortOldEdge R o else 0

/-- The old cohort is gone and the chosen slots below `j` have materialized. -/
def CohortGenMat (R j : Nat) (s : CohortLane) : Prop :=
  ∃ lam, CohortGen R s lam (2 * R + 1) ∧
    ∀ i, i < j → i < R → cohortTok R s (cohortPos R lam i) ≠ .other

section Lane

variable {R : Nat}

theorem cohortGenEdgeAtLt (hR : 2 ≤ R) (o : Nat) : cohortGenEdgeAt R o < 2 * R := by
  unfold cohortGenEdgeAt
  by_cases ho : o ≤ 2 * R
  · rw [if_pos ho]
    exact cohortOldEdgeLt hR ho
  · rw [if_neg ho]
    omega

theorem cohortGenFromExact {o : Nat} {s : CohortLane} (h : CohortGenFrom R o s)
    (hn : ¬ CohortGenFrom R (o + 1) s) : o ≤ 2 * R ∧ ∃ lam, CohortGen R s lam o := by
  obtain ⟨lam, o', ho, hg⟩ := h
  have hle := cohortOldLe hg.1
  have ho2 : o ≤ 2 * R := by
    rcases Nat.lt_or_ge (2 * R) o with hl | hl
    · exact (hn ⟨lam, o', Or.inr (by omega), hg⟩).elim
    · exact hl
  have he : o' = o := by
    rcases Nat.lt_or_ge o o' with hl | hl
    · exact (hn ⟨lam, o', Or.inl (by omega), hg⟩).elim
    · omega
  rw [he] at hg
  exact ⟨ho2, lam, hg⟩

/-- The old-phase stage: every edge keeps the class at phase `≥ o`; the nominated edge moves
it to `o + 1`. -/
theorem cohortGenFromStage (o : Nat) :
    (∀ s, CohortGenFrom R o s → ¬ CohortGenFrom R (o + 1) s → ∀ k,
      CohortGenFrom R o (cohortEdge R s k) ∨ CohortGenFrom R (o + 1) (cohortEdge R s k)) ∧
    (∀ s, CohortGenFrom R o s → ¬ CohortGenFrom R (o + 1) s →
      CohortGenFrom R (o + 1) (cohortEdge R s (cohortGenEdgeAt R o))) := by
  refine ⟨fun s h hn k => ?_, fun s h hn => ?_⟩
  · obtain ⟨ho2, lam, hg⟩ := cohortGenFromExact h hn
    obtain ⟨o', ho', hg', -⟩ := cohortGenEdge hg (cohortGenPre hg ho2) k
    exact Or.inl ⟨_, o', Or.inl ho', hg'⟩
  · obtain ⟨ho2, lam, hg⟩ := cohortGenFromExact h hn
    unfold cohortGenEdgeAt
    rw [if_pos ho2]
    refine ⟨_, o + 1, Or.inl (Nat.le_refl _), cohortGenAdvance hg ho2 ?_⟩
    intro hlt hold
    apply hn
    refine ⟨lam, o + 1, Or.inl (Nat.le_refl _), hold, ?_⟩
    have hc := hg.2
    rw [cohortBottomSettle (by omega : o ≤ R)] at hc
    rw [cohortBottomSettle (by omega : o + 1 ≤ R)]
    exact hc

/-- The materialization stage: materialized slots stay materialized; the edge at the source
cell of the unread slot `j` materializes it. -/
theorem cohortGenMatStage (j : Nat) :
    (∀ s, CohortGenMat R j s → ¬ CohortGenMat R (j + 1) s → ∀ k,
      CohortGenMat R j (cohortEdge R s k) ∨ CohortGenMat R (j + 1) (cohortEdge R s k)) ∧
    (∀ s, CohortGenMat R j s → ¬ CohortGenMat R (j + 1) s →
      CohortGenMat R (j + 1) (cohortEdge R s (R - 1 - j))) := by
  have key : ∀ s, CohortGenMat R j s → ¬ CohortGenMat R (j + 1) s →
      ∃ lam, CohortGen R s lam (2 * R + 1) ∧
        (∀ i, i < j → i < R → cohortTok R s (cohortPos R lam i) ≠ .other) ∧
        cohortPos R lam j = R - 1 - j ∧ lam (R - 1) < R := by
    intro s h hn
    obtain ⟨lam, hg, hm⟩ := h
    have hR := hg.2.two
    have hjR : j < R := by
      rcases Nat.lt_or_ge j R with hl | hl
      · exact hl
      · exact (hn ⟨lam, hg, fun i _ hiR => hm i (by omega) hiR⟩).elim
    have hu : cohortTok R s (cohortPos R lam j) = .other := by
      refine Classical.byContradiction fun hne => hn ⟨lam, hg, fun i hi hiR => ?_⟩
      rcases Nat.lt_or_ge i j with hl | hl
      · exact hm i hl hiR
      · have : i = j := by omega
        rw [this]
        exact hne
    have hl0 : lam j = 0 := by
      rcases hg.2.pkt j hjR with h1 | ⟨h1, -⟩ | ⟨-, h1⟩
      · rw [hu] at h1
        cases h1
      · rw [hu] at h1
        cases h1
      · exact h1
    have hch := chosenChain hg.2 j (R - 1) (by omega) (by omega)
    refine ⟨lam, hg, hm, ?_, by omega⟩
    unfold cohortPos
    omega
  refine ⟨fun s h hn k => ?_, fun s h hn => ?_⟩
  · obtain ⟨lam, hg, hm, -, hpre⟩ := key s h hn
    obtain ⟨o', ho', hg', hm'⟩ := cohortGenEdge hg hpre k
    have he : o' = 2 * R + 1 := by
      have := cohortOldLe hg'.1
      omega
    rw [he] at hg'
    exact Or.inl ⟨_, hg', fun i hi hiR => hm' i hiR (Or.inr (hm i hi hiR))⟩
  · obtain ⟨lam, hg, hm, hpos, hpre⟩ := key s h hn
    obtain ⟨o', ho', hg', hm'⟩ := cohortGenEdge hg hpre (R - 1 - j)
    have he : o' = 2 * R + 1 := by
      have := cohortOldLe hg'.1
      omega
    rw [he] at hg'
    refine ⟨_, hg', fun i hi hiR => hm' i hiR ?_⟩
    rcases Nat.lt_or_ge i j with hl | hl
    · exact Or.inr (hm i hl hiR)
    · have : i = j := by omega
      rw [this]
      exact Or.inl hpos

theorem cohortGenFromZero {s : CohortLane} {lam : Nat → Nat} (h : CohortGen R s lam 0) :
    CohortGenFrom R 0 s :=
  ⟨lam, 0, Or.inl (Nat.le_refl 0), h⟩

theorem cohortGenMatOfFrom {s : CohortLane} (h : CohortGenFrom R (2 * R + 1) s) :
    CohortGenMat R 0 s := by
  obtain ⟨lam, o', ho, hg⟩ := h
  have he : o' = 2 * R + 1 := by
    have := cohortOldLe hg.1
    omega
  rw [he] at hg
  exact ⟨lam, hg, fun i hi _ => absurd hi (Nat.not_lt_zero _)⟩

/-- (E): all chosen slots materialized after the old cohort is gone. -/
theorem cohortGenMatPost {s : CohortLane} (h : CohortGenMat R R s) :
    (∃ lam, CohortPostStrict R s lam) ∧ CohortSettledTop R s := by
  obtain ⟨lam, hg, hm⟩ := h
  obtain ⟨hP, ht⟩ := cohortGenPost hg (fun i hi => hm i hi hi)
  exact ⟨⟨lam, hP⟩, ht⟩

end Lane

/-! ### The BANK chain -/

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- The old cohort's settlement, launch, consumption and terminal on the BANK chain, run on the
generated class: `2 R + 1` one-letter stages. -/
theorem cohortOldCharge :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortGenFrom R 0 (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortGenFrom R (2 * R + 1) (cohortProj ring root lane src R (piD z.val.1)))
      ((2 * R + 1) * (2 * n)) :=
  bankRepairDigitChargedChain (bankRepairNext ring hbank)
    (fun j z => CohortLayout ring hbank root src R z ∧
      CohortGenFrom R j (cohortProj ring root lane src R (piD z.val.1))) (2 * n)
    (fun j => cohortLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortGenFrom R j) (CohortGenFrom R (j + 1)) (cohortGenEdgeAt R j)
      (cohortGenEdgeAtLt hR j) (cohortGenFromStage j).1 (cohortGenFromStage j).2) (2 * R + 1)

include hn hR hsrc hend in
/-- The materialization cover on the BANK chain: `R` one-letter stages (`n H_r ≤ n r`). -/
theorem cohortMatCharge :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortGenMat R 0 (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortGenMat R R (cohortProj ring root lane src R (piD z.val.1)))
      (R * (2 * n)) :=
  bankRepairDigitChargedChain (bankRepairNext ring hbank)
    (fun j z => CohortLayout ring hbank root src R z ∧
      CohortGenMat R j (cohortProj ring root lane src R (piD z.val.1))) (2 * n)
    (fun j => cohortLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortGenMat R j) (CohortGenMat R (j + 1)) (R - 1 - j) (by omega)
      (cohortGenMatStage j).1 (cohortGenMatStage j).2) R

include hn hR hsrc hend in
/-- From the generated class at phase `0` to (E): post-strict chosen cohort with settled top. -/
theorem cohortGenPostCharge :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        ∃ lam, CohortGen R (cohortProj ring root lane src R (piD z.val.1)) lam 0)
      (fun z => CohortLayout ring hbank root src R z ∧
        (∃ lam, CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) ∧
        CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1)))
      ((2 * R + 1) * (2 * n) + R * (2 * n)) := by
  have hold := bankRepairDigitChargedWeaken (bankRepairNext ring hbank)
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortGenFrom R 0 (cohortProj ring root lane src R (piD z.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      ∃ lam, CohortGen R (cohortProj ring root lane src R (piD z.val.1)) lam 0)
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortGenFrom R (2 * R + 1) (cohortProj ring root lane src R (piD z.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortGenFrom R (2 * R + 1) (cohortProj ring root lane src R (piD z.val.1)))
    _
    (fun _ hz => ⟨hz.1, (match hz.2 with | ⟨_, h⟩ => cohortGenFromZero h)⟩)
    (fun _ h => h) (cohortOldCharge ring hn hbank root lane src R hR hsrc hend)
  have hmat := bankRepairDigitChargedWeaken (bankRepairNext ring hbank)
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortGenMat R 0 (cohortProj ring root lane src R (piD z.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortGenFrom R (2 * R + 1) (cohortProj ring root lane src R (piD z.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortGenMat R R (cohortProj ring root lane src R (piD z.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      (∃ lam, CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) ∧
      CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1)))
    _
    (fun _ hz => ⟨hz.1, cohortGenMatOfFrom hz.2⟩)
    (fun _ hz => ⟨hz.1, cohortGenMatPost hz.2⟩)
    (cohortMatCharge ring hn hbank root lane src R hR hsrc hend)
  exact bankRepairDigitZeroCompose _ _ _ _ _ _ hold hmat

include hn hR hsrc hend in
/-- One cohort cycle: from the generated class at phase `0` (old cohort arrived, chosen cohort
rearmed) to the chosen cohort's arrival, the next cycle's entry. Old-cohort stages, the
materialization cover and T22's transport. -/
theorem cohortCycleCharge :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        ∃ lam, CohortGen R (cohortProj ring root lane src R (piD z.val.1)) lam 0)
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortSettling R 0 (cohortProj ring root lane src R (piD z.val.1)))
      ((2 * R + 1) * (2 * n) + R * (2 * n) + 32 * n * R) := by
  have hgrid : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        (∃ lam, CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) ∧
        CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortSettling R 0 (cohortProj ring root lane src R (piD z.val.1)))
      (32 * n * R) := by
    intro z hz T
    obtain ⟨hL, ⟨lam, hP⟩, ht⟩ := hz
    exact cohortRealChargeTop ring hn hbank root lane src R hR hsrc hend z hL lam hP ht T
  exact bankRepairDigitZeroCompose _ _ _ _ _ _
    (cohortGenPostCharge ring hn hbank root lane src R hR hsrc hend) hgrid

include hn hR hsrc hend in
/-- One cohort cycle costs at most `39 n R` doubled (`19.5 n R` interactions in expectation),
inside the paper's `20 n r`. -/
theorem cohortCycleChargeLe :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        ∃ lam, CohortGen R (cohortProj ring root lane src R (piD z.val.1)) lam 0)
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortSettling R 0 (cohortProj ring root lane src R (piD z.val.1)))
      (39 * n * R) := by
  have h := cohortCycleCharge ring hn hbank root lane src R hR hsrc hend
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
  exact Nat.le_trans (h x hx T) (Nat.mul_le_mul_left _ hle)

include hn hR hsrc hend in
/-- From the generated class at phase `0` to the chosen cohort's own terminal completion. -/
theorem cohortGenCompletionCharge :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        ∃ lam, CohortGen R (cohortProj ring root lane src R (piD z.val.1)) lam 0)
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortCarry R (R + 1) (cohortProj ring root lane src R (piD z.val.1)))
      ((2 * R + 1) * (2 * n) + R * (2 * n) +
        (32 * n * R + (R * (2 * n) + (R + 1) * (2 * n)))) :=
  bankRepairDigitZeroCompose _ _ _ _ _ _
    (cohortGenPostCharge ring hn hbank root lane src R hR hsrc hend)
    (cohortCompletionCharge ring hn hbank root lane src R hR hsrc hend)

end Bank

end L3.CohortStages

#print axioms L3.CohortStages.cohortGenEdgeAtLt
#print axioms L3.CohortStages.cohortGenFromExact
#print axioms L3.CohortStages.cohortGenFromStage
#print axioms L3.CohortStages.cohortGenMatStage
#print axioms L3.CohortStages.cohortGenFromZero
#print axioms L3.CohortStages.cohortGenMatOfFrom
#print axioms L3.CohortStages.cohortGenMatPost
#print axioms L3.CohortStages.cohortOldCharge
#print axioms L3.CohortStages.cohortMatCharge
#print axioms L3.CohortStages.cohortGenPostCharge
#print axioms L3.CohortStages.cohortCycleCharge
#print axioms L3.CohortStages.cohortCycleChargeLe
#print axioms L3.CohortStages.cohortGenCompletionCharge
