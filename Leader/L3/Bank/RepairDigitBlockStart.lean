import Leader.L3.Bank.RepairDigitCohortClose

/-!
# T30 item 1: the block entrance just after a closing letter, and the per-block charge

One interior complete pair and one lane, as in `BankRepairDigitCohortClose`.

* `cycleEntryCharge`: on the BANK chain with the cycle ghost, from **any** state of the cycle
  class in cycle `j` (any old phase, any hop counter) the first closing letter (start of cycle
  `j + 1`) costs `≤ 39 n R` doubled. (T25's `cohortCycleStageCharge` is the case of a cycle
  start.)
* `cycleCutCharge`: from the start of cycle `j`, the old cohort of cycle `j + K` is gone (old
  phase `2R + 1`, i.e. its terminal has fired) at cost `≤ K · 39 n R + (2R + 1) · 2n` doubled.
* `blockModelCharge`: entrance plus four cycles plus the old phase of the fifth cycle:
  `39 n R + 4 · 39 n R + (2R + 1) · 2n ≤ 200 n R`. The fifth completion of a block started at a
  closing letter is the terminal of the fifth old cohort, reached in the old phase of the fifth
  cycle, before the fifth closing letter; so the block fits the R10c allowance exactly.
* `JustClosed`: the block entrance on the coupled chain `windowNext` (BANK × audit × cycle
  ghost): the state is the image of a `WinInvD` state under a letter that advanced the arrival
  counter. `justClosedStart` gives the strengthened window invariant and a cycle start there;
  `justClosedWindow` gives T28's closed window (`windowClosingD`).
* `windowSimCharge`: generic transfer on `windowNext` carrying `WinInvD` and any invariant
  `Inv`, by simulation with `cohortCycleNext`.
* `blockEntryCharge`: from every `WinInvD` state, the first `JustClosed` state costs
  `≤ 39 n R` doubled.
-/

namespace L3.BlockStart

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortTransfer
open L3.CohortClose

/-! ### Charges on the BANK chain with the cycle ghost -/

section Model

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- The old-cohort stages of cycle `j`: phase `0` to phase `o` at `2n` per phase. -/
theorem cycleOldChain (j o : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycOld R j 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycOld R j o (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (o * (2 * n)) :=
  bankRepairDigitChargedChain (cohortCycleNext ring hbank root lane src R)
    (fun o w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycOld R j o (cohortProj ring root lane src R (piD w.1.val.1)) w.2) (2 * n)
    (fun o => cohortCycLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortCycOld R j o) (CohortCycOld R j (o + 1)) (cohortGenEdgeAt R o)
      (cohortGenEdgeAtLt hR o) (cohortCycOldStage j o).1 (cohortCycOldStage j o).2) o

include hn hR hsrc hend in
/-- **Entrance**: from any state of the cycle class in cycle `j`, the first closing letter (the
start of cycle `j + 1`) costs `≤ 39 n R` doubled. -/
theorem cycleEntryCharge (j : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2 o)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R (j + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (39 * n * R) := by
  have hold := cycleOldChain ring hn hbank root lane src R hR hsrc hend j (2 * R + 1)
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
      ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2 o)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycOld R j (2 * R + 1) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycMat R j 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    _ (fun _ hw => ⟨hw.1, Or.inl (by
        obtain ⟨o, ho⟩ := hw.2
        exact ⟨o, Or.inl (Nat.zero_le o), ho⟩)⟩)
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
/-- **The cut inside a block**: from the start of cycle `j`, the old cohort of cycle `j + K` is
gone (its terminal has fired) at cost `≤ K · 39 n R + (2R + 1) · 2n` doubled. -/
theorem cycleCutCharge (j K : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycStart R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycOld R (j + K) (2 * R + 1) (cohortProj ring root lane src R (piD w.1.val.1))
          w.2)
      (K * (39 * n * R) + (2 * R + 1) * (2 * n)) := by
  have hcyc := bankRepairDigitChargedChain (cohortCycleNext ring hbank root lane src R)
    (fun i w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycStart R (j + i) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (39 * n * R)
    (fun i => cohortCycleStageCharge ring hn hbank root lane src R hR hsrc hend (j + i)) K
  have hold := bankRepairDigitChargedWeaken (cohortCycleNext ring hbank root lane src R)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycOld R (j + K) 0 (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (fun w => CohortLayout ring hbank root src R w.1 ∧
      CohortCycStart R (j + K) (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    _ _ _ (fun _ hw => ⟨hw.1, Or.inl ⟨0, Or.inl (Nat.le_refl 0), hw.2⟩⟩) (fun _ hw => hw)
    (cycleOldChain ring hn hbank root lane src R hR hsrc hend (j + K) (2 * R + 1))
  exact bankRepairDigitZeroCompose _ _ _ _ _ _ hcyc hold

/-- The block budget: `39 n R + (4 · 39 n R + (2R + 1) · 2n) ≤ 200 n R` for `R ≥ 2`. -/
theorem blockBudget {n R : Nat} (hR : 2 ≤ R) :
    39 * n * R + (4 * (39 * n * R) + (2 * R + 1) * (2 * n)) ≤ 200 * n * R := by
  have e1 : (2 * R + 1) * (2 * n) = 2 * (R * (2 * n)) + 2 * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : R * (2 * n) = 2 * (n * R) := by rw [Nat.mul_comm R, Nat.mul_assoc]
  have e4 : 39 * n * R = 39 * (n * R) := Nat.mul_assoc _ _ _
  have e5 : 200 * n * R = 200 * (n * R) := Nat.mul_assoc _ _ _
  have hnR : n * 2 ≤ n * R := Nat.mul_le_mul_left n hR
  rw [e1, e2, e4, e5]
  omega

include hn hR hsrc hend in
/-- **The block on the model chain**: from any state of the cycle class in cycle `j`, through
the first closing letter (entrance), four full cycles, and the old phase of the fifth cycle
after the entrance (the fifth old cohort's terminal), at cost `≤ 200 n R` doubled. -/
theorem blockModelCharge (j : Nat) :
    BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD w.1.val.1)) w.2 o)
      (fun w => CohortLayout ring hbank root src R w.1 ∧
        CohortCycOld R (j + 1 + 4) (2 * R + 1)
          (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
      (200 * n * R) :=
  bankRepairDigitChargedMono _ _ _ (blockBudget hR)
    (bankRepairDigitZeroCompose _ _ _ _ _ _
      (cycleEntryCharge ring hn hbank root lane src R hR hsrc hend j)
      (cycleCutCharge ring hn hbank root lane src R hR hsrc hend (j + 1) 4))

end Model

/-! ### The entrance on the coupled chain -/

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The block entrance**: the coupled state (BANK × audit × cycle ghost) just after a closing
letter, i.e. the image under a letter that advanced the arrival counter of a state carrying the
strengthened window invariant. -/
def JustClosed
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  ∃ (w0 : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n),
    WinInvD ring hbank root lane src R Base w0.1 w0.2 ∧
    w = windowNext ring hbank root lane src R w0 e ∧ w.2.2 = w0.2.2 + 1

include hn hR hsrc hend in
/-- At the block entrance: the strengthened window invariant holds and the lane is at the start
of the cycle numbered by the arrival counter (the closed cohort is the old cohort, in phase `0`). -/
theorem justClosedStart
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : JustClosed ring hbank root lane src R Base w) :
    WinInvD ring hbank root lane src R Base w.1 w.2 ∧
    CohortCycStart R w.2.2 (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2 := by
  obtain ⟨w0, e, hw0, rfl, hcl⟩ := h
  refine ⟨(winInvDStep ring hn hbank root lane src R hR hsrc hend Base w0.1 w0.2 hw0 e).1, ?_⟩
  obtain ⟨hlay, -, -, ⟨o, hcyc⟩, -⟩ := hw0
  have hproj := (cohortBankStep ring hn hbank root lane src R hR hsrc hend w0.1.1 hlay e).2
  rcases cohortCycStep hcyc (cohortEdgeOf root src R e) with ⟨o', -, hin, -⟩ | hst
  · have h1 := hin.1
    have h2 : (cohortCycleGhost R (cohortProj ring root lane src R (piD w0.1.1.val.1)) w0.2
        (cohortEdgeOf root src R e)).2 = w0.2.2 + 1 := hcl
    omega
  · have h2 : (cohortCycleGhost R (cohortProj ring root lane src R (piD w0.1.1.val.1)) w0.2
        (cohortEdgeOf root src R e)).2 = w0.2.2 + 1 := hcl
    show CohortCycStart R (cohortCycleGhost R (cohortProj ring root lane src R
        (piD w0.1.1.val.1)) w0.2 (cohortEdgeOf root src R e)).2
      (cohortProj ring root lane src R (piD (bankRepairNext ring hbank w0.1.1 e).val.1))
      (cohortCycleGhost R (cohortProj ring root lane src R (piD w0.1.1.val.1)) w0.2
        (cohortEdgeOf root src R e))
    rw [hproj, h2]
    exact hst

include hn hR hsrc hend in
/-- At the block entrance the closed window of T28 is available: the crossings `chi` of the
cohort that just arrived (the old cohort of the new cycle), recorded on the delimiter edge with
increasing times, carrying atoms of their slots' provenance and tail bits, with distinct sampled
operands stamped before their exports, and no extra export between the first and the last
crossing along any continuation. -/
theorem justClosedWindow
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : JustClosed ring hbank root lane src R Base w) :
    ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
      (∀ i, i < R →
        DigitRecordedExport w.1.2 (chi i) ∧ OnEdge ring root lane src R (chi i) ∧
        t0 < (chi i).time ∧
        ∃ a, (chi i).operand = some a ∧ GhostOk ring root lane src R Base w.1.2 (cohortTail R i) a) ∧
      (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
      (∀ a b (id : DigitStamp n), a < R → b < R → (chi a).operand = some (.sampled id) →
        (chi b).operand = some (.sampled id) → a = b) ∧
      (∀ i (id : DigitStamp n), i < R → (chi i).operand = some (.sampled id) →
        id.time < (chi i).time) ∧
      ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
        DigitRecordedExport (word.foldl (windowNext ring hbank root lane src R) w).1.2 x →
        OnEdge ring root lane src R x → (chi 0).time ≤ x.time →
        x.time ≤ (chi (R - 1)).time → ∃ i, i < R ∧ x = chi i := by
  obtain ⟨w0, e, hw0, rfl, hcl⟩ := h
  exact windowClosingD ring hn hbank root lane src R hR hsrc hend Base w0 hw0 e hcl

include hn hR hsrc hend in
/-- **Generic window transfer**: on the coupled chain `windowNext`, a real target `Good` and an
invariant `Inv` carried by every letter off `Good` (on `WinInvD`), with every model state of `B`
forcing `Good`: the first hit of `Good` costs at most the model charge of any stage `A → B` of
`cohortCycleNext`. -/
theorem windowSimCharge
    (Inv Good : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (A B : BankReferenceState ring hbank × ((Nat → Nat) × Nat) → Prop) (c : Nat)
    (hinv : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Inv w → ¬ Good w →
      Inv (windowNext ring hbank root lane src R w e))
    (hgood : ∀ w, WinInvD ring hbank root lane src R Base w.1 w.2 → Inv w → B (w.1.1, w.2) →
      Good w)
    (hc : BankRepairDigitChargedStage (cohortCycleNext ring hbank root lane src R) A B c)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (hi : Inv w) (ha : A (w.1.1, w.2))
    (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R) Good w T ≤ n ^ T * c := by
  have hsim := costNumeratorSimLe (windowNext ring hbank root lane src R)
    (cohortCycleNext ring hbank root lane src R)
    (fun w y => y = (w.1.1, w.2) ∧ WinInvD ring hbank root lane src R Base w.1 w.2 ∧ Inv w)
    Good B
    (fun w y e h hg => by
      obtain ⟨rfl, hw, hi⟩ := h
      exact ⟨rfl, (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).1,
        hinv w e hw hi hg⟩)
    (fun w y h hb => by
      obtain ⟨rfl, hw, hi⟩ := h
      exact hgood w hw hi hb)
    T w (w.1.1, w.2) ⟨rfl, hw, hi⟩
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hsim) (hc _ ha T)

include hn hR hsrc hend in
/-- **Every block can be started just after a closing letter**: from every state carrying the
strengthened window invariant (any cycle, any old phase, any hop counter), the first block
entrance `JustClosed` costs `≤ 39 n R` doubled. -/
theorem blockEntryCharge
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (JustClosed ring hbank root lane src R Base) w T ≤ n ^ T * (39 * n * R) := by
  obtain ⟨o, hcyc⟩ := hw.2.2.2.1
  refine windowSimCharge ring hn hbank root lane src R hR hsrc hend Base
    (fun v => v.2.2 = w.2.2 ∨ JustClosed ring hbank root lane src R Base v)
    (JustClosed ring hbank root lane src R Base)
    (fun v => CohortLayout ring hbank root src R v.1 ∧
      ∃ o, CohortCycIn R w.2.2 (cohortProj ring root lane src R (piD v.1.val.1)) v.2 o)
    (fun v => CohortLayout ring hbank root src R v.1 ∧
      CohortCycStart R (w.2.2 + 1) (cohortProj ring root lane src R (piD v.1.val.1)) v.2)
    (39 * n * R) ?_ ?_ (cycleEntryCharge ring hn hbank root lane src R hR hsrc hend w.2.2) w hw
    (Or.inl rfl) ⟨hw.1, o, hcyc⟩ T
  · intro v e hv hi hg
    rcases hi with hi | hi
    · rcases (winInvDStep ring hn hbank root lane src R hR hsrc hend Base v.1 v.2 hv e).2 with
        hs | ⟨hs, -⟩
      · left
        show (windowGhost ring hbank root lane src R v.1 v.2 e).2 = w.2.2
        rw [hs, hi]
      · exact Or.inr ⟨v, e, hv, rfl, hs⟩
    · exact absurd hi hg
  · intro v hv hi hb
    rcases hi with hi | hi
    · have := hb.2.1
      simp only at this
      omega
    · exact hi

include hn hR hsrc hend in
/-- **The block on the coupled chain**: from any state with the strengthened window invariant and
an invariant `Inv` carried by every letter off `Good`, if every state at which the old cohort of
the fifth cycle after the entrance is gone satisfies `Good`, the first hit of `Good` costs
`≤ 200 n R` doubled: entrance `39 n R`, four cycles `4 · 39 n R`, the fifth old phase
`(2R + 1) · 2n ≤ 5 n R`. -/
theorem blockCharge
    (Inv Good : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hinv : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Inv w → ¬ Good w →
      Inv (windowNext ring hbank root lane src R w e))
    (j : Nat)
    (hgood : ∀ w, WinInvD ring hbank root lane src R Base w.1 w.2 → Inv w →
      (CohortLayout ring hbank root src R w.1.1 ∧
        CohortCycOld R (j + 1 + 4) (2 * R + 1)
          (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2) → Good w)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (hi : Inv w) (hj : w.2.2 = j)
    (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R) Good w T ≤ n ^ T * (200 * n * R) := by
  obtain ⟨o, hcyc⟩ := hw.2.2.2.1
  exact windowSimCharge ring hn hbank root lane src R hR hsrc hend Base Inv Good
    (fun v => CohortLayout ring hbank root src R v.1 ∧
      ∃ o, CohortCycIn R j (cohortProj ring root lane src R (piD v.1.val.1)) v.2 o)
    (fun v => CohortLayout ring hbank root src R v.1 ∧
      CohortCycOld R (j + 1 + 4) (2 * R + 1) (cohortProj ring root lane src R (piD v.1.val.1))
        v.2)
    (200 * n * R) hinv hgood (blockModelCharge ring hn hbank root lane src R hR hsrc hend j) w hw
    hi ⟨hw.1, o, by rw [← hj]; exact hcyc⟩ T

end Coupled

end L3.BlockStart

#print axioms L3.BlockStart.cycleEntryCharge
#print axioms L3.BlockStart.cycleCutCharge
#print axioms L3.BlockStart.blockModelCharge
#print axioms L3.BlockStart.justClosedStart
#print axioms L3.BlockStart.justClosedWindow
#print axioms L3.BlockStart.windowSimCharge
#print axioms L3.BlockStart.blockEntryCharge
#print axioms L3.BlockStart.blockCharge
