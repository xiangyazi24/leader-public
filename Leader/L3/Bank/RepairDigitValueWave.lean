import Leader.L3.Bank.RepairDigitFirstZeroClock

/-!
# T20: the successor-value cut and the restarted comparison cut

The two remaining pre-drain cuts on the BANK reference state, written from the receipt rows of
`DigitOriginReceipts` (Target.lean) and repair.tex 4829-5060:

* `BankRepairDigitValuesStableCut` (successorValuesStable): the coupled BANK x audit run of the
  T19 cut (accepted R-fold start, W fixed root, `DigitAt`), with the base value cut after the
  retirement, the first structural cut `rho`, a `DigitValueChain` of five coherent writer
  cohorts per complete block dependency, and every complete block covered by the chain.
* `BankRepairDigitComparisonCut` (preDrain): the same data and the first
  `DigitComparisonReady` cut restarted at the last value cut `sigma_dig`.

Generic facts proved here:

* `bankRepairDigitRankWord`, `bankRepairDigitRankBelow`: a nominated-edge rank certificate
  bounds the length of a shortest reaching word, so the rank method can never certify a bound
  below `n * dist`. This is the formal half of the T20 obstruction (see comms/T20-notes.md).
* `bankRepairDigitChargedChain`: `K` successive stages of charge `c` compose to `K * c`, which is
  the summation of (E.S4) over the block dependencies.
* `bankRepairDigitPreDrainHalfOfClocks`: the 201 pre-drain on the concrete cuts from the two
  named clocks `BankRepairDigitValueWaveClock` and `BankRepairDigitComparisonClock`.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ### The successor-value cut -/

/-- The receipt fields of the value wave on an audit `audit` at root `root`: base value cut
after the retirement, first structural cut, value chain and coverage of every complete block. -/
def BankRepairDigitValueReceipts {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired restart : Nat) : Prop :=
  ∃ (first stop baseCut structural last : Nat) (cuts : List (Nat × Nat)),
    DigitFirstSegment ring root audit.start first stop ∧
    DigitBaseValueCut ring root audit 0 retired baseCut ∧
    DigitFirstCut (DigitStructuralAt ring root audit) structural ∧
    DigitValueChain ring root audit structural first baseCut last restart cuts ∧
    (∀ block : Nat, DigitCompleteBlock ring root audit.start block →
      ∃ stable : Nat, (block, stable) ∈ cuts)

/-- ValuesStable: all successor-value dependencies current and stable, on the coupled BANK x
audit run of the T19 cut. `restart` is the last value cut `sigma_dig`. -/
def BankRepairDigitValuesStableCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n))
    (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired restart : Nat),
    BankRepairRFoldEstablished ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    BankRepairDigitValueReceipts ring root audit retired restart

/-- preDrain: the value receipts and the first comparison-ready cut restarted at the last value
cut (simultaneous strict comparison currentness, repair.tex 4994-5054). -/
def BankRepairDigitComparisonCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n))
    (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired restart comparisonCut : Nat),
    BankRepairRFoldEstablished ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    BankRepairDigitValueReceipts ring root audit retired restart ∧
    DigitFirstCut (DigitComparisonReady ring root audit restart) comparisonCut

/-- The comparison cut carries the value cut. -/
theorem bankRepairDigitComparisonCutStable {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : BankRepairDigitComparisonCut ring hbank z) :
    BankRepairDigitValuesStableCut ring hbank z := by
  obtain ⟨start, word, root, audit, retired, restart, _, hs, hf, hr, hat, hv, _⟩ := h
  exact ⟨start, word, root, audit, retired, restart, hs, hf, hr, hat, hv⟩

/-- The value cut keeps the W fixed root and the coupled audit, as the T19 cut does. -/
theorem bankRepairDigitValuesStableRoot {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : BankRepairDigitValuesStableCut ring hbank z) :
    ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WFixedRoot ring root (piW z.val.1) ∧
      DigitAt ring audit audit.clock (piD z.val.1) audit.current := by
  obtain ⟨_, _, root, audit, _, _, _, _, hr, hat, _⟩ := h
  exact ⟨root, audit, hr, hat⟩

/-- The pre-drain cuts with the concrete boundary, first-zero and successor-value cuts. -/
def bankRepairDigitValueCuts {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDigitPreDrainCuts ring hbank :=
  bankRepairDigitZeroCuts ring hbank (BankRepairDigitValuesStableCut ring hbank)

/-! ### Rank certificates and shortest words -/

/-- A nominated-edge drop on every reachable non-target state gives a reaching word of length at
most the rank. -/
theorem bankRepairDigitRankWord {S : Type} {n : Nat} (next : S → Fin n → S)
    (P : S → Prop) (Φ : S → Nat) (x : S)
    (hdrop : ∀ u : List (Fin n), ¬ P (u.foldl next x) →
      ∃ e : Fin n, Φ (next (u.foldl next x) e) + 1 ≤ Φ (u.foldl next x)) :
    ∃ w : List (Fin n), w.length ≤ Φ x ∧ P (w.foldl next x) := by
  have key : ∀ k : Nat, ∀ u : List (Fin n), Φ (u.foldl next x) ≤ k →
      ∃ w : List (Fin n), w.length ≤ Φ (u.foldl next x) ∧ P ((u ++ w).foldl next x) := by
    intro k
    induction k with
    | zero =>
      intro u hu
      by_cases hp : P (u.foldl next x)
      · exact ⟨[], Nat.zero_le _, by simpa using hp⟩
      · obtain ⟨e, he⟩ := hdrop u hp
        omega
    | succ k ih =>
      intro u hu
      by_cases hp : P (u.foldl next x)
      · exact ⟨[], Nat.zero_le _, by simpa using hp⟩
      · obtain ⟨e, he⟩ := hdrop u hp
        have hq : (u ++ [e]).foldl next x = next (u.foldl next x) e := by
          rw [List.foldl_append]
          rfl
        obtain ⟨w, hw, hpw⟩ := ih (u ++ [e]) (by rw [hq]; omega)
        refine ⟨e :: w, ?_, ?_⟩
        · rw [hq] at hw
          simp only [List.length_cons]
          omega
        · have hassoc : u ++ e :: w = (u ++ [e]) ++ w := by simp
          rw [hassoc]
          exact hpw
  obtain ⟨w, hw, hpw⟩ := key (Φ x) [] (Nat.le_refl _)
  exact ⟨w, hw, by simpa using hpw⟩

/-- The rank of a nominated-edge certificate is at least the length of every shortest reaching
word: if no word shorter than `m` reaches the target, the rank is at least `m`. -/
theorem bankRepairDigitRankBelow {S : Type} {n : Nat} (next : S → Fin n → S)
    (P : S → Prop) (Φ : S → Nat) (x : S)
    (hdrop : ∀ u : List (Fin n), ¬ P (u.foldl next x) →
      ∃ e : Fin n, Φ (next (u.foldl next x) e) + 1 ≤ Φ (u.foldl next x))
    (m : Nat)
    (hfar : ∀ w : List (Fin n), w.length < m → ¬ P (w.foldl next x)) :
    m ≤ Φ x := by
  obtain ⟨w, hw, hpw⟩ := bankRepairDigitRankWord next P Φ x hdrop
  exact Nat.le_of_not_lt (fun h => hfar w (by omega) hpw)

/-! ### Chains of charged stages -/

/-- A stage whose start is inside its finish costs nothing. -/
theorem bankRepairDigitChargedSub {S : Type} {n : Nat} (next : S → Fin n → S)
    (A B : S → Prop) (h : ∀ x, A x → B x) :
    BankRepairDigitChargedStage next A B 0 := by
  intro x hx T
  rw [costNumerator_terminal next B x (h x hx) T]
  simp

/-- Restrict the start and enlarge the finish of a charged stage. -/
theorem bankRepairDigitChargedWeaken {S : Type} {n : Nat} (next : S → Fin n → S)
    (A A' B B' : S → Prop) (c : Nat) (hA : ∀ x, A' x → A x) (hB : ∀ x, B x → B' x)
    (h : BankRepairDigitChargedStage next A B c) :
    BankRepairDigitChargedStage next A' B' c := by
  intro x hx T
  exact Nat.le_trans (Nat.mul_le_mul_left 2
    (L3.Prob.costNumerator_target_mono next B B' hB x T)) (h x (hA x hx) T)

/-- `K` successive stages of charge `c` compose to charge `K * c` (the sum of (E.S4) over the
successive block-dependency stopping times). -/
theorem bankRepairDigitChargedChain {S : Type} {n : Nat} (next : S → Fin n → S)
    (P : Nat → S → Prop) (c : Nat)
    (h : ∀ j : Nat, BankRepairDigitChargedStage next (P j) (P (j + 1)) c) :
    ∀ K : Nat, BankRepairDigitChargedStage next (P 0) (P K) (K * c) := by
  intro K
  induction K with
  | zero =>
    rw [Nat.zero_mul]
    exact bankRepairDigitChargedSub next (P 0) (P 0) (fun _ hx => hx)
  | succ K ih =>
    rw [Nat.succ_mul]
    exact bankRepairDigitZeroCompose next (P 0) (P K) (P (K + 1)) _ _ ih (h K)

/-! ### The two named clocks and the conditional assembly -/

/-- The successor-value wave clock on the concrete cuts (repair.tex 4829-4942, 4994-5020). -/
def BankRepairDigitValueWaveClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    (BankRepairDigitFirstZeroCut ring hbank)
    (BankRepairDigitValuesStableCut ring hbank)
    (bankRepairDigitValueWaveMicroCharge n)

/-- The restarted comparison clock on the concrete cuts (repair.tex 4195-4239, 4944-4992,
5026-5054, 5351-5359). -/
def BankRepairDigitComparisonClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    (BankRepairDigitValuesStableCut ring hbank)
    (BankRepairDigitComparisonCut ring hbank)
    (bankRepairDigitComparisonMicroCharge n)

/-- The value-wave clock from per-block clocks: a family of intermediate cuts starting at the
first-zero cut, `K` block stages of charge `c` each, and `K * c` within `200 n^2`. -/
theorem bankRepairDigitValueWaveOfBlockClocks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (P : Nat → BankReferenceState ring hbank → Prop) (K c : Nat)
    (h0 : ∀ z, BankRepairDigitFirstZeroCut ring hbank z → P 0 z)
    (hstep : ∀ j : Nat, BankRepairDigitChargedStage (bankRepairNext ring hbank) (P j) (P (j + 1)) c)
    (hlast : ∀ z, P K z → BankRepairDigitValuesStableCut ring hbank z)
    (hfit : K * c ≤ bankRepairDigitValueWaveMicroCharge n) :
    BankRepairDigitValueWaveClock ring hbank :=
  bankRepairDigitChargedMono _ _ _ hfit
    (bankRepairDigitChargedWeaken _ (P 0) _ (P K) _ _ h0 hlast
      (bankRepairDigitChargedChain _ P c hstep K))

/-- The 201-half pre-drain from every W-stage entrance on the concrete cuts, given the two named
clocks. -/
theorem bankRepairDigitPreDrainHalfOfClocks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwave : BankRepairDigitValueWaveClock ring hbank)
    (hpair : BankRepairDigitComparisonClock ring hbank) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (BankRepairDigitComparisonCut ring hbank) 201 :=
  bankRepairDigitPreDrainHalfClock ring hn hbank
    (BankRepairDigitValuesStableCut ring hbank) (BankRepairDigitComparisonCut ring hbank)
    hwave hpair

end L3.RenewalReferenceClock
