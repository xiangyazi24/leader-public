import Leader.L3.Bank.RepairDigitFinalRing

/-!
# T18: the final-region flush certificate

The final rank `bankRepairDigitFinalRankOf` (both lanes, read at the previous block's outputs
and the final block's inputs and carries) is lifted to BANK states on the gone-reachable class.
The last delimiter is `L = first + R ⌊(n - 1 - first) / R⌋`.

* `bankRepairDigitFinalFlushTasksHold`: the final certificate at `F + R + U + r`;
* `bankRepairDigitFlushClockHolds`, `bankRepairDigitFirstZeroReceiptHolds`,
  `bankRepairDigitPreDrainHalfHolds`: the unconditional assemblies.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-- The last delimiter of a layout with first delimiter `first` and span `R`. -/
def bankRepairDigitLastDelim (R first n : Nat) : Nat :=
  first + R * ((n - 1 - first) / R)

/-- The layout facts the final rank needs, from the delimiter pattern. -/
theorem bankRepairDigitFinLayout {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (R first : Nat) (hR : 2 ≤ R) (hf2 : 2 ≤ first)
    (hw : first + R + 1 ≤ n)
    (hb : ∀ k : Nat, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0)) :
    R + 2 ≤ bankRepairDigitLastDelim R first n ∧ bankRepairDigitLastDelim R first n < n ∧
    n ≤ bankRepairDigitLastDelim R first n + R ∧
    (S (digitSite ring root (bankRepairDigitLastDelim R first n - R))).word.beta = true ∧
    (S (digitSite ring root (bankRepairDigitLastDelim R first n))).word.beta = true ∧
    (∀ k, bankRepairDigitLastDelim R first n - R < k → k < n →
      k ≠ bankRepairDigitLastDelim R first n → (S (digitSite ring root k)).word.beta = false) ∧
    (∀ k, 0 < k → k < n → (S (digitSite ring root k)).word.beta = true →
      k ≤ bankRepairDigitLastDelim R first n) := by
  have hq : 1 ≤ (n - 1 - first) / R := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hRq := Nat.mul_le_mul_left R hq
  rw [Nat.mul_one] at hRq
  have hLge : first + R ≤ bankRepairDigitLastDelim R first n := by
    unfold bankRepairDigitLastDelim; omega
  obtain ⟨f1, f2, _, f4, f5, f6⟩ := bankRepairDigitLastDelimFacts R first n
    (bankRepairDigitLastDelim R first n) (by omega) (by omega) (by omega)
    (fun k => (S (digitSite ring root k)).word.beta) hb rfl
  obtain ⟨_, g2, g3⟩ := f6 (by omega)
  refine ⟨by omega, f1, f2, g2, f4, ?_, f5⟩
  intro k h1 h2 h3
  by_cases hkL : k < bankRepairDigitLastDelim R first n
  · exact g3 k h1 hkL
  · cases hbk : (S (digitSite ring root k)).word.beta
    · rfl
    · have := f5 k (by omega) h2 hbk
      omega

/-- In the BANK band two spans fit after the leader: `t + 2 (2^t - 1) ≤ n`. -/
theorem bankRepairDigitFinWidth {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).t + 2 * digitSpan (compileAdvice (ceilLogTwo n)) ≤ n := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have hs : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hbank
  have hpop := bankRepairDigitPopulationLower hn hbank
  unfold digitSpan
  rw [ht]
  unfold bankRepairDigitExponent at hpop
  generalize ceilLogTwo (ceilLogTwo n) = s at hs hpop ⊢
  have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
    have := Nat.pow_add 2 (s - 1) 1
    rw [show s - 1 + 1 = s by omega, Nat.pow_one] at this
    omega
  have hE := bankRepairDigitPowLower (s - 1)
  generalize 2 ^ (s - 1) = E at h2s hpop hE
  have hE4 := bankRepairDigitPowLower (E - 4)
  have h16 : 2 ^ E = 2 ^ (E - 4) * 16 := by
    have := Nat.pow_add 2 (E - 4) 4
    rw [show E - 4 + 4 = E by omega] at this
    rw [this]
  omega

theorem bankRepairDigitFinDataOfGone {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (hz : BankRepairDigitGoneReachable ring hbank z) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first z ∧
      2 ≤ first ∧ first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n := by
  obtain ⟨root, first, hL, ht, hf, hb⟩ :=
    bankRepairDigitGoneReachableDelimiters ring hn hbank z hz
  have hw := bankRepairDigitFinWidth hn hbank
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n)
    (by have := bankRepairBankBand hbank; omega)
  exact ⟨root, first, ⟨hL.1, by omega, by omega, hb⟩, by omega, by omega⟩

/-! ### The final rank on the BANK chain -/

open Classical in
/-- The final rank of a BANK state (zero off the layout class). -/
noncomputable def bankRepairDigitFinRank {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Nat :=
  if h : ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first z then
    bankRepairDigitFinalRankOf ring (Classical.choose h)
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n)))
        (Classical.choose (Classical.choose_spec h)) n)
      (piD z.val.1)
  else 0

theorem bankRepairDigitFinRankEq {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (z : BankReferenceState ring hbank) (h : BankRepairDigitLeadData ring hbank root first z) :
    bankRepairDigitFinRank ring hbank z =
      bankRepairDigitFinalRankOf ring root (digitSpan (compileAdvice (ceilLogTwo n)))
        (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
        (piD z.val.1) := by
  have hex : ∃ (r : Fin n) (f : Nat), BankRepairDigitLeadData ring hbank r f z :=
    ⟨root, first, h⟩
  unfold bankRepairDigitFinRank
  rw [dif_pos hex]
  obtain ⟨e1, e2⟩ := bankRepairDigitLeadDataUnique ring hbank _ _ _ _ z h
    (Classical.choose_spec (Classical.choose_spec hex))
  rw [e2, e1]

/-- The nominated edge: a dropping edge when one exists. -/
noncomputable def bankRepairDigitFinChosen {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (e0 : Fin n)
    (z : BankReferenceState ring hbank) : Fin n :=
  if h : ∃ e : Fin n, bankRepairDigitFinRank ring hbank (bankRepairNext ring hbank z e) + 1 ≤
      bankRepairDigitFinRank ring hbank z then Classical.choose h else e0

theorem bankRepairDigitFinChosenSpec {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (e0 : Fin n)
    (z : BankReferenceState ring hbank)
    (h : ∃ e : Fin n, bankRepairDigitFinRank ring hbank (bankRepairNext ring hbank z e) + 1 ≤
      bankRepairDigitFinRank ring hbank z) :
    bankRepairDigitFinRank ring hbank
        (bankRepairNext ring hbank z (bankRepairDigitFinChosen ring hbank e0 z)) + 1 ≤
      bankRepairDigitFinRank ring hbank z := by
  unfold bankRepairDigitFinChosen
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Off the final receipt, some lane fails the final condition below the last delimiter. -/
theorem bankRepairDigitFinalFailing {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (L : Nat) (hLn : L < n)
    (hbL : (S (digitSite ring root L)).word.beta = true)
    (hmax : ∀ k, 0 < k → k < n → (S (digitSite ring root k)).word.beta = true → k ≤ L)
    (hnf : ¬ DigitFinalBoundary ring root S) :
    ∃ (lane0 : DigitLane) (j0 : Nat), j0 < n - L ∧
      ¬ bankRepairDigitFinOKSh (n - L) j0 (bankRepairDigitInL ring root lane0 S L j0)
        (bankRepairDigitLvL ring root lane0 S L j0) := by
  refine Classical.byContradiction (fun hcon => hnf ?_)
  intro source last _ _ hnext lane k hk1 hk2
  have hlast : last = L := by
    have h1 := hmax last hnext.1.1 hnext.1.2.1 hnext.1.2.2
    refine Classical.byContradiction (fun hne => ?_)
    have h2 := hnext.2.2.2.2 L (by omega) hLn
    rw [hbL] at h2
    exact Bool.noConfusion h2
  rw [hlast] at hk1
  obtain ⟨j, rfl⟩ : ∃ j, k = L + j := ⟨k - L, by omega⟩
  have hok : bankRepairDigitFinOKSh (n - L) j (bankRepairDigitInL ring root lane S L j)
      (bankRepairDigitLvL ring root lane S L j) :=
    Classical.byContradiction (fun hb => hcon ⟨lane, j, by omega, hb⟩)
  obtain ⟨e1, _, e3⟩ := bankRepairDigitEndpointViewLane lane S (digitSite ring root (L + j))
  dsimp only [DigitLastCarryInert]
  rw [e1, e3]
  exact Classical.byContradiction (fun hno =>
    bankRepairDigitFinOKShOf n L j hk2 (bankRepairDigitLaneLive lane (S (digitSite ring root (L + j))).top)
      (bankRepairDigitLaneIn lane (S (digitSite ring root (L + j))).top) hno hok)

/-- STEP 3, final region: the final certificate at the paper's budget `F + R + U + r`. -/
theorem bankRepairDigitFinalFlushTasksHold {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) := by
  have hR := bankRepairDigitLeadSpanTwo hbank
  unfold BankRepairDigitFinalFlushTasks BankRepairDigitRegionTasks
  refine ⟨bankRepairDigitFinRank ring hbank,
    bankRepairDigitFinChosen ring hbank ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · intro z₀ word hz₀ hnt
    have hz := bankRepairDigitGoneReachableStep ring hbank z₀ hz₀.1 word
    have hlead := bankRepairDigitLeaderLeadingStable ring hn hbank z₀ hz₀.1 hz₀.2 word
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz hlead hnt ⊢
    obtain ⟨root, first, hd, hf2, hw⟩ := bankRepairDigitFinDataOfGone ring hn hbank z hz
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    obtain ⟨hRL, hLn, _, hbS, hbL, hbF, hmax⟩ := bankRepairDigitFinLayout ring root
      (piD z.val.1) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
    obtain ⟨r', hW, hlb⟩ := hlead
    have hr : r' = root := hd.1.1.2.2.1 r' hW.1
    subst hr
    have hnf : ¬ DigitFinalBoundary ring r' (piD z.val.1) := fun hf =>
      hnt ⟨hz, r', hW, hlb, hf⟩
    apply bankRepairDigitFinChosenSpec
    obtain ⟨lane0, j0, hj0, hbad⟩ := bankRepairDigitFinalFailing ring r' (piD z.val.1) _ hLn
      hbL hmax hnf
    obtain ⟨k, _, hdrop⟩ := bankRepairDigitFinalRankDrop ring (by omega) r' (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      hR hRL hLn (hedge r').2.1 hbS hbL hbF
      (fun k _ => ⟨(hedge (digitSite ring r' k)).2.2.1, (hedge (digitSite ring r' k)).2.2.2⟩)
      lane0 j0 hj0 hbad
    refine ⟨digitSite ring r' k, ?_⟩
    rw [bankRepairDigitFinRankEq ring hbank r' first _
        (bankRepairDigitLeadDataStep ring hn hbank r' first z hd _),
      bankRepairDigitFinRankEq ring hbank r' first z hd, (hedge _).1]
    exact hdrop
  · intro z₀ word hz₀ _ e
    have hz := bankRepairDigitGoneReachableStep ring hbank z₀ hz₀.1 word
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz ⊢
    obtain ⟨root, first, hd, hf2, hw⟩ := bankRepairDigitFinDataOfGone ring hn hbank z hz
    obtain ⟨k, hk, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    obtain ⟨hRL, hLn, _, hbS, hbL, hbF, _⟩ := bankRepairDigitFinLayout ring root
      (piD z.val.1) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
    rw [bankRepairDigitFinRankEq ring hbank root first _
        (bankRepairDigitLeadDataStep ring hn hbank root first z hd _),
      bankRepairDigitFinRankEq ring hbank root first z hd, (hedge _).1]
    exact bankRepairDigitFinalRankStep ring (by omega) root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      hR hRL hLn (hedge root).2.1 hbS hbL hbF
      (fun k _ => ⟨(hedge (digitSite ring root k)).2.2.1, (hedge (digitSite ring root k)).2.2.2⟩)
      k hk
  · intro z hz
    obtain ⟨root, first, hd, hf2, hw⟩ := bankRepairDigitFinDataOfGone ring hn hbank z hz.1
    obtain ⟨_, hLn, hnL, _⟩ := bankRepairDigitFinLayout ring root
      (piD z.val.1) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
    rw [bankRepairDigitFinRankEq ring hbank root first z hd]
    have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
    have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
      compileAdvice_t_large _ (by omega)
    have hspan : digitSpan (compileAdvice (ceilLogTwo n)) =
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) := by
      unfold digitSpan bankRepairDigitRadius
      rw [ht]
    rw [← hspan]
    have h1 := bankRepairDigitFinalRankLe ring root (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n) (piD z.val.1)
    have h2 := bankRepairDigitFinalBudget (digitSpan (compileAdvice (ceilLogTwo n)))
      (n - bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      (by omega) (by omega)
    exact Nat.le_trans h1 h2

/-! ### Unconditional assemblies -/

/-- The flush clock at the remainder charge. -/
theorem bankRepairDigitFlushClockHolds {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitReceiptFlushClock ring hbank (bankRepairDigitFlushMicroCharge n) :=
  bankRepairDigitFlushClockOfFinalRegion ring hn hbank
    (bankRepairDigitFinalFlushTasksHold ring hn hbank)

/-- The first-zero clock with the receipt, from every W-stage entrance. -/
theorem bankRepairDigitFirstZeroReceiptHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitFirstZeroReceiptOfFinalRegion ring hn hbank cuts
    (bankRepairDigitFinalFlushTasksHold ring hn hbank) hzero

/-- The 201-half pre-drain from every W-stage entrance, given the later value stages. -/
theorem bankRepairDigitPreDrainHalfHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 :=
  bankRepairDigitPreDrain201OfFinalRegion ring hn hbank cuts preDrain
    (bankRepairDigitFinalFlushTasksHold ring hn hbank) hzero hwave hpair

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitFinLayout
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinWidth
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinDataOfGone
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinRankEq
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinChosenSpec
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalFailing
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalFlushTasksHold
#print axioms L3.RenewalReferenceClock.bankRepairDigitFlushClockHolds
#print axioms L3.RenewalReferenceClock.bankRepairDigitFirstZeroReceiptHolds
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreDrainHalfHolds
