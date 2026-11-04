import Leader.L3.Bank.RepairDigitFinalLaneDrop

/-!
# T18: the final lane rank on the projected ring

Lane `lane` of a projected ring `S` read at the previous block `[L - R, L)` (outputs) and the
final block `[L, n)` (inputs and carries). Each edge class is matched with its lane lemma.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-! ### Lane shapes -/

def bankRepairDigitOutL {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (lane : DigitLane) (S : Fin n → ProjD c) (b i : Nat) : BankRepairDigitOutSh :=
  bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (S (digitSite ring root (b + i))).top)

def bankRepairDigitInL {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (lane : DigitLane) (S : Fin n → ProjD c) (b i : Nat) : BankRepairDigitInSh :=
  bankRepairDigitInShOf (bankRepairDigitLaneIn lane (S (digitSite ring root (b + i))).top)

def bankRepairDigitLvL {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (lane : DigitLane) (S : Fin n → ProjD c) (b i : Nat) : Bool :=
  bankRepairDigitLaneLive lane (S (digitSite ring root (b + i))).top

def bankRepairDigitFinalLaneRankOf {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R L : Nat) (lane : DigitLane) (S : Fin n → ProjD c) : Nat :=
  bankRepairDigitLaneRank R (n - L) (bankRepairDigitOutL ring root lane S (L - R))
    (bankRepairDigitInL ring root lane S L) (bankRepairDigitLvL ring root lane S L)

/-- The final rank: both lanes. -/
def bankRepairDigitFinalRankOf {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R L : Nat) (S : Fin n → ProjD c) : Nat :=
  bankRepairDigitFinalLaneRankOf ring root R L .writer S +
    bankRepairDigitFinalLaneRankOf ring root R L .comparison S

/-! ### Rows on projected records, lane generic -/

theorem bankRepairDigitFinRowD (c : Compiled) (lane : DigitLane) (x y : ProjD c)
    (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hby : y.word.beta = false) :
    (bankRepairDigitInShOf (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x),
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x,
      bankRepairDigitInShOf (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y),
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y) =
    bankRepairDigitFinStep x.word.beta (bankRepairDigitInShOf (bankRepairDigitLaneIn lane x.top))
      (bankRepairDigitLaneLive lane x.top)
      (bankRepairDigitInShOf (bankRepairDigitLaneIn lane y.top))
      (bankRepairDigitLaneLive lane y.top) := by
  cases lane
  · exact bankRepairDigitWriterFinRow c x.lift y.lift hl hly hby
  · exact bankRepairDigitComparisonFinRow c x.lift y.lift hl hly hby

theorem bankRepairDigitDelRowD (c : Compiled) (lane : DigitLane) (x y : ProjD c)
    (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hbx : x.word.beta = false) (hby : y.word.beta = true) :
    (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).x),
      bankRepairDigitInShOf (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y),
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y) =
    bankRepairDigitDelStep (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane x.top))
      (bankRepairDigitInShOf (bankRepairDigitLaneIn lane y.top))
      (bankRepairDigitLaneLive lane y.top) := by
  cases lane
  · exact bankRepairDigitWriterDelRow c x.lift y.lift hl hly hbx hby
  · exact bankRepairDigitComparisonDelRow c x.lift y.lift hl hly hbx hby

theorem bankRepairDigitPipeRowD (c : Compiled) (lane : DigitLane) (x y : ProjD c)
    (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hby : y.word.beta = false) :
    (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).x),
      bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).y)) =
    bankRepairDigitPipeStep x.word.beta
      (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane x.top))
      (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane y.top)) := by
  cases lane
  · exact bankRepairDigitWriterPipeRow c x.lift y.lift hl hly hby
  · exact bankRepairDigitComparisonPipeRow c x.lift y.lift hl hly hby

theorem bankRepairDigitEntryRowD (c : Compiled) (lane : DigitLane) (x y : ProjD c)
    (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hby : y.word.beta = true) :
    bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).y =
      bankRepairDigitLaneOut lane y.top := by
  obtain ⟨h1, h2⟩ := bankRepairDigitEntryRow c x.lift y.lift hl hly hby
  cases lane
  · exact h1
  · exact h2

theorem bankRepairDigitResetRowD (c : Compiled) (lane : DigitLane) (x y : ProjD c)
    (hr : (x.word.native.l || y.word.native.l) = true) :
    bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x = .E ∧
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x = false := by
  obtain ⟨a1, -, -, -, a5, -, a7, -, -, -, a11, -⟩ :=
    bankRepairDigitRootEdgeResets c x.lift y.lift x.word.beta y.word.beta hr
  cases lane
  · refine ⟨a1, ?_⟩
    show (liveTopPair c x.lift y.lift x.word.beta y.word.beta).x.wCarry.isW = false
    rw [a5]; rfl
  · refine ⟨a7, ?_⟩
    show (liveTopPair c x.lift y.lift x.word.beta y.word.beta).x.qCarry.isL = false
    rw [a11]; rfl

/-! ### Edge classes -/

section Edges

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
  (S : Fin n → ProjD c) (R L : Nat) (hR : 2 ≤ R) (hRL : R + 2 ≤ L) (hLn : L < n)
  (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
  (hbS : (S (digitSite ring root (L - R))).word.beta = true)
  (hbL : (S (digitSite ring root L)).word.beta = true)
  (hbF : ∀ k, L - R < k → k < n → k ≠ L → (S (digitSite ring root k)).word.beta = false)
  (lane : DigitLane)

include hn hRL hroot hbL hbF in
theorem bankRepairDigitFinalLaneFin (j : Nat) (hj : L + j + 1 < n)
    (hbX : (pairW (S (digitSite ring root (L + j))).word
      (S (digitSite ring root (L + j + 1))).word).1.beta =
        (S (digitSite ring root (L + j))).word.beta)
    (hbY : (pairW (S (digitSite ring root (L + j))).word
      (S (digitSite ring root (L + j + 1))).word).2.beta =
        (S (digitSite ring root (L + j + 1))).word.beta) :
    bankRepairDigitFinalLaneRankOf ring root R L lane
        (phiD ring S (digitSite ring root (L + j))) +
      (if bankRepairDigitFinActive
          (decide (0 < bankRepairDigitLastStart (n - L) (bankRepairDigitInL ring root lane S L)
            (bankRepairDigitLvL ring root lane S L)))
          (decide (j = 0)) (bankRepairDigitInL ring root lane S L j)
          (bankRepairDigitLvL ring root lane S L j)
          (bankRepairDigitInL ring root lane S L (j + 1))
          (bankRepairDigitLvL ring root lane S L (j + 1)) = true then 1 else 0) ≤
    bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hPX, hPY, hPo⟩ :=
    bankRepairDigitLeadEdgeSites ring hn root S (L + j) (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot (L + j) (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (L + j + 1) (by omega) hj
  have hby := hbF (L + j + 1) (by omega) hj (by omega)
  have hbx : (S (digitSite ring root (L + j))).word.beta = decide (j = 0) := by
    by_cases h : j = 0
    · subst h; simpa using hbL
    · rw [hbF (L + j) (by omega) (by omega) (by omega)]
      exact (decide_eq_false h).symm
  have hrow := bankRepairDigitFinRowD c lane _ _ hxl hyl hby
  rw [hbx] at hrow
  unfold bankRepairDigitFinalLaneRankOf
  generalize phiD ring S (digitSite ring root (L + j)) = T at hPX hPY hPo ⊢
  have hoo : ∀ i, i < R → bankRepairDigitOutL ring root lane T (L - R) i =
      bankRepairDigitOutL ring root lane S (L - R) i := by
    intro i hi
    unfold bankRepairDigitOutL
    rw [hPo (L - R + i) (by omega) (by omega) (by omega) (by omega)]
  have ho : ∀ k, k < n - L → k ≠ j → k ≠ j + 1 →
      bankRepairDigitInL ring root lane T L k = bankRepairDigitInL ring root lane S L k ∧
        bankRepairDigitLvL ring root lane T L k = bankRepairDigitLvL ring root lane S L k := by
    intro k hk h1 h2
    unfold bankRepairDigitInL bankRepairDigitLvL
    rw [hPo (L + k) (by omega) (by omega) (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  have hr : (bankRepairDigitInL ring root lane T L j, bankRepairDigitLvL ring root lane T L j,
      bankRepairDigitInL ring root lane T L (j + 1),
      bankRepairDigitLvL ring root lane T L (j + 1)) =
      bankRepairDigitFinStep (decide (j = 0)) (bankRepairDigitInL ring root lane S L j)
        (bankRepairDigitLvL ring root lane S L j) (bankRepairDigitInL ring root lane S L (j + 1))
        (bankRepairDigitLvL ring root lane S L (j + 1)) := by
    show (bankRepairDigitInShOf (bankRepairDigitLaneIn lane (T (digitSite ring root (L + j))).top),
      bankRepairDigitLaneLive lane (T (digitSite ring root (L + j))).top,
      bankRepairDigitInShOf (bankRepairDigitLaneIn lane (T (digitSite ring root (L + j + 1))).top),
      bankRepairDigitLaneLive lane (T (digitSite ring root (L + j + 1))).top) = _
    rw [hPX, hPY]
    exact hrow
  rw [bankRepairDigitLaneRankCongr R (n - L) (bankRepairDigitOutL ring root lane S (L - R))
    (bankRepairDigitOutL ring root lane T (L - R)) (bankRepairDigitInL ring root lane T L)
    (bankRepairDigitInL ring root lane T L) (bankRepairDigitLvL ring root lane T L)
    (bankRepairDigitLvL ring root lane T L) hoo (fun _ _ => ⟨rfl, rfl⟩)]
  exact bankRepairDigitLaneFin R (n - L) j (by omega) _ _ _ _ _ ho hr

include hn hRL hLn hroot in
theorem bankRepairDigitFinalLaneReset (k : Nat) (hkn : k + 1 = n) (hLk : L ≤ k)
    (hbX : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).1.beta = (S (digitSite ring root k)).word.beta)
    (hbY : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).2.beta =
        (S (digitSite ring root (k + 1))).word.beta) :
    bankRepairDigitFinalLaneRankOf ring root R L lane (phiD ring S (digitSite ring root k)) +
      bankRepairDigitLam (n - L) (n - L - 1)
        (decide (0 < bankRepairDigitLastStart (n - L) (bankRepairDigitInL ring root lane S L)
          (bankRepairDigitLvL ring root lane S L)))
        (bankRepairDigitInL ring root lane S L (n - L - 1))
        (bankRepairDigitLvL ring root lane S L (n - L - 1)) ≤
    bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hPX, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S k (by omega) hbX hbY
  have hyl : (S (digitSite ring root (k + 1))).word.native.l = true :=
    (hroot _).2 (by rw [hkn, bankRepairDigitSiteN])
  have hres := bankRepairDigitResetRowD c lane (S (digitSite ring root k))
    (S (digitSite ring root (k + 1))) (by rw [hyl, Bool.or_true])
  unfold bankRepairDigitFinalLaneRankOf
  generalize phiD ring S (digitSite ring root k) = T at hPX hPY hPo ⊢
  have hoo : ∀ i, i < R → bankRepairDigitOutL ring root lane T (L - R) i =
      bankRepairDigitOutL ring root lane S (L - R) i := by
    intro i hi
    unfold bankRepairDigitOutL
    rw [hPo (L - R + i) (by omega) (by omega) (by omega) (by omega)]
  have ho : ∀ k', k' < n - L → k' ≠ n - L - 1 →
      bankRepairDigitInL ring root lane T L k' = bankRepairDigitInL ring root lane S L k' ∧
        bankRepairDigitLvL ring root lane T L k' = bankRepairDigitLvL ring root lane S L k' := by
    intro k' hk1 hk2
    unfold bankRepairDigitInL bankRepairDigitLvL
    rw [hPo (L + k') (by omega) (by omega) (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  have e : L + (n - L - 1) = k := by omega
  have hx : bankRepairDigitInL ring root lane T L (n - L - 1) = .E := by
    unfold bankRepairDigitInL
    rw [e, hPX, hres.1] <;> rfl
  have hk : bankRepairDigitLvL ring root lane T L (n - L - 1) = false := by
    unfold bankRepairDigitLvL
    rw [e, hPX]
    exact hres.2
  rw [bankRepairDigitLaneRankCongr R (n - L) (bankRepairDigitOutL ring root lane S (L - R))
    (bankRepairDigitOutL ring root lane T (L - R)) (bankRepairDigitInL ring root lane T L)
    (bankRepairDigitInL ring root lane T L) (bankRepairDigitLvL ring root lane T L)
    (bankRepairDigitLvL ring root lane T L) hoo (fun _ _ => ⟨rfl, rfl⟩)]
  exact bankRepairDigitLaneReset R (n - L) (by omega) _ _ _ _ _ ho hx hk

include hn hR hRL hLn hroot hbL hbF in
theorem bankRepairDigitFinalLaneDel (k : Nat) (hkL : k + 1 = L)
    (hbX : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).1.beta = (S (digitSite ring root k)).word.beta)
    (hbY : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).2.beta =
        (S (digitSite ring root (k + 1))).word.beta) :
    bankRepairDigitFinalLaneRankOf ring root R L lane (phiD ring S (digitSite ring root k)) +
      (if 0 < bankRepairDigitLastStart (n - L) (bankRepairDigitInL ring root lane S L)
            (bankRepairDigitLvL ring root lane S L) ∧
          ((bankRepairDigitIsDSh (bankRepairDigitOutL ring root lane S (L - R) (R - 1)) = true ∧
              bankRepairDigitInL ring root lane S L 0 = .E ∧
              bankRepairDigitLvL ring root lane S L 0 = false) ∨
            bankRepairDigitOutL ring root lane S (L - R) (R - 1) = .U) then 1 else 0) ≤
    bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hPX, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S k (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot k (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (k + 1) (by omega) (by omega)
  have hbx := hbF k (by omega) (by omega) (by omega)
  have hby : (S (digitSite ring root (k + 1))).word.beta = true := by rw [hkL]; exact hbL
  have hrow := bankRepairDigitDelRowD c lane _ _ hxl hyl hbx hby
  unfold bankRepairDigitFinalLaneRankOf
  generalize phiD ring S (digitSite ring root k) = T at hPX hPY hPo ⊢
  have hoo : ∀ i, i < R → i ≠ R - 1 → bankRepairDigitOutL ring root lane T (L - R) i =
      bankRepairDigitOutL ring root lane S (L - R) i := by
    intro i hi hi'
    unfold bankRepairDigitOutL
    rw [hPo (L - R + i) (by omega) (by omega) (by omega) (by omega)]
  have ho : ∀ k', k' < n - L → k' ≠ 0 →
      bankRepairDigitInL ring root lane T L k' = bankRepairDigitInL ring root lane S L k' ∧
        bankRepairDigitLvL ring root lane T L k' = bankRepairDigitLvL ring root lane S L k' := by
    intro k' hk1 hk2
    unfold bankRepairDigitInL bankRepairDigitLvL
    rw [hPo (L + k') (by omega) (by omega) (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  have e1 : L - R + (R - 1) = k := by omega
  have e2 : L + 0 = k + 1 := by omega
  have hr : (bankRepairDigitOutL ring root lane T (L - R) (R - 1),
      bankRepairDigitInL ring root lane T L 0, bankRepairDigitLvL ring root lane T L 0) =
      bankRepairDigitDelStep (bankRepairDigitOutL ring root lane S (L - R) (R - 1))
        (bankRepairDigitInL ring root lane S L 0) (bankRepairDigitLvL ring root lane S L 0) := by
    unfold bankRepairDigitOutL bankRepairDigitInL bankRepairDigitLvL
    rw [e1, e2, hPX, hPY]
    exact hrow
  exact bankRepairDigitLaneDel R (n - L) (by omega) (by omega) _ _ _ _ _ _ hoo ho hr

include hn hR hRL hLn hroot hbS hbF in
theorem bankRepairDigitFinalLanePipe (i : Nat) (hi : i + 1 < R)
    (hbX : (pairW (S (digitSite ring root (L - R + i))).word
      (S (digitSite ring root (L - R + i + 1))).word).1.beta =
        (S (digitSite ring root (L - R + i))).word.beta)
    (hbY : (pairW (S (digitSite ring root (L - R + i))).word
      (S (digitSite ring root (L - R + i + 1))).word).2.beta =
        (S (digitSite ring root (L - R + i + 1))).word.beta) :
    bankRepairDigitFinalLaneRankOf ring root R L lane
        (phiD ring S (digitSite ring root (L - R + i))) +
      (if 0 < bankRepairDigitLastStart (n - L) (bankRepairDigitInL ring root lane S L)
            (bankRepairDigitLvL ring root lane S L) ∧
          min (bankRepairDigitPhiW R i (bankRepairDigitPipeStep (decide (i = 0))
                (bankRepairDigitOutL ring root lane S (L - R) i)
                (bankRepairDigitOutL ring root lane S (L - R) (i + 1))).1)
              (bankRepairDigitPhiW R (i + 1) (bankRepairDigitPipeStep (decide (i = 0))
                (bankRepairDigitOutL ring root lane S (L - R) i)
                (bankRepairDigitOutL ring root lane S (L - R) (i + 1))).2) <
            bankRepairDigitPhiOf R (bankRepairDigitOutL ring root lane S (L - R))
        then 1 else 0) ≤
    bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hPX, hPY, hPo⟩ :=
    bankRepairDigitLeadEdgeSites ring hn root S (L - R + i) (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot (L - R + i) (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (L - R + i + 1) (by omega) (by omega)
  have hby := hbF (L - R + i + 1) (by omega) (by omega) (by omega)
  have hbx : (S (digitSite ring root (L - R + i))).word.beta = decide (i = 0) := by
    by_cases h : i = 0
    · subst h; simpa using hbS
    · rw [hbF (L - R + i) (by omega) (by omega) (by omega)]
      exact (decide_eq_false h).symm
  have hrow := bankRepairDigitPipeRowD c lane _ _ hxl hyl hby
  rw [hbx] at hrow
  unfold bankRepairDigitFinalLaneRankOf
  generalize phiD ring S (digitSite ring root (L - R + i)) = T at hPX hPY hPo ⊢
  have hoo : ∀ i', i' < R → i' ≠ i → i' ≠ i + 1 → bankRepairDigitOutL ring root lane T (L - R) i' =
      bankRepairDigitOutL ring root lane S (L - R) i' := by
    intro i' hi1 hi2 hi3
    unfold bankRepairDigitOutL
    rw [hPo (L - R + i') (by omega) (by omega) (by omega) (by omega)]
  have ho : ∀ k', k' < n - L →
      bankRepairDigitInL ring root lane T L k' = bankRepairDigitInL ring root lane S L k' ∧
        bankRepairDigitLvL ring root lane T L k' = bankRepairDigitLvL ring root lane S L k' := by
    intro k' hk1
    unfold bankRepairDigitInL bankRepairDigitLvL
    rw [hPo (L + k') (by omega) (by omega) (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  have hr : (bankRepairDigitOutL ring root lane T (L - R) i,
      bankRepairDigitOutL ring root lane T (L - R) (i + 1)) =
      bankRepairDigitPipeStep (decide (i = 0)) (bankRepairDigitOutL ring root lane S (L - R) i)
        (bankRepairDigitOutL ring root lane S (L - R) (i + 1)) := by
    show (bankRepairDigitOutShOf
        (bankRepairDigitLaneOut lane (T (digitSite ring root (L - R + i))).top),
      bankRepairDigitOutShOf
        (bankRepairDigitLaneOut lane (T (digitSite ring root (L - R + i + 1))).top)) = _
    rw [hPX, hPY]
    exact hrow
  rw [bankRepairDigitLaneRankCongr R (n - L) (bankRepairDigitOutL ring root lane T (L - R))
    (bankRepairDigitOutL ring root lane T (L - R)) (bankRepairDigitInL ring root lane S L)
    (bankRepairDigitInL ring root lane T L) (bankRepairDigitLvL ring root lane S L)
    (bankRepairDigitLvL ring root lane T L) (fun _ _ => rfl) ho]
  have h := bankRepairDigitLanePipe R (n - L) i hi _ _ (bankRepairDigitInL ring root lane S L)
    (bankRepairDigitLvL ring root lane S L) hoo hr
  have h1 : bankRepairDigitOutL ring root lane T (L - R) i =
      (bankRepairDigitPipeStep (decide (i = 0)) (bankRepairDigitOutL ring root lane S (L - R) i)
        (bankRepairDigitOutL ring root lane S (L - R) (i + 1))).1 := congrArg Prod.fst hr
  have h2 : bankRepairDigitOutL ring root lane T (L - R) (i + 1) =
      (bankRepairDigitPipeStep (decide (i = 0)) (bankRepairDigitOutL ring root lane S (L - R) i)
        (bankRepairDigitOutL ring root lane S (L - R) (i + 1))).2 := congrArg Prod.snd hr
  rw [h1, h2] at h
  exact h

include hn hR hRL hLn hroot hbS in
theorem bankRepairDigitFinalLaneEntry (k : Nat) (hkL : k + 1 = L - R)
    (hbX : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).1.beta = (S (digitSite ring root k)).word.beta)
    (hbY : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).2.beta =
        (S (digitSite ring root (k + 1))).word.beta) :
    bankRepairDigitFinalLaneRankOf ring root R L lane (phiD ring S (digitSite ring root k)) =
      bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hPX, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S k (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot k (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (k + 1) (by omega) (by omega)
  have hby : (S (digitSite ring root (k + 1))).word.beta = true := by rw [hkL]; exact hbS
  have hrow := bankRepairDigitEntryRowD c lane _ _ hxl hyl hby
  unfold bankRepairDigitFinalLaneRankOf
  generalize phiD ring S (digitSite ring root k) = T at hPX hPY hPo ⊢
  apply bankRepairDigitLaneRankCongr
  · intro i hi
    unfold bankRepairDigitOutL
    by_cases h0 : i = 0
    · rw [h0, show L - R + 0 = k + 1 by omega, hPY, hrow]
    · rw [hPo (L - R + i) (by omega) (by omega) (by omega) (by omega)]
  · intro k' hk1
    unfold bankRepairDigitInL bankRepairDigitLvL
    rw [hPo (L + k') (by omega) (by omega) (by omega) (by omega)]
    exact ⟨rfl, rfl⟩

include hn hLn in
theorem bankRepairDigitFinalLaneFar (k : Nat) (hk : k + 1 < L - R)
    (hbX : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).1.beta = (S (digitSite ring root k)).word.beta)
    (hbY : (pairW (S (digitSite ring root k)).word
      (S (digitSite ring root (k + 1))).word).2.beta =
        (S (digitSite ring root (k + 1))).word.beta) :
    bankRepairDigitFinalLaneRankOf ring root R L lane (phiD ring S (digitSite ring root k)) =
      bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hPX, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S k (by omega) hbX hbY
  unfold bankRepairDigitFinalLaneRankOf
  generalize phiD ring S (digitSite ring root k) = T at hPX hPY hPo ⊢
  apply bankRepairDigitLaneRankCongr
  · intro i hi
    unfold bankRepairDigitOutL
    rw [hPo (L - R + i) (by omega) (by omega) (by omega) (by omega)]
  · intro k' hk1
    unfold bankRepairDigitInL bankRepairDigitLvL
    rw [hPo (L + k') (by omega) (by omega) (by omega) (by omega)]
    exact ⟨rfl, rfl⟩

end Edges

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitFinRowD
#print axioms L3.RenewalReferenceClock.bankRepairDigitDelRowD
#print axioms L3.RenewalReferenceClock.bankRepairDigitPipeRowD
#print axioms L3.RenewalReferenceClock.bankRepairDigitEntryRowD
#print axioms L3.RenewalReferenceClock.bankRepairDigitResetRowD
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLaneFin
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLaneReset
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLaneDel
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLanePipe
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLaneEntry
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLaneFar
