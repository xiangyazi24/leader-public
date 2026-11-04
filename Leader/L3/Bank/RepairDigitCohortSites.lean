import Leader.L3.Bank.RepairDigitCohortDomination
import Leader.L3.Bank.RepairDigitFinalSites
import Leader.L3.Bank.RepairDigitCohortTransfer

/-!
# T23 item 2: the cohort lane on the real chain

One interior complete pair: source delimiter at digit offset `src`, target delimiter at
`src + R`, next delimiter at `src + 2R`, no leader in `[src - 1, src + 2R]`. The masked lane
projection `cohortProj` reads the source outputs (cells `q < R`) and the target inputs and
carry-live bits (cells `R ≤ q < 2R`) of one lane; every other register is masked.

* `cohortProjStep`: on the projected ring, the edge at digit offset `src + k` (`k < 2R`) acts on
  the projection as `cohortEdge R · k`, and every other edge is the identity on it
  (`cohortEdgeOf` recovers `k` from the letter).
* `cohortBankStep`: the same on the BANK chain `bankRepairNext`, on the layout class
  `CohortLayout` (fixed leader, fixed `Q_W`, the three delimiter betas), which is closed.
* `cohortRealCharge`: from a BANK state whose projection is post-strict, the first arrival of the
  whole cohort at its destinations costs at most the T22 charge `32 n R`.
-/

namespace L3.CohortSites

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open K2ArbitraryElimination.FiniteAccounting

/-! ### The terminal row on projected records -/

theorem cohortTermRowD (c : Compiled) (lane : DigitLane) (x y : ProjD c)
    (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hbx : x.word.beta = false) (hby : y.word.beta = true) :
    (bankRepairDigitInShOf (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x),
      bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x) =
    cohortTermStep (bankRepairDigitInShOf (bankRepairDigitLaneIn lane x.top))
      (bankRepairDigitLaneLive lane x.top) := by
  cases lane
  · exact cohortWriterTermRow c x.lift y.lift hl hly hbx hby
  · exact cohortComparisonTermRow c x.lift y.lift hl hly hbx hby

/-! ### The masked projection -/

/-- One lane of the pair `[src, src + R)`, `[src + R, src + 2R)`, masked off the tracked
registers. -/
def cohortProj {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (S : Fin n → ProjD c) : CohortLane where
  out q := if q < R then bankRepairDigitOutL ring root lane S src q else .E
  inp q := if R ≤ q ∧ q < 2 * R then bankRepairDigitInL ring root lane S src q else .E
  live q := if R ≤ q ∧ q < 2 * R then bankRepairDigitLvL ring root lane S src q else false

theorem cohortLaneExt {s t : CohortLane} (h1 : ∀ q, s.out q = t.out q)
    (h2 : ∀ q, s.inp q = t.inp q) (h3 : ∀ q, s.live q = t.live q) : s = t := by
  cases s
  cases t
  simp only [CohortLane.mk.injEq]
  exact ⟨funext fun q => h1 q, funext fun q => h2 q, funext fun q => h3 q⟩

/-- Digit offset of a site from the root. -/
def cohortIdx {n : Nat} (root : Fin n) (e : Fin n) : Nat := (e.val + n - root.val) % n

theorem cohortIdxSite {n : Nat} (ring : DirectedRing n) (root : Fin n) (j : Nat) (hj : j < n) :
    cohortIdx root (digitSite ring root j) = j := by
  unfold cohortIdx
  rw [bankRepairDigitSiteVal]
  have hr := root.isLt
  by_cases h : root.val + j < n
  · rw [Nat.mod_eq_of_lt h, show root.val + j + n - root.val = j + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · have e : (root.val + j) % n = root.val + j - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show root.val + j - n < n by omega)]
    rw [e, show root.val + j - n + n - root.val = j by omega, Nat.mod_eq_of_lt hj]

/-- The pair edge drawn by a letter: `some k` for the site at offset `src + k`, `k < 2R`. -/
def cohortEdgeOf {n : Nat} (root : Fin n) (src R : Nat) (e : Fin n) : Option Nat :=
  if src ≤ cohortIdx root e ∧ cohortIdx root e < src + 2 * R then some (cohortIdx root e - src)
  else none

theorem cohortEdgeOfSite {n : Nat} (ring : DirectedRing n) (root : Fin n) (src R : Nat)
    (hend : src + 2 * R < n) (k : Nat) (hk : k < 2 * R) :
    cohortEdgeOf root src R (digitSite ring root (src + k)) = some k := by
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root (src + k) (by omega),
    if_pos (⟨by omega, by omega⟩ : src ≤ src + k ∧ src + k < src + 2 * R),
    Nat.add_sub_cancel_left]

/-! ### Edge classes on the projected ring -/

section Edges

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
  (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
  (hb0 : (S (digitSite ring root src)).word.beta = true)
  (hbR : (S (digitSite ring root (src + R))).word.beta = true)
  (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
  (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
    (S (digitSite ring root (src + k))).word.beta = false)
  (lane : DigitLane)

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
theorem cohortProjPipe (k : Nat) (hk : k + 1 < R)
    (hbX : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).1.beta =
        (S (digitSite ring root (src + k))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).2.beta =
        (S (digitSite ring root (src + k + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root (src + k))) =
      cohortEdge R (cohortProj ring root lane src R S) k := by
  obtain ⟨hPX, hPY, hPo⟩ :=
    bankRepairDigitLeadEdgeSites ring hn root S (src + k) (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  have hby : (S (digitSite ring root (src + k + 1))).word.beta = false :=
    hbF (k + 1) (by omega) (by omega) (by omega)
  have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = 0) := by
    by_cases h : k = 0
    · subst h
      simpa using hb0
    · rw [hbF k (by omega) (by omega) (by omega)]
      exact (decide_eq_false h).symm
  have hrow := bankRepairDigitPipeRowD c lane _ _ hxl hyl hby
  rw [hbx] at hrow
  generalize phiD ring S (digitSite ring root (src + k)) = T at hPX hPY hPo ⊢
  have hPY' : (T (digitSite ring root (src + (k + 1)))).top = _ := hPY
  have ck : k < R := by omega
  apply cohortLaneExt
  · intro q
    simp only [cohortProj, cohortEdge, if_pos hk, cohortUpd, if_pos ck]
    by_cases h1 : q = k + 1
    · rw [h1, if_pos hk, if_pos rfl]
      unfold bankRepairDigitOutL
      rw [hPY']
      exact congrArg Prod.snd hrow
    · by_cases h2 : q = k
      · rw [h2, if_pos ck, if_neg (show ¬ k = k + 1 by omega), if_pos rfl]
        unfold bankRepairDigitOutL
        rw [hPX]
        exact congrArg Prod.fst hrow
      · rw [if_neg h1, if_neg h2]
        by_cases h3 : q < R
        · rw [if_pos h3, if_pos h3]
          unfold bankRepairDigitOutL
          rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
        · rw [if_neg h3, if_neg h3]
  · intro q
    simp only [cohortProj, cohortEdge, if_pos hk]
    by_cases h : R ≤ q ∧ q < 2 * R
    · rw [if_pos h, if_pos h]
      unfold bankRepairDigitInL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]
  · intro q
    simp only [cohortProj, cohortEdge, if_pos hk]
    by_cases h : R ≤ q ∧ q < 2 * R
    · rw [if_pos h, if_pos h]
      unfold bankRepairDigitLvL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
theorem cohortProjDel (k : Nat) (hk : k + 1 = R)
    (hbX : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).1.beta =
        (S (digitSite ring root (src + k))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).2.beta =
        (S (digitSite ring root (src + k + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root (src + k))) =
      cohortEdge R (cohortProj ring root lane src R S) k := by
  obtain ⟨hPX, hPY, hPo⟩ :=
    bankRepairDigitLeadEdgeSites ring hn root S (src + k) (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  have hbx : (S (digitSite ring root (src + k))).word.beta = false :=
    hbF k (by omega) (by omega) (by omega)
  have hby : (S (digitSite ring root (src + k + 1))).word.beta = true := by
    rw [show src + k + 1 = src + R by omega]
    exact hbR
  have hrow := bankRepairDigitDelRowD c lane _ _ hxl hyl hbx hby
  generalize phiD ring S (digitSite ring root (src + k)) = T at hPX hPY hPo ⊢
  have hPY' : (T (digitSite ring root (src + (k + 1)))).top = _ := hPY
  have c1 : ¬ k + 1 < R := by omega
  have ck : k < R := by omega
  have c2 : R ≤ k + 1 ∧ k + 1 < 2 * R := by omega
  apply cohortLaneExt
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_pos hk, cohortUpd, if_pos ck, if_pos c2]
    by_cases h1 : q = k
    · rw [h1, if_pos rfl, if_pos ck]
      unfold bankRepairDigitOutL
      rw [hPX]
      exact congrArg Prod.fst hrow
    · rw [if_neg h1]
      by_cases h3 : q < R
      · rw [if_pos h3, if_pos h3]
        unfold bankRepairDigitOutL
        rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg h3, if_neg h3]
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_pos hk, cohortUpd, if_pos ck, if_pos c2]
    by_cases h1 : q = k + 1
    · rw [h1, if_pos rfl, if_pos c2]
      unfold bankRepairDigitInL
      rw [hPY']
      exact congrArg (fun p => p.2.1) hrow
    · rw [if_neg h1]
      by_cases h : R ≤ q ∧ q < 2 * R
      · rw [if_pos h, if_pos h]
        unfold bankRepairDigitInL
        rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg h, if_neg h]
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_pos hk, cohortUpd, if_pos ck, if_pos c2]
    by_cases h1 : q = k + 1
    · rw [h1, if_pos rfl, if_pos c2]
      unfold bankRepairDigitLvL
      rw [hPY']
      exact congrArg (fun p => p.2.2) hrow
    · rw [if_neg h1]
      by_cases h : R ≤ q ∧ q < 2 * R
      · rw [if_pos h, if_pos h]
        unfold bankRepairDigitLvL
        rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg h, if_neg h]

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
theorem cohortProjFin (k : Nat) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (hbX : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).1.beta =
        (S (digitSite ring root (src + k))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).2.beta =
        (S (digitSite ring root (src + k + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root (src + k))) =
      cohortEdge R (cohortProj ring root lane src R S) k := by
  obtain ⟨hPX, hPY, hPo⟩ :=
    bankRepairDigitLeadEdgeSites ring hn root S (src + k) (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  have hby : (S (digitSite ring root (src + k + 1))).word.beta = false :=
    hbF (k + 1) (by omega) (by omega) (by omega)
  have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = R) := by
    by_cases h : k = R
    · rw [h]
      simpa using hbR
    · rw [hbF k (by omega) (by omega) h]
      exact (decide_eq_false h).symm
  have hrow := bankRepairDigitFinRowD c lane _ _ hxl hyl hby
  rw [hbx] at hrow
  generalize phiD ring S (digitSite ring root (src + k)) = T at hPX hPY hPo ⊢
  have hPY' : (T (digitSite ring root (src + (k + 1)))).top = _ := hPY
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  have ck : R ≤ k ∧ k < 2 * R := by omega
  have ck1 : R ≤ k + 1 ∧ k + 1 < 2 * R := by omega
  apply cohortLaneExt
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_neg c2, if_pos hk2]
    by_cases h3 : q < R
    · rw [if_pos h3, if_pos h3]
      unfold bankRepairDigitOutL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h3, if_neg h3]
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_neg c2, if_pos hk2, cohortUpd, if_pos ck,
      if_pos ck1]
    by_cases h1 : q = k + 1
    · rw [h1, if_pos rfl, if_pos ck1]
      unfold bankRepairDigitInL
      rw [hPY']
      exact congrArg (fun p => p.2.2.1) hrow
    · by_cases h2 : q = k
      · rw [h2, if_neg (show ¬ k = k + 1 by omega), if_pos rfl, if_pos ck]
        unfold bankRepairDigitInL
        rw [hPX]
        exact congrArg Prod.fst hrow
      · rw [if_neg h1, if_neg h2]
        by_cases h : R ≤ q ∧ q < 2 * R
        · rw [if_pos h, if_pos h]
          unfold bankRepairDigitInL
          rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
        · rw [if_neg h, if_neg h]
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_neg c2, if_pos hk2, cohortUpd, if_pos ck,
      if_pos ck1]
    by_cases h1 : q = k + 1
    · rw [h1, if_pos rfl, if_pos ck1]
      unfold bankRepairDigitLvL
      rw [hPY']
      exact congrArg (fun p => p.2.2.2) hrow
    · by_cases h2 : q = k
      · rw [h2, if_neg (show ¬ k = k + 1 by omega), if_pos rfl, if_pos ck]
        unfold bankRepairDigitLvL
        rw [hPX]
        exact congrArg (fun p => p.2.1) hrow
      · rw [if_neg h1, if_neg h2]
        by_cases h : R ≤ q ∧ q < 2 * R
        · rw [if_pos h, if_pos h]
          unfold bankRepairDigitLvL
          rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
        · rw [if_neg h, if_neg h]

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
theorem cohortProjTerm (k : Nat) (hk : k + 1 = 2 * R)
    (hbX : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).1.beta =
        (S (digitSite ring root (src + k))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).2.beta =
        (S (digitSite ring root (src + k + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root (src + k))) =
      cohortEdge R (cohortProj ring root lane src R S) k := by
  obtain ⟨hPX, -, hPo⟩ :=
    bankRepairDigitLeadEdgeSites ring hn root S (src + k) (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  have hbx : (S (digitSite ring root (src + k))).word.beta = false :=
    hbF k (by omega) (by omega) (by omega)
  have hby : (S (digitSite ring root (src + k + 1))).word.beta = true := by
    rw [show src + k + 1 = src + 2 * R by omega]
    exact hb2R
  have hrow := cohortTermRowD c lane _ _ hxl hyl hbx hby
  generalize phiD ring S (digitSite ring root (src + k)) = T at hPX hPo ⊢
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  have c3 : ¬ k + 1 < 2 * R := by omega
  have ck : R ≤ k ∧ k < 2 * R := by omega
  apply cohortLaneExt
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_pos hk]
    by_cases h3 : q < R
    · rw [if_pos h3, if_pos h3]
      unfold bankRepairDigitOutL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h3, if_neg h3]
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_pos hk, cohortUpd,
      if_pos ck]
    by_cases h2 : q = k
    · rw [h2, if_pos rfl, if_pos ck]
      unfold bankRepairDigitInL
      rw [hPX]
      exact congrArg Prod.fst hrow
    · rw [if_neg h2]
      by_cases h : R ≤ q ∧ q < 2 * R
      · rw [if_pos h, if_pos h]
        unfold bankRepairDigitInL
        rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg h, if_neg h]
  · intro q
    simp only [cohortProj, cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_pos hk, cohortUpd,
      if_pos ck]
    by_cases h2 : q = k
    · rw [h2, if_pos rfl, if_pos ck]
      unfold bankRepairDigitLvL
      rw [hPX]
      exact congrArg Prod.snd hrow
    · rw [if_neg h2]
      by_cases h : R ≤ q ∧ q < 2 * R
      · rw [if_pos h, if_pos h]
        unfold bankRepairDigitLvL
        rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg h, if_neg h]

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
theorem cohortProjEntry (j : Nat) (hj : j + 1 = src)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root j)) =
      cohortProj ring root lane src R S := by
  obtain ⟨-, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S j (by omega) hbX hbY
  have hxl := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
  have hby : (S (digitSite ring root (j + 1))).word.beta = true := by
    rw [hj]
    exact hb0
  have hrow := bankRepairDigitEntryRowD c lane _ _ hxl hyl hby
  generalize phiD ring S (digitSite ring root j) = T at hPY hPo ⊢
  apply cohortLaneExt
  · intro q
    simp only [cohortProj]
    by_cases h3 : q < R
    · rw [if_pos h3, if_pos h3]
      unfold bankRepairDigitOutL
      by_cases h0 : q = 0
      · rw [h0, show src + 0 = j + 1 by omega, hPY, hrow]
      · rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h3, if_neg h3]
  · intro q
    simp only [cohortProj]
    by_cases h : R ≤ q ∧ q < 2 * R
    · rw [if_pos h, if_pos h]
      unfold bankRepairDigitInL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]
  · intro q
    simp only [cohortProj]
    by_cases h : R ≤ q ∧ q < 2 * R
    · rw [if_pos h, if_pos h]
      unfold bankRepairDigitLvL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
theorem cohortProjFar (j : Nat) (hj : j < n) (hfar : j + 1 < src ∨ src + 2 * R ≤ j)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root j)) =
      cohortProj ring root lane src R S := by
  obtain ⟨-, -, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S j hj hbX hbY
  generalize phiD ring S (digitSite ring root j) = T at hPo ⊢
  apply cohortLaneExt
  · intro q
    simp only [cohortProj]
    by_cases h3 : q < R
    · rw [if_pos h3, if_pos h3]
      unfold bankRepairDigitOutL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h3, if_neg h3]
  · intro q
    simp only [cohortProj]
    by_cases h : R ≤ q ∧ q < 2 * R
    · rw [if_pos h, if_pos h]
      unfold bankRepairDigitInL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]
  · intro q
    simp only [cohortProj]
    by_cases h : R ≤ q ∧ q < 2 * R
    · rw [if_pos h, if_pos h]
      unfold bankRepairDigitLvL
      rw [hPo (src + q) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]

include hn hR hsrc hend hroot hb0 hbR hb2R hbF in
/-- Every letter acts on the masked projection as the T22 lane step. -/
theorem cohortProjStep (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    cohortProj ring root lane src R (phiD ring S (digitSite ring root j)) =
      cohortLaneStep R (cohortProj ring root lane src R S)
        (cohortEdgeOf root src R (digitSite ring root j)) := by
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases h : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos h]
    obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    rw [Nat.add_sub_cancel_left]
    show _ = cohortEdge R _ k
    by_cases h1 : k + 1 < R
    · exact cohortProjPipe ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane k h1
        hbX hbY
    · by_cases h2 : k + 1 = R
      · exact cohortProjDel ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane k h2
          hbX hbY
      · by_cases h3 : k + 1 < 2 * R
        · exact cohortProjFin ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane k
            (by omega) h3 hbX hbY
        · exact cohortProjTerm ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane k
            (by omega) hbX hbY
  · rw [if_neg h]
    show _ = cohortProj ring root lane src R S
    by_cases h1 : j + 1 = src
    · exact cohortProjEntry ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j h1
        hbX hbY
    · exact cohortProjFar ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j hj
        (by omega) hbX hbY

end Edges

/-! ### The BANK chain -/

/-- The layout class of one interior pair: fixed leader and `Q_W`, delimiters at `src`,
`src + R`, `src + 2R`, no other delimiter in between. -/
def CohortLayout {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (src R : Nat)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairDigitLayoutFixed ring hbank root z ∧
    (piD z.val.1 (digitSite ring root src)).word.beta = true ∧
    (piD z.val.1 (digitSite ring root (src + R))).word.beta = true ∧
    (piD z.val.1 (digitSite ring root (src + 2 * R))).word.beta = true ∧
    ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (piD z.val.1 (digitSite ring root (src + k))).word.beta = false

/-- One BANK letter: the layout class is closed, and the masked projection moves by the T22
lane step of the drawn pair edge. -/
theorem cohortBankStep {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (z : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z)
    (e : Fin n) :
    CohortLayout ring hbank root src R (bankRepairNext ring hbank z e) ∧
      cohortProj ring root lane src R (piD (bankRepairNext ring hbank z e).val.1) =
        cohortLaneStep R (cohortProj ring root lane src R (piD z.val.1))
          (cohortEdgeOf root src R e) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z hL e
  have hbeta := (bankRepairDigitPhiDAt ring (by omega) (piD z.val.1) e hbX hbY).2.2.2
  refine ⟨⟨bankRepairDigitLayoutFixedStep ring hn hbank root z hL e, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [heq, hbeta]
    exact hb0
  · rw [heq, hbeta]
    exact hbR
  · rw [heq, hbeta]
    exact hb2R
  · intro k h1 h2 h3
    rw [heq, hbeta]
    exact hbF k h1 h2 h3
  · rw [heq]
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact cohortProjStep ring (by omega) root (piD z.val.1) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF lane j hj hbX hbY

/-- The whole cohort sits at its destinations (pending or settled), packet `i` at target offset
`R - 1 - i`. -/
def CohortArrived (R : Nat) (s : CohortLane) : Prop :=
  ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .pkt (cohortTail R i) ∨
    cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i)

/-- T22's charge on the BANK chain: from a layout state whose masked lane is post-strict with
ghost `lam`, the first arrival of the cohort costs at most `32 n R` (expected `16 n R`). -/
theorem cohortRealCharge {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (z : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z)
    (lam : Nat → Nat)
    (hP : CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) :
    ∀ T, 2 * costNumerator (bankRepairNext ring hbank)
        (fun z => CohortArrived R (cohortProj ring root lane src R (piD z.val.1))) z T ≤
      n ^ T * (32 * n * R) := by
  intro T
  have hsim := L3.CohortTransfer.costNumeratorGhostSimLe (bankRepairNext ring hbank)
    (fun z lam e => cohortGhost R (cohortProj ring root lane src R (piD z.val.1)) lam
      (cohortEdgeOf root src R e))
    (cohortNext R (cohortEdgeOf root src R))
    (fun w y => y = (cohortProj ring root lane src R (piD w.1.val.1), w.2) ∧
      CohortLayout ring hbank root src R w.1 ∧
      CohortPostStrict R (cohortProj ring root lane src R (piD w.1.val.1)) w.2)
    (fun z => CohortArrived R (cohortProj ring root lane src R (piD z.val.1))) (CohortDone R)
    (by
      intro z g y e h hna
      obtain ⟨hy, hz, hP⟩ := h
      obtain ⟨hz', hstep⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z hz e
      have hnd : ¬ gridDone R R g := fun hd => hna (fun i hi => cohortDonePacked hP hd hi)
      subst hy
      refine ⟨Prod.ext hstep.symm rfl, hz', ?_⟩
      rw [hstep]
      exact cohortPostStrictStep hP hnd _)
    (by
      intro z g y h hd
      obtain ⟨hy, -, hP⟩ := h
      subst hy
      exact fun i hi => cohortDonePacked hP hd hi)
    T z lam _ ⟨rfl, hz, hP⟩
  have hdom := cohortDominationCharge (n := n) (R := R) (by omega)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (cohortProj ring root lane src R (piD z.val.1), lam) (Or.inl hP) T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hsim) hdom

end L3.CohortSites

#print axioms L3.CohortSites.cohortTermRowD
#print axioms L3.CohortSites.cohortLaneExt
#print axioms L3.CohortSites.cohortIdxSite
#print axioms L3.CohortSites.cohortEdgeOfSite
#print axioms L3.CohortSites.cohortProjPipe
#print axioms L3.CohortSites.cohortProjDel
#print axioms L3.CohortSites.cohortProjFin
#print axioms L3.CohortSites.cohortProjTerm
#print axioms L3.CohortSites.cohortProjEntry
#print axioms L3.CohortSites.cohortProjFar
#print axioms L3.CohortSites.cohortProjStep
#print axioms L3.CohortSites.cohortBankStep
#print axioms L3.CohortSites.cohortRealCharge
