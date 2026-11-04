import Leader.L3.Width.DigitQuietStepScan
import Leader.L3.Width.DigitQuietRows
import Leader.L3.Bank.RepairDigitLeadingFlush
import Leader.L3.Bank.RepairDigitCloseReceipt

/-!
# The quiet class: the report clause of the one-letter law

`liveTop_report_source` (WidthDigitQuietRows) says a report is an OLD dirty endpoint or a comparison
carry at its terminal with the error bit set.  The law's report clause lists only the dirty
endpoints.  This module excludes the third case on the quiet class:

* a live comparison carry in the class has error bit `false` wherever the class describes it: the
  leading segment and the first segment have no live carry (except the inert one at the last site,
  whose right neighbour is the root), a target block of a pair carries only scanned carries
  (`pairQuiet_target_carryError`), and the fragment's only terminal edge has the root on its right;
* so no edge of the class is a terminal edge of non-root sites whose left comparison carry is live
  with the error bit set (`quiet_no_error_terminal`);
* hence `quiet_report_clause`: a report is an old dirty endpoint.

Consumer: `QuietStepLaw` (WidthDigitQuiet), report clause; assembled in
`WidthDigitQuietStepLaw` when the pair closure exists.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- The field reads of the lifted record.  Consumer: `quiet_no_error_terminal`. -/
theorem lift_l (p : ProjD c) : p.lift.l = p.word.native.l := rfl

/-- Consumer: `quiet_no_error_terminal`. -/
theorem lift_beta (p : ProjD c) : p.lift.beta = p.word.beta := rfl

/-- Consumer: `quiet_no_error_terminal`. -/
theorem lift_qCarry (p : ProjD c) : p.lift.qCarry = p.top.qCarry := rfl

/-- Consumer: `quiet_report_clause`. -/
theorem lift_topDirty (p : ProjD c) : p.lift.topDirty = p.top.topDirty := rfl

/-- The site `n` steps from the root is the root.  Consumer: `quiet_no_error_terminal`. -/
theorem digitSite_n (ring : DirectedRing n) (root : Fin n) :
    digitSite ring root n = root := by
  apply Fin.ext
  rw [RenewalReferenceClock.bankRepairDigitSiteVal, Nat.add_comm, Nat.add_mod_left, Nat.mod_eq_of_lt root.isLt]

/-- **No terminal edge of non-root sites has a live comparison carry with the error bit set on
its left, in the quiet class.**  Consumer: `quiet_report_clause`. -/
theorem quiet_no_error_terminal (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (e : Fin n) :
    ¬ ((S e).lift.l = false ∧ (S (ring.rightNeighbor e)).lift.l = false ∧
      (S e).lift.qCarry.isL = true ∧
      topTerminal (S e).lift (S (ring.rightNeighbor e)).lift = true ∧
      qcE (S e).lift.qCarry = true) := by
  have hn : 0 < n := e.pos
  rintro ⟨hxl, hyl, hq, hterm, herr⟩
  obtain ⟨k, hk, rfl⟩ := RenewalReferenceClock.bankRepairDigitSiteSurj ring root e
  rw [lift_l] at hxl hyl
  rw [lift_qCarry] at hq herr
  have hroot := hQ.rootFixed
  by_cases hk0 : k = 0
  · subst hk0
    have := (hroot (digitSite ring root 0)).mpr rfl
    rw [hxl] at this
    exact Bool.false_ne_true this
  by_cases hkn : k + 1 = n
  · have hY : ring.rightNeighbor (digitSite ring root k) = root := by
      rw [← CloseReceipt.digitSiteSucc, hkn]; exact digitSite_n ring root
    rw [hY] at hyl
    have := (hroot root).mpr rfl
    rw [hyl] at this
    exact Bool.false_ne_true this
  have hk1 : k + 1 < n := by omega
  have hY : ring.rightNeighbor (digitSite ring root k) = digitSite ring root (k + 1) :=
    (CloseReceipt.digitSiteSucc ring root k).symm
  rw [hY] at hyl hterm
  have hbeta : (S (digitSite ring root (k + 1))).word.beta = true := by
    unfold topTerminal at hterm
    rw [lift_l, lift_beta, hyl] at hterm
    simpa using hterm
  obtain ⟨hf2, hfn, hlay⟩ := hQ.layout
  obtain ⟨hge, hmod⟩ := (hlay (k + 1) (by omega) hk1).mp hbeta
  -- the live carry with its error bit, at the comparison lane view of site `k`
  have hlive : (view ring root S DigitLane.comparison k).carryLive = true := hq
  have herr' : (view ring root S DigitLane.comparison k).carryError = true := herr
  by_cases hlead : k + 1 = first
  · -- the leading segment has no live carry
    have := (hQ.leading DigitLane.comparison k (by omega) (by omega)).2.2
    rw [hlive] at this
    exact Bool.noConfusion this
  · -- k + 1 = first + (j + 1) R
    obtain ⟨q, hq'⟩ : ∃ q, k + 1 - first = digitSpan c * q :=
      ⟨(k + 1 - first) / digitSpan c, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm⟩
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, Nat.mul_zero] at hq'; omega
      · exact h0
    by_cases hq1 : q = 1
    · -- the first segment
      subst hq1
      have hseg := hQ.firstSegment DigitLane.comparison k (by omega) (by omega) (by omega)
      rcases hseg with ⟨hlast, -⟩ | ⟨hoff, -⟩
      · omega
      · rw [hlive] at hoff
        exact Bool.noConfusion hoff
    · -- the target block of the pair (q - 2, q - 1)
      have hq2 : 2 ≤ q := by omega
      obtain ⟨j, rfl⟩ : ∃ j, q = j + 2 := ⟨q - 2, by omega⟩
      have e1 : (j + 2) * digitSpan c = (j + 1) * digitSpan c + digitSpan c := by
        rw [show j + 2 = (j + 1) + 1 from rfl, Nat.succ_mul]
      have e2 : digitSpan c * (j + 2) = (j + 2) * digitSpan c := Nat.mul_comm _ _
      have hpair := hQ.pairs DigitLane.comparison j (by omega)
      have hoff : k = first + (j + 1) * digitSpan c + (digitSpan c - 1) := by omega
      have hcarry := pairQuiet_target_carryError ring root S DigitLane.comparison
        (first + j * digitSpan c) (first + (j + 1) * digitSpan c) hpair (digitSpan c - 1)
        (by omega) (by rw [← hoff]; exact hlive)
      rw [← hoff] at hcarry
      rw [hcarry] at herr'
      exact Bool.false_ne_true herr'

/-- **The report clause of the one-letter law**: on the quiet class a report clears an old dirty
endpoint.  Consumer: `QuietStepLaw` (WidthDigitQuiet), assembled in `WidthDigitQuietStepLaw`. -/
theorem quiet_report_clause (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (e : Fin n)
    (h : (topD (S e) (S (ring.rightNeighbor e))).topReject = true) :
    (S e).top.topDirty = true ∨ (S (ring.rightNeighbor e)).top.topDirty = true := by
  have hrep := liveTop_report_source c (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta h
  rcases hrep with h1 | h1 | ⟨hl1, hl2, hq, ht, he⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd ⟨hl1, hl2, hq, ht, he⟩ (quiet_no_error_terminal hR ring root first S hQ e)

end L3.DigitQuiet

#print axioms L3.DigitQuiet.quiet_no_error_terminal
#print axioms L3.DigitQuiet.quiet_report_clause
