import Leader.L3.Bank.RepairDigitCohortClose

/-!
# T28 item 2: the carry-ledger invariant on the target cells

`LedgerOk` on one lane of the pair `[src, src + R)`, `[src + R, src + 2R)`: every carry ledger on
a target cell `src + q` (`R ≤ q < 2R`) and the ledger of every recorded terminal receipt on the
terminal edge `src + 2R - 1 → src + 2R` is either *inherited* (`inherited ≠ none`: present at the
audit start, or a missing ledger) or *fresh*: `inherited = none`, exactly `q + 1 - R` uses
(`R` for a terminal), the `j`-th use aimed at the target cell `src + R + j`, use times strictly
increasing and before the clock (before the terminal's time for a terminal).

Every letter of the audit preserves it (`ledgerOkStep`); it holds at the audit start
(`ledgerOkInitial`) and along every coupled BANK × audit word in the layout class
(`ledgerOkRun`, `ledgerOkFromStart`).
-/

namespace L3.CohortLedger

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence

section Replay

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source destination : Fin n)
  (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- Left ledger of the replay: retired, kept, or launched at a marker with one use stamped now
at the source. -/
theorem replayCarryX (hlx : x.leader = false) (hly : y.leader = false) :
    (digitLaneReplay lane time source destination x y gx gy).x.carry = none ∨
    (digitLaneReplay lane time source destination x y gx gy).x.carry = gx.carry ∨
    (x.marker = true ∧ ∃ u : DigitUse c n, u.time = time ∧ u.target = source ∧
      (digitLaneReplay lane time source destination x y gx gy).x.carry =
        some (DigitCarryGhost.mk none [u])) := by
  cases hxc : x.carryLive <;> cases hxm : x.marker <;>
    simp [digitLaneReplay, hlx, hly, hxc, hxm] <;> (repeat' split) <;> simp_all

/-- Right ledger of the replay off a marker: kept, or the left ledger (or a missing one) with one
use appended, stamped now at the destination. -/
theorem replayCarryY (hlx : x.leader = false) (hly : y.leader = false) (hmy : y.marker = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry ∨
    ∃ u : DigitUse c n, u.time = time ∧ u.target = destination ∧
      (digitLaneReplay lane time source destination x y gx gy).y.carry =
        some (DigitCarryGhost.mk
          (gx.carry.getD (DigitCarryGhost.mk
            (some (.missing (DigitStamp.mk time source lane) .carry)) [])).inherited
          ((gx.carry.getD (DigitCarryGhost.mk
            (some (.missing (DigitStamp.mk time source lane) .carry)) [])).uses ++ [u])) := by
  cases hxc : x.carryLive <;>
    simp [digitLaneReplay, hlx, hly, hmy, hxc] <;> (repeat' split) <;> simp_all

/-- A terminal receipt records the left ledger, stamped now at the source. -/
theorem replayTerminal (t : DigitTerminal c n)
    (h : (digitLaneReplay lane time source destination x y gx gy).terminal = some t) :
    t.ledger = gx.carry ∧ t.time = time ∧ t.source = source := by
  simp only [digitLaneReplay] at h
  split at h
  · injection h with h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

end Replay

/-! ### Fresh ledgers -/

section Fresh

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n) (src R : Nat)

/-- Uses aimed at the target cells in order, with strictly increasing times before `t`. -/
def UsesOk (t : Nat) (us : List (DigitUse c n)) : Prop :=
  ∀ j (u : DigitUse c n), us[j]? = some u →
    u.target = digitSite ring root (src + R + j) ∧ u.time < t ∧
    ∀ j' (u' : DigitUse c n), j' < j → us[j']? = some u' → u'.time < u.time

/-- A ledger reaching target offset `q`: inherited, or fresh with the uses of cells
`R, …, q`. -/
def FreshOk (t q : Nat) (L : DigitCarryGhost c n) : Prop :=
  L.inherited ≠ none ∨
    (L.inherited = none ∧ L.uses.length = q + 1 - R ∧ UsesOk ring root src R t L.uses)

theorem usesOkMono {t t' : Nat} (h : t ≤ t') {us : List (DigitUse c n)}
    (hu : UsesOk ring root src R t us) : UsesOk ring root src R t' us := by
  intro j u hj
  obtain ⟨a, b, d⟩ := hu j u hj
  exact ⟨a, by omega, d⟩

theorem freshOkMono {t t' q : Nat} (h : t ≤ t') {L : DigitCarryGhost c n}
    (hL : FreshOk ring root src R t q L) : FreshOk ring root src R t' q L := by
  rcases hL with hL | ⟨a, b, d⟩
  · exact Or.inl hL
  · exact Or.inr ⟨a, b, usesOkMono ring root src R h d⟩

theorem singletonGet {u w : DigitUse c n} {k : Nat} (h : [u][k]? = some w) : k = 0 ∧ w = u := by
  cases k with
  | zero =>
    simp at h
    exact ⟨rfl, h.symm⟩
  | succ k => simp at h

theorem usesOkAppend {t : Nat} {us : List (DigitUse c n)} (hu : UsesOk ring root src R t us)
    (u : DigitUse c n) (ht : u.time = t)
    (hg : u.target = digitSite ring root (src + R + us.length)) :
    UsesOk ring root src R (t + 1) (us ++ [u]) := by
  intro j w hw
  by_cases hj : j < us.length
  · rw [List.getElem?_append_left hj] at hw
    obtain ⟨a, b, d⟩ := hu j w hw
    refine ⟨a, by omega, fun j' u' hj' hu' => ?_⟩
    rw [List.getElem?_append_left (by omega)] at hu'
    exact d j' u' hj' hu'
  · rw [List.getElem?_append_right (by omega)] at hw
    obtain ⟨h0, rfl⟩ := singletonGet hw
    have hjl : j = us.length := by omega
    refine ⟨by rw [hg, hjl], by omega, fun j' u' hj' hu' => ?_⟩
    rw [List.getElem?_append_left (by omega)] at hu'
    have := (hu j' u' hu').2.1
    omega

theorem usesOkSingle {t : Nat} (u : DigitUse c n) (ht : u.time = t)
    (hg : u.target = digitSite ring root (src + R)) : UsesOk ring root src R (t + 1) [u] := by
  intro j w hw
  obtain ⟨h0, rfl⟩ := singletonGet hw
  subst h0
  refine ⟨by rw [hg]; rfl, by omega, fun j' u' hj' _ => absurd hj' (Nat.not_lt_zero _)⟩

end Fresh

/-! ### The ledger invariant on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- **The carry-ledger invariant** of one lane of the pair. -/
def LedgerOk (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → ∀ L : DigitCarryGhost c n,
    (laneCells ring root lane src A.current q).carry = some L →
    FreshOk ring root src R (A.clock + 1) q L) ∧
  (∀ T : DigitTerminal c n, DigitRecordedTerminal A T → T.lane = lane →
    T.source = digitSite ring root (src + (2 * R - 1)) → ∀ L : DigitCarryGhost c n,
    T.ledger = some L → FreshOk ring root src R T.time (2 * R - 1) L)

theorem cellFar (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (lane : DigitLane) (src j q : Nat) (hj : j < n) (hq : src + q < n)
    (hs : 1 ≤ src) (n1 : src + q ≠ j) (n2 : src + q ≠ j + 1) :
    laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
      laneCells ring root lane src A.current q := by
  unfold laneCells
  rw [curFar]
  · intro he
    exact n1 (bankRepairDigitSiteInj ring root hq hj he)
  · intro he
    rw [← bankRepairDigitSiteSucc] at he
    by_cases hjn : j + 1 < n
    · exact n2 (bankRepairDigitSiteInj ring root hq hjn he)
    · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
      have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) hq (by omega) he
      omega

theorem cellX (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (lane : DigitLane) (src k : Nat) :
    laneCells ring root lane src
      (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
    (digitLaneReplay lane (A.clock + 1) (digitSite ring root (src + k))
      (digitSite ring root (src + k + 1))
      (digitLaneView lane (S (digitSite ring root (src + k)))
        (laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1)))))
      (digitLaneView lane (S (digitSite ring root (src + k + 1)))
        (laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1)))))
      (laneCells ring root lane src A.current k)
      (laneCells ring root lane src A.current (k + 1))).x := by
  unfold laneCells
  rw [curX]
  unfold svcAt
  rw [serviceLaneX, serviceLane]
  rfl

theorem cellY (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (lane : DigitLane) (src k : Nat) :
    laneCells ring root lane src
      (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
    (digitLaneReplay lane (A.clock + 1) (digitSite ring root (src + k))
      (digitSite ring root (src + k + 1))
      (digitLaneView lane (S (digitSite ring root (src + k)))
        (laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1)))))
      (digitLaneView lane (S (digitSite ring root (src + k + 1)))
        (laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1)))))
      (laneCells ring root lane src A.current k)
      (laneCells ring root lane src A.current (k + 1))).y := by
  unfold laneCells
  rw [show digitSite ring root (src + (k + 1)) =
    ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
  unfold svcAt
  rw [serviceLaneY, serviceLane]
  rfl

/-- **Every letter preserves the carry-ledger invariant** (layout hypotheses of
`cohortProjStep`). -/
theorem ledgerOkStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (_hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (h : LedgerOk ring root lane src R A) :
    LedgerOk ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨hC, hT⟩ := h
  have hclk : (digitAuditStep ring S A (digitSite ring root j)).clock = A.clock + 1 := rfl
  refine ⟨?_, ?_⟩
  · intro q hq1 hq2 L hL
    rw [hclk]
    have far : src + q ≠ j → src + q ≠ j + 1 →
        FreshOk ring root src R (A.clock + 1 + 1) q L := by
      intro n1 n2
      rw [cellFar ring root S A lane src j q hj (by omega) (by omega) n1 n2] at hL
      exact freshOkMono ring root src R (by omega) (hC q hq1 hq2 L hL)
    by_cases hin : src ≤ j ∧ j < src + 2 * R
    · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
      have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
      have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega)
        (by omega)
      have vlx : (digitLaneView lane (S (digitSite ring root (src + k)))
          (laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).leader = false := by
        rw [laneViewLeader]; exact hlx
      have vly : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
          (laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).leader = false := by
        rw [laneViewLeader]; exact hly
      have vmx : (digitLaneView lane (S (digitSite ring root (src + k)))
          (laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).marker =
            (S (digitSite ring root (src + k))).word.beta := by
        rw [laneViewMarker, laneMarkerXBeta lane _ _ hbX]
      have vmy : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
          (laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).marker =
            (S (digitSite ring root (src + k + 1))).word.beta := by
        rw [laneViewMarker, laneMarkerYBeta lane _ _ hbY]
      by_cases hqk : q = k
      · subst hqk
        rw [cellX] at hL
        rcases replayCarryX lane _ _ _ _ _ _ _ vlx vly with h1 | h1 | ⟨hm, u, hu1, hu2, h1⟩
        · rw [h1] at hL
          cases hL
        · rw [h1] at hL
          exact freshOkMono ring root src R (by omega) (hC q hq1 hq2 L hL)
        · rw [h1] at hL
          injection hL with hL
          subst hL
          have hqR : q = R := by
            rw [vmx] at hm
            by_cases hqR : q = R
            · exact hqR
            · rw [hbF q (by omega) (by omega) hqR] at hm
              cases hm
          subst hqR
          refine Or.inr ⟨rfl, by simp, usesOkSingle ring root src q u hu1 ?_⟩
          rw [hu2]
      · by_cases hqk1 : q = k + 1
        · subst hqk1
          rw [cellY ring hn] at hL
          by_cases hkR : k + 1 = R
          · -- Del: the delimiter's ledger is untouched
            have hmx' : (digitLaneView lane (S (digitSite ring root (src + k)))
                (laneMarkerX lane (S (digitSite ring root (src + k)))
                  (S (digitSite ring root (src + k + 1))))).marker = false := by
              rw [vmx]; exact hbF k (by omega) (by omega) (by omega)
            have hmy' : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
                (laneMarkerY lane (S (digitSite ring root (src + k)))
                  (S (digitSite ring root (src + k + 1))))).marker = true := by
              rw [vmy, show src + k + 1 = src + R by omega]; exact hbR
            rw [(replayDel lane _ _ _ _ _ _ _ vlx vly hmx' hmy').2.1] at hL
            exact freshOkMono ring root src R (by omega) (hC (k + 1) hq1 hq2 L hL)
          · have hmy' : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
                (laneMarkerY lane (S (digitSite ring root (src + k)))
                  (S (digitSite ring root (src + k + 1))))).marker = false := by
              rw [vmy]; exact hbF (k + 1) (by omega) (by omega) hkR
            have hkR' : R ≤ k := by omega
            rcases replayCarryY lane _ _ _ _ _ _ _ vlx vly hmy' with h1 | ⟨u, hu1, hu2, h1⟩
            · rw [h1] at hL
              exact freshOkMono ring root src R (by omega) (hC (k + 1) hq1 hq2 L hL)
            · rw [h1] at hL
              injection hL with hL
              subst hL
              cases hgx : (laneCells ring root lane src A.current k).carry with
              | none =>
                left
                simp
              | some L0 =>
                simp only [Option.getD_some]
                rcases hC k hkR' (by omega) L0 hgx with h0 | ⟨a, b, d⟩
                · exact Or.inl h0
                · refine Or.inr ⟨a, by simp [b]; omega, ?_⟩
                  apply usesOkAppend ring root src R d u hu1
                  rw [hu2, b, show src + R + (k + 1 - R) = src + k + 1 by omega]
        · by_cases hk1 : src + q = src + k + 1
          · omega
          · exact far (by omega) (by omega)
    · exact far (by omega) (by omega)
  · intro T hTr hTl hTs L hL
    obtain ⟨f, hf, h1, h2, h3⟩ := hTr
    rcases auditFrameMemStepCases ring S A _ f hf with hf' | hf'
    · exact hT T ⟨f, hf', h1, h2, h3⟩ hTl hTs L hL
    · subst hf'
      have hje : j = src + (2 * R - 1) :=
        bankRepairDigitSiteInj ring root hj (by omega) (h2.trans hTs)
      subst hje
      rw [hTl] at h3
      have h3' : (digitReceiptLane lane (svcAt ring S A
          (digitSite ring root (src + (2 * R - 1))))).terminal = some T := h3
      unfold svcAt at h3'
      rw [serviceLane] at h3'
      obtain ⟨e1, e2, -⟩ := replayTerminal lane _ _ _ _ _ _ _ T h3'
      rw [e2]
      rw [hL] at e1
      exact hC (2 * R - 1) (by omega) (by omega) L e1.symm

/-- The invariant at the audit start: every ledger is inherited and nothing is recorded. -/
theorem ledgerOkInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) : LedgerOk ring root lane src R (digitAuditInitial S) := by
  refine ⟨fun q _ _ L hL => ?_, fun T hT => ?_⟩
  · left
    have hL' : (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).carry =
        some L := hL
    rw [laneGhostInitial] at hL'
    unfold DigitLaneGhost.initial at hL'
    by_cases hc : (digitLaneView lane (S (digitSite ring root (src + q)))
        (S (digitSite ring root (src + q))).word.beta).carryLive = true
    · rw [if_pos hc] at hL'
      injection hL' with hL'
      subst hL'
      intro hh
      cases hh
    · rw [if_neg hc] at hL'
      cases hL'
  · obtain ⟨f, hf, -⟩ := hT
    exact absurd hf (List.not_mem_nil)

end Ring

/-! ### Along the coupled run -/

section Run

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
theorem ledgerOkBankStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : LedgerOk ring root lane src R z.2) (e : Fin n) :
    CohortLayout ring hbank root src R (bankRepairDigitBoundaryAuditNext ring hbank z e).1 ∧
    LedgerOk ring root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e).2 := by
  refine ⟨(cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hz e).1, ?_⟩
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  show LedgerOk ring root lane src R (digitAuditStep ring (piD z.1.val.1) z.2 e)
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact ledgerOkStep ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hb0
    hbR hb2R hbF lane z.2 j hj hbX hbY hc

include hn hR hsrc hend in
/-- **Ledger run**: along every coupled word the layout and the carry-ledger invariant persist. -/
theorem ledgerOkRun (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      CohortLayout ring hbank root src R z.1 → LedgerOk ring root lane src R z.2 →
      CohortLayout ring hbank root src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1 ∧
      LedgerOk ring root lane src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).2 := by
  induction word with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons e rest ih =>
      intro z h1 h2
      obtain ⟨a, b⟩ := ledgerOkBankStep ring hn hbank root lane src R hR hsrc hend z h1 h2 e
      exact ih _ a b

include hn hR hsrc hend in
/-- The carry-ledger invariant along every coupled word from the audit start. -/
theorem ledgerOkFromStart (z : BankReferenceState ring hbank)
    (hz : CohortLayout ring hbank root src R z) (word : List (Fin n)) :
    LedgerOk ring root lane src R
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (z, digitAuditInitial (piD z.val.1))).2 :=
  (ledgerOkRun ring hn hbank root lane src R hR hsrc hend word _ hz
    (ledgerOkInitial ring root lane src R _)).2

end Run

end L3.CohortLedger

#print axioms L3.CohortLedger.ledgerOkStep
#print axioms L3.CohortLedger.ledgerOkRun
#print axioms L3.CohortLedger.ledgerOkFromStart
