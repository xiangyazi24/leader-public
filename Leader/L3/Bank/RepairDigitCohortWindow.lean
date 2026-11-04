import Leader.L3.Bank.RepairDigitCohortIdentity

/-!
# T27 items 2-3: the delimiter window (M2), the crossing map (M3), no extra export (F3)

Within a cycle of the cohort class (`CohortCycIn`), the chosen slots sit at strictly decreasing
cells `cohortPos R lam i`; the delimiter edge `R - 1 → R` accepts only the packet at cell `R - 1`,
which is a chosen slot (M2, `delSlot`), and that slot crosses. The crossing exports are tracked
by a proof-only map `chi` from slot to recorded export (`CycWin`): every delimiter-edge export
recorded since the cycle start `t0` is `chi i` for a crossed slot `i`, crossed slots have their
recorded export, and crossing times increase with the slot. When the chosen grid completes,
every slot has crossed and the delimiter-edge exports of the window are exactly `chi 0, …,
chi (R - 1)` (F3, `noExtraExport`).
-/

namespace L3.CohortWindow

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity

/-! ### Chosen slots on the lane -/

section Slots

variable {R c : Nat} {s : CohortLane} {lam : Nat → Nat}

theorem posStrict (h : CohortChosen R s lam c) {a b : Nat} (hab : a < b) (hb : b < R) :
    cohortPos R lam b < cohortPos R lam a := by
  have := chosenChain h a b (Nat.le_of_lt hab) hb
  unfold cohortPos
  omega

theorem posInj (h : CohortChosen R s lam c) {a b : Nat} (ha : a < R) (hb : b < R)
    (he : cohortPos R lam a = cohortPos R lam b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := posStrict h hab hb
    omega
  · exact hab
  · have := posStrict h hab ha
    omega

theorem tailLt (h : CohortChosen R s lam c) (hnd : ¬ gridDone R R lam) : lam (R - 1) < R := by
  have hR := h.two
  apply Nat.lt_of_not_le
  intro hle
  apply hnd
  unfold gridDone
  intro i hi
  have := chosenChain h i (R - 1) (by omega) (by omega)
  omega

/-- **M2 (window)**: an occupied delimiter cell holds a chosen slot. -/
theorem delSlot (h : CohortChosen R s lam c) (hc : R ≤ c) (hnd : ¬ gridDone R R lam)
    (hocc : cohortTok R s (R - 1) ≠ .empty) :
    ∃ i, i < R ∧ cohortPos R lam i = R - 1 := by
  have hR := h.two
  have ht := tailLt h hnd
  by_cases hex : ∃ i, i < R ∧ cohortPos R lam i = R - 1
  · exact hex
  · by_cases hl : lam (R - 1) < R - 1
    · exact absurd (h.gap (R - 1) (by omega) hl (fun i hi he => hex ⟨i, hi, he⟩)) hocc
    · exact ⟨R - 1, by omega, by unfold cohortPos; omega⟩

theorem genStepCases (ke : Option Nat) (i : Nat) :
    cohortGenStep R s lam ke i = lam i ∨
      (ke = some (cohortPos R lam i) ∧ i < R ∧ lam i < R ∧
        cohortTok R s (cohortPos R lam i) ≠ .other ∧
        cohortTok R s (cohortPos R lam i + 1) = .empty ∧
        cohortGenStep R s lam ke i = lam i + 1) := by
  cases ke with
  | none => exact Or.inl rfl
  | some k =>
    have hg : cohortGenStep R s lam (some k) i = cohortGenGhost R s lam k i := rfl
    rw [hg]
    unfold cohortGenGhost
    by_cases hc : i < R ∧ lam i < R ∧ cohortPos R lam i = k ∧ cohortTok R s k ≠ .other ∧
        cohortTok R s (k + 1) = .empty
    · rw [if_pos hc]
      obtain ⟨h1, h2, hk, h3, h4⟩ := hc
      subst hk
      exact Or.inr ⟨rfl, h1, h2, h3, h4, rfl⟩
    · rw [if_neg hc]
      exact Or.inl rfl

theorem genStepGe (ke : Option Nat) (i : Nat) : lam i ≤ cohortGenStep R s lam ke i := by
  rcases genStepCases (R := R) (s := s) (lam := lam) ke i with h | ⟨-, -, -, -, -, h⟩ <;> omega

theorem genStepHop {k i : Nat} (hi : i < R) (hl : lam i < R) (hp : cohortPos R lam i = k)
    (h1 : cohortTok R s k ≠ .other) (h2 : cohortTok R s (k + 1) = .empty) :
    cohortGenStep R s lam (some k) i = lam i + 1 := by
  show cohortGenGhost R s lam k i = lam i + 1
  unfold cohortGenGhost
  exact if_pos ⟨hi, hl, hp, h1, h2⟩

theorem tokOutPkt {o : BankRepairDigitOutSh} {T : Bool} (h : cohortTokOut o = .pkt T) :
    o = .D T := by
  cases o <;> simp_all [cohortTokOut]

theorem tokInEmpty {i : BankRepairDigitInSh} {l : Bool} (h : cohortTokIn i l = .empty) :
    i = .E ∧ l = false := by
  cases l <;> cases i <;> simp_all [cohortTokIn]

theorem bottomGe (R o : Nat) : R ≤ cohortBottom R o := by
  by_cases ho : o ≤ R
  · rw [cohortBottomSettle ho]
    exact Nat.le_refl R
  · rw [cohortBottomCarry (by omega)]
    omega

end Slots

/-! ### The delimiter edge on the ring -/

section Delim

variable {c : Compiled} {n : Nat}

theorem delExportShapes (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmx : laneMarkerX lane X Y = false) (hmy : laneMarkerY lane X Y = true)
    (x : DigitExport c n)
    (hx : (digitReceiptLane lane (digitService t e d X Y gx gy)).exported = some x) :
    ∃ T, bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top) = .D T ∧
      bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top) = .E ∧
      bankRepairDigitLaneLive lane Y.top = false := by
  have h3 := (replayDel lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmx) (by rw [laneViewMarker]; exact hmy)).2.2
  rw [laneViewOutSh, laneViewInSh, laneViewLive, ← serviceLane, hx] at h3
  have h4 : delAccept (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top))
      (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top))
      (bankRepairDigitLaneLive lane Y.top) = true := by
    rw [← h3]
    rfl
  exact delAcceptTrue _ _ _ h4

/-- The export of the new frame is recorded in the stepped audit. -/
theorem recordedNew (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (lane : DigitLane) (x : DigitExport c n)
    (hx : (digitReceiptLane lane (svcAt ring S A e)).exported = some x)
    (hl : x.lane = lane) (hs : x.source = e) (ht : x.time = A.clock + 1) :
    DigitRecordedExport (digitAuditStep ring S A e) x := by
  refine ⟨DigitFrame.mk (A.clock + 1) e S A.current (svcAt ring S A e),
    List.mem_cons.mpr (Or.inl rfl), ht.symm, hs.symm, ?_⟩
  show (digitReceiptLane x.lane (svcAt ring S A e)).exported = some x
  rw [hl]
  exact hx

theorem recordedTimeLe (A : DigitAudit c n) (hfo : AuditFrameOrder A) (x : DigitExport c n)
    (h : DigitRecordedExport A x) : x.time ≤ A.clock := by
  obtain ⟨f, hf, ht, -⟩ := h
  rw [← ht]
  exact (hfo.2.1 f hf).2

/-- The delimiter edge of a letter, read on the masked lane: an export happens exactly on a
data packet into an empty carry-free delimiter input. -/
def DelFacts (ring : DirectedRing n) (lane : DigitLane) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (s : CohortLane) (R : Nat) : Prop :=
  (∀ x : DigitExport c n, (digitReceiptLane lane (svcAt ring S A e)).exported = some x →
    ∃ T, s.out (R - 1) = .D T ∧ s.inp R = .E ∧ s.live R = false) ∧
  (∀ T, s.out (R - 1) = .D T → s.inp R = .E → s.live R = false →
    ∃ x : DigitExport c n, (digitReceiptLane lane (svcAt ring S A e)).exported = some x ∧
      x.lane = lane ∧ x.source = e ∧ x.time = A.clock + 1)

theorem delEdgeFacts (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (hbX : (pairW (S (digitSite ring root (src + (R - 1)))).word
      (S (digitSite ring root (src + (R - 1) + 1))).word).1.beta =
        (S (digitSite ring root (src + (R - 1)))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + (R - 1)))).word
      (S (digitSite ring root (src + (R - 1) + 1))).word).2.beta =
        (S (digitSite ring root (src + (R - 1) + 1))).word.beta) :
    DelFacts ring lane S A (digitSite ring root (src + (R - 1)))
      (cohortProj ring root lane src R S) R := by
  have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1)) (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1) + 1) (by omega)
    (by omega)
  have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1) + 1))) = false := by
    rw [laneMarkerXBeta lane _ _ hbX]
    exact hbF (R - 1) (by omega) (by omega) (by omega)
  have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1) + 1))) = true := by
    rw [laneMarkerYBeta lane _ _ hbY, show src + (R - 1) + 1 = src + R by omega]
    exact hbR
  have hR1 : R - 1 < R := by omega
  have eo := projOut ring root lane src R S (R - 1) hR1
  have ei := projIn ring root lane src R S R (Nat.le_refl R) (by omega)
  have el := projLive ring root lane src R S R (Nat.le_refl R) (by omega)
  have hsite : digitSite ring root (src + R) = digitSite ring root (src + (R - 1) + 1) := by
    rw [show src + (R - 1) + 1 = src + R by omega]
  rw [hsite] at ei el
  constructor
  · intro x hx
    obtain ⟨T, h1, h2, h3⟩ := delExportShapes lane (A.clock + 1)
      (digitSite ring root (src + (R - 1)))
      (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1)))) (S (digitSite ring root (src + (R - 1) + 1)))
      (A.current (digitSite ring root (src + (R - 1))))
      (A.current (digitSite ring root (src + (R - 1) + 1))) hlx hly hmx hmy x hx
    exact ⟨T, by rw [eo, h1], by rw [ei, h2], by rw [el, h3]⟩
  · intro T h1 h2 h3
    rw [eo] at h1
    rw [ei] at h2
    rw [el] at h3
    obtain ⟨ex, e1, -, e3, e4, e5, -⟩ := recordDeliveryD lane (A.clock + 1)
      (digitSite ring root (src + (R - 1)))
      (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1)))) (S (digitSite ring root (src + (R - 1) + 1)))
      (A.current (digitSite ring root (src + (R - 1))))
      (A.current (digitSite ring root (src + (R - 1) + 1))) hlx hly hmy h1 h2 h3
    exact ⟨ex, e1, e4, e5, e3⟩

theorem edgeOfSome (ring : DirectedRing n) (root : Fin n) (src R j k : Nat) (hj : j < n)
    (h : cohortEdgeOf root src R (digitSite ring root j) = some k) : j = src + k := by
  unfold cohortEdgeOf at h
  rw [cohortIdxSite ring root j hj] at h
  by_cases hc : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hc] at h
    have := Option.some.inj h
    omega
  · rw [if_neg hc] at h
    cases h

end Delim

/-! ### M3: the crossing map, and the window invariant -/

section Window

variable {c : Compiled} {n : Nat}

/-- The window of a cycle started at `t0`: every delimiter-edge export recorded since `t0` is the
crossing export `chi i` of a crossed chosen slot; every crossed slot has its recorded crossing
export; crossing times increase with the slot. -/
def CycWin (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (lam : Nat → Nat) (chi : Nat → DigitExport c n) (t0 : Nat) : Prop :=
  t0 ≤ A.clock ∧
  (∀ x : DigitExport c n, DigitRecordedExport A x → OnEdge ring root lane src R x →
    t0 < x.time → ∃ i, i < R ∧ R ≤ cohortPos R lam i ∧ x = chi i) ∧
  (∀ i, i < R → R ≤ cohortPos R lam i →
    DigitRecordedExport A (chi i) ∧ OnEdge ring root lane src R (chi i) ∧ t0 < (chi i).time) ∧
  (∀ a b, a < b → b < R → R ≤ cohortPos R lam b → (chi a).time < (chi b).time)

/-- **M3 step row**: the slot at the delimiter cell takes the letter's export. -/
def chiNext (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) (lam : Nat → Nat)
    (chi : Nat → DigitExport c n) (i : Nat) : DigitExport c n :=
  if cohortPos R lam i = R - 1 ∧ e = digitSite ring root (src + (R - 1)) then
    ((digitReceiptLane lane (svcAt ring S A e)).exported).getD (chi i)
  else chi i

/-- A cycle start: nothing has crossed and nothing is recorded after the clock. -/
theorem cycWinStart (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (hfo : AuditFrameOrder A) (chi : Nat → DigitExport c n) :
    CycWin ring root lane src R A (fun _ => 0) chi A.clock := by
  refine ⟨Nat.le_refl _, fun x hx _ ht => ?_, fun i hi hc => ?_, fun a b _ hb hc => ?_⟩
  · have := recordedTimeLe A hfo x hx
    omega
  · have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · have hp : cohortPos R (fun _ => 0) b = R - 1 - b := rfl
    omega

/-- **Window step** (M2 + M3): in a cycle, every letter keeps the window, the slot at the
delimiter cell taking the letter's export when it crosses. -/
theorem cycWinStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (hfo : AuditFrameOrder A) (e : Fin n)
    (s : CohortLane) (ke : Option Nat)
    (hedge : ke = some (R - 1) → e = digitSite ring root (src + (R - 1)))
    (hkeDel : e = digitSite ring root (src + (R - 1)) → ke = some (R - 1))
    (hdel : e = digitSite ring root (src + (R - 1)) → DelFacts ring lane S A e s R)
    {jj o : Nat} {g : (Nat → Nat) × Nat} (hcyc : CohortCycIn R jj s g o)
    (chi : Nat → DigitExport c n) (t0 : Nat)
    (hw : CycWin ring root lane src R A g.1 chi t0) :
    CycWin ring root lane src R (digitAuditStep ring S A e) (cohortGenStep R s g.1 ke)
      (chiNext ring root lane src R S A e g.1 chi) t0 := by
  obtain ⟨-, hg, -, hnd⟩ := hcyc
  have hch := hg.2
  have hR := hch.two
  have hcR := bottomGe R o
  obtain ⟨hw0, hw1, hw2, hw3⟩ := hw
  -- crossed slots stay crossed and keep their export
  have K1 : ∀ i, i < R → R ≤ cohortPos R g.1 i →
      R ≤ cohortPos R (cohortGenStep R s g.1 ke) i ∧
      chiNext ring root lane src R S A e g.1 chi i = chi i := by
    intro i hi hc
    have := genStepGe (s := s) (lam := g.1) (R := R) ke i
    refine ⟨by unfold cohortPos at hc ⊢; omega, ?_⟩
    unfold chiNext
    exact if_neg (fun hh => by have := hh.1; omega)
  -- a newly crossed slot crossed at the delimiter with the letter's export
  have K2 : ∀ i, i < R → ¬ R ≤ cohortPos R g.1 i →
      R ≤ cohortPos R (cohortGenStep R s g.1 ke) i →
      cohortPos R g.1 i = R - 1 ∧
      DigitRecordedExport (digitAuditStep ring S A e) (chiNext ring root lane src R S A e g.1 chi i) ∧
      OnEdge ring root lane src R (chiNext ring root lane src R S A e g.1 chi i) ∧
      (chiNext ring root lane src R S A e g.1 chi i).time = A.clock + 1 := by
    intro i hi hc hc'
    rcases genStepCases (s := s) (lam := g.1) ke i with h | ⟨hk, -, -, ht1, ht2, h⟩
    · unfold cohortPos at hc hc'
      rw [h] at hc'
      exact absurd hc' hc
    · have hpi : cohortPos R g.1 i = R - 1 := by
        unfold cohortPos at hc hc' ⊢
        rw [h] at hc'
        omega
      rw [hpi] at hk ht1 ht2
      have he := hedge hk
      obtain ⟨hd1, hd2⟩ := hdel he
      have hD : ∃ T, s.out (R - 1) = .D T := by
        rcases hch.pkt i hi with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [hpi, cohortTokSrc _ (by omega : R - 1 < R)] at h1
          exact ⟨_, tokOutPkt h1⟩
        · rw [hpi, cohortTokSrc _ (by omega : R - 1 < R)] at h1
          exact absurd h1 (cohortTokOutNe _ _)
        · rw [hpi] at h1
          exact absurd h1 ht1
      obtain ⟨T, hT⟩ := hD
      rw [show R - 1 + 1 = R by omega, cohortTokTgt _ (Nat.le_refl R)] at ht2
      obtain ⟨hE, hL⟩ := tokInEmpty ht2
      obtain ⟨x, hx, hxl, hxs, hxt⟩ := hd2 T hT hE hL
      have hchi : chiNext ring root lane src R S A e g.1 chi i = x := by
        unfold chiNext
        rw [if_pos ⟨hpi, he⟩, hx]
        rfl
      rw [hchi]
      exact ⟨hpi, recordedNew ring S A e lane x hx hxl hxs hxt, ⟨hxl, hxs.trans he⟩, hxt⟩
  refine ⟨Nat.le_succ_of_le hw0, ?_, ?_, ?_⟩
  · intro x hx ho ht
    rcases recordedExportStepCases ring S A _ x hx with hx' | ⟨_, hs, hr⟩
    · obtain ⟨i, hi, hc, rfl⟩ := hw1 x hx' ho ht
      obtain ⟨a, b⟩ := K1 i hi hc
      exact ⟨i, hi, a, b.symm⟩
    · -- M2: the new export is the crossing of the chosen slot at the delimiter cell
      have he : e = digitSite ring root (src + (R - 1)) := hs.symm.trans ho.2
      rw [ho.1] at hr
      obtain ⟨T, h1, h2, h3⟩ := (hdel he).1 x hr
      have tk1 : cohortTok R s (R - 1) = .pkt T := by
        rw [cohortTokSrc _ (by omega : R - 1 < R), h1]
        rfl
      have tk2 : cohortTok R s (R - 1 + 1) = .empty := by
        rw [show R - 1 + 1 = R by omega, cohortTokTgt _ (Nat.le_refl R), h2, h3]
        rfl
      obtain ⟨i, hi, hpi⟩ := delSlot hch hcR hnd (by rw [tk1]; intro hh; cases hh)
      have hstep : cohortGenStep R s g.1 ke i = g.1 i + 1 := by
        rw [hkeDel he]
        exact genStepHop hi (by unfold cohortPos at hpi; omega) hpi
          (by rw [tk1]; intro hh; cases hh) tk2
      refine ⟨i, hi, ?_, ?_⟩
      · rw [cohortPos, hstep]
        unfold cohortPos at hpi
        omega
      · unfold chiNext
        rw [if_pos ⟨hpi, he⟩, hr]
        rfl
  · intro i hi hc'
    by_cases hc : R ≤ cohortPos R g.1 i
    · obtain ⟨a, b⟩ := K1 i hi hc
      obtain ⟨r1, r2, r3⟩ := hw2 i hi hc
      rw [b]
      exact ⟨recordedExportStep ring S A _ _ r1, r2, r3⟩
    · obtain ⟨-, r1, r2, r3⟩ := K2 i hi hc hc'
      exact ⟨r1, r2, by rw [r3]; omega⟩
  · intro a b hab hb hc'
    have hpab := posStrict hch hab hb
    by_cases hc : R ≤ cohortPos R g.1 b
    · obtain ⟨-, ea⟩ := K1 a (by omega) (by omega)
      obtain ⟨-, eb⟩ := K1 b hb hc
      rw [ea, eb]
      exact hw3 a b hab hb hc
    · obtain ⟨hpb, -, -, r3⟩ := K2 b hb hc hc'
      obtain ⟨-, ea⟩ := K1 a (by omega) (by omega)
      rw [ea, r3]
      have := recordedTimeLe A hfo _ (hw2 a (by omega) (by omega)).1
      omega

/-- Exports recorded in `B` no later than `A`'s clock were recorded in `A`. -/
def ExportsBack (A B : DigitAudit c n) : Prop :=
  ∀ x : DigitExport c n, DigitRecordedExport B x → x.time ≤ A.clock → DigitRecordedExport A x

theorem exportsBackStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) : ExportsBack A (digitAuditStep ring S A e) := by
  intro x hx ht
  rcases recordedExportStepCases ring S A e x hx with h | ⟨h, -, -⟩
  · exact h
  · omega

/-- **F3 (no extra export)**: once every slot of the window has crossed, every delimiter-edge
export recorded (now or later) between the first and the last crossing is a crossing export. -/
theorem noExtraExport (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (hR : 2 ≤ R) (A B : DigitAudit c n) (hfo : AuditFrameOrder A) (hAB : ExportsBack A B)
    (lam : Nat → Nat)
    (chi : Nat → DigitExport c n) (t0 : Nat) (hw : CycWin ring root lane src R A lam chi t0)
    (hdone : gridDone R R lam) (x : DigitExport c n) (hx : DigitRecordedExport B x)
    (ho : OnEdge ring root lane src R x) (h1 : (chi 0).time ≤ x.time)
    (h2 : x.time ≤ (chi (R - 1)).time) : ∃ i, i < R ∧ x = chi i := by
  obtain ⟨-, hw1, hw2, -⟩ := hw
  have hc : ∀ i, i < R → R ≤ cohortPos R lam i := by
    intro i hi
    have := hdone i hi
    unfold cohortPos
    omega
  obtain ⟨r1, -, r3⟩ := hw2 0 (by omega) (hc 0 (by omega))
  have hlast := recordedTimeLe A hfo _ (hw2 (R - 1) (by omega) (hc (R - 1) (by omega))).1
  have hxA : DigitRecordedExport A x := hAB x hx (by omega)
  obtain ⟨i, hi, -, he⟩ := hw1 x hxA ho (by omega)
  exact ⟨i, hi, he⟩

end Window

/-! ### The window on the coupled chain (BANK × audit) × cycle ghost -/

section WindowRun

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

/-- The cycle ghost of `cohortCycleNext`, read off the BANK component of the coupled state. -/
noncomputable def windowGhost
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (e : Fin n) : (Nat → Nat) × Nat :=
  cohortCycleGhost R (cohortProj ring root lane src R (piD z.1.val.1)) g
    (cohortEdgeOf root src R e)

/-- The coupled chain with the cycle ghost. -/
noncomputable def windowNext
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n) :
    (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) :=
  (bankRepairDigitBoundaryAuditNext ring hbank w.1 e,
    windowGhost ring hbank root lane src R w.1 w.2 e)

/-- The window invariant of the coupled state: layout, ordered frames, the cycle class with the
cycle ghost, and a window. -/
def WinInv (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) : Prop :=
  CohortLayout ring hbank root src R z.1 ∧ AuditFrameOrder z.2 ∧
  (∃ o, CohortCycIn R g.2 (cohortProj ring root lane src R (piD z.1.val.1)) g o) ∧
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R z.2 g.1 chi t0

include hn hR hsrc hend in
/-- **Window step on the coupled chain**: every letter keeps the window invariant; the arrival
counter stays, or advances by one with a closed window (every slot crossed). -/
theorem winInvStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WinInv ring hbank root lane src R z g) (e : Fin n) :
    WinInv ring hbank root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e)
      (windowGhost ring hbank root lane src R z g e) ∧
    ((windowGhost ring hbank root lane src R z g e).2 = g.2 ∨
      ((windowGhost ring hbank root lane src R z g e).2 = g.2 + 1 ∧
        ∃ (lam : Nat → Nat) (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
          (t0 : Nat), gridDone R R lam ∧
          CycWin ring root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e).2 lam
            chi t0)) := by
  obtain ⟨hlay, hfo, ⟨o, hcyc⟩, chi, t0, hw⟩ := h
  obtain ⟨hlay', hproj⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hlay e
  have hfo' : AuditFrameOrder (bankRepairDigitBoundaryAuditNext ring hbank z e).2 :=
    auditFrameOrderStep ring (piD z.1.val.1) z.2 e hfo
  have hcs := cohortCycStep hcyc (cohortEdgeOf root src R e)
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD z.1.val.1) z.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD z.1.val.1)) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY
  have hw' := cycWinStep ring root lane src R (piD z.1.val.1) z.2 hfo (digitSite ring root jx)
    (cohortProj ring root lane src R (piD z.1.val.1))
    (cohortEdgeOf root src R (digitSite ring root jx)) hedge hkeDel hdel hcyc chi t0 hw
  have hcyc' : ∃ o', CohortCycIn R (windowGhost ring hbank root lane src R z g
      (digitSite ring root jx)).2
      (cohortProj ring root lane src R
        (piD (bankRepairDigitBoundaryAuditNext ring hbank z (digitSite ring root jx)).1.val.1))
      (windowGhost ring hbank root lane src R z g (digitSite ring root jx)) o' := by
    show ∃ o', CohortCycIn R _ (cohortProj ring root lane src R
      (piD (bankRepairNext ring hbank z.1 (digitSite ring root jx)).val.1)) _ o'
    rw [hproj]
    rcases hcs with ⟨o', -, hin, -⟩ | hst
    · refine ⟨o', ?_⟩
      unfold windowGhost
      rw [hin.1]
      exact hin
    · refine ⟨0, ?_⟩
      unfold windowGhost
      rw [hst.1]
      exact hst
  unfold windowGhost cohortCycleGhost at hcyc' ⊢
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD z.1.val.1))
      g.1 (cohortEdgeOf root src R (digitSite ring root jx)))
  · rw [if_pos hd] at hcyc' ⊢
    refine ⟨⟨hlay', hfo', hcyc', chi, _,
      cycWinStart ring root lane src R _ hfo' chi⟩, Or.inr ⟨rfl, _, _, t0, hd, hw'⟩⟩
  · rw [if_neg hd] at hcyc' ⊢
    exact ⟨⟨hlay', hfo', hcyc', _, t0, hw'⟩, Or.inl rfl⟩

include hn hR hsrc hend in
/-- The window invariant along every coupled word. -/
theorem winInvRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInv ring hbank root lane src R w.1 w.2 →
      WinInv ring hbank root lane src R
        (word.foldl (windowNext ring hbank root lane src R) w).1
        (word.foldl (windowNext ring hbank root lane src R) w).2 := by
  induction word with
  | nil => intro w h; exact h
  | cons e rest ih =>
      intro w h
      exact ih _ (winInvStep ring hn hbank root lane src R hR hsrc hend w.1 w.2 h e).1

/-- Recorded exports only accumulate along the coupled chain. -/
theorem exportsBackRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      ExportsBack w.1.2 (word.foldl (windowNext ring hbank root lane src R) w).1.2 := by
  induction word with
  | nil => intro w x hx _; exact hx
  | cons e rest ih =>
      intro w x hx ht
      have h1 := ih (windowNext ring hbank root lane src R w e) x hx
        (by show x.time ≤ w.1.2.clock + 1; omega)
      exact exportsBackStep ring (piD w.1.1.val.1) w.1.2 e x h1 ht

include hR in
/-- The window invariant at the T24 cycle entry (cycle `0`, nothing crossed). -/
theorem winInvEntry
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (hfo : AuditFrameOrder z.2)
    (hset : CohortSettling R 0 (cohortProj ring root lane src R (piD z.1.val.1)))
    (hyng : ∀ q, q < R →
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .other ∨
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .pkt (decide (q = 0)))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) :
    WinInv ring hbank root lane src R z ((fun _ => 0), 0) :=
  ⟨hz, hfo, ⟨0, cohortCycEntry hR hset hyng⟩, chi, _, cycWinStart ring root lane src R z.2 hfo chi⟩

include hn hR hsrc hend in
/-- **F3 on the coupled chain**: when a letter completes an arrival (the counter advances), the
closed window `chi` has every slot crossed with increasing crossing times, and along every
continuation every delimiter-edge export recorded between the first crossing `chi 0` and the
last crossing `chi (R - 1)` is one of the crossing exports. With `exports j := chi (R - 1 - j)`
this is the last clause of `DigitCompletion` (`exports last = chi 0`, `exports first =
chi (R - 1)`). -/
theorem windowClosing
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : WinInv ring hbank root lane src R w.1 w.2) (e : Fin n)
    (hcl : (windowNext ring hbank root lane src R w e).2.2 = w.2.2 + 1) :
    ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
      (∀ i, i < R →
        DigitRecordedExport (windowNext ring hbank root lane src R w e).1.2 (chi i) ∧
        OnEdge ring root lane src R (chi i) ∧ t0 < (chi i).time) ∧
      (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
      ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
        DigitRecordedExport
          (word.foldl (windowNext ring hbank root lane src R)
            (windowNext ring hbank root lane src R w e)).1.2 x →
        OnEdge ring root lane src R x → (chi 0).time ≤ x.time →
        x.time ≤ (chi (R - 1)).time → ∃ i, i < R ∧ x = chi i := by
  have hfo' : AuditFrameOrder (windowNext ring hbank root lane src R w e).1.2 :=
    auditFrameOrderStep ring (piD w.1.1.val.1) w.1.2 e h.2.1
  rcases (winInvStep ring hn hbank root lane src R hR hsrc hend w.1 w.2 h e).2 with hs | hs
  · have : (windowNext ring hbank root lane src R w e).2.2 = w.2.2 := hs
    omega
  · obtain ⟨-, lam, chi, t0, hd, hw⟩ := hs
    have hc : ∀ i, i < R → R ≤ cohortPos R lam i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    refine ⟨chi, t0, fun i hi => hw.2.2.1 i hi (hc i hi),
      fun a b hab hb => hw.2.2.2 a b hab hb (hc b hb), fun word x hx ho h1 h2 => ?_⟩
    exact noExtraExport ring root lane src R hR _ _ hfo'
      (exportsBackRun ring hbank root lane src R word _) lam chi t0 hw hd x hx ho h1 h2

/-- F3 in the indexing of `DigitCompletion`: with `exports j := chi (R - 1 - j)` over `Fin r`,
`r = R`, a recorded delimiter-edge export between `exports last` and `exports first` is some
`exports j`. -/
theorem windowClause {c : Compiled} (r : Nat) (hr : r = R) (chi : Nat → DigitExport c n)
    (B : DigitAudit c n)
    (hx : ∀ x : DigitExport c n, DigitRecordedExport B x → OnEdge ring root lane src R x →
      (chi 0).time ≤ x.time → x.time ≤ (chi (R - 1)).time → ∃ i, i < R ∧ x = chi i)
    (other : DigitExport c n) (h0 : DigitRecordedExport B other) (h1 : other.lane = lane)
    (h2 : other.source = digitSite ring root (src + (r - 1)))
    (h3 : (chi (R - 1 - (r - 1))).time ≤ other.time)
    (h4 : other.time ≤ (chi (R - 1 - 0)).time) :
    ∃ j : Fin r, other = chi (R - 1 - j.val) := by
  subst hr
  rw [Nat.sub_self] at h3
  rw [Nat.sub_zero] at h4
  obtain ⟨i, hi, he⟩ := hx other h0 ⟨h1, h2⟩ h3 h4
  refine ⟨⟨r - 1 - i, by omega⟩, ?_⟩
  show other = chi (r - 1 - (r - 1 - i))
  rw [show r - 1 - (r - 1 - i) = i by omega]
  exact he

end WindowRun

end L3.CohortWindow

#print axioms L3.CohortWindow.delEdgeFacts
#print axioms L3.CohortWindow.winInvStep
#print axioms L3.CohortWindow.winInvRun
#print axioms L3.CohortWindow.winInvEntry
#print axioms L3.CohortWindow.noExtraExport
#print axioms L3.CohortWindow.windowClosing
#print axioms L3.CohortWindow.windowClause
