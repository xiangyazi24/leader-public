import Leader.L3.Top.PinnedPhaseFillCost
import Leader.L3.Top.PinnedRaceClear

/-!
# Q7 (P.12 favourable): the pending count against the accepted queue along the front clearing

While the outward front clears the window, pending packets only move and the port adds one packet
to the queue and one pending register at a time, so `|Q| - (number of pending registers)` is
constant.  This module proves the one-letter statement for windows of the front shape.

Consumer: `Leader/L3/Top/PinnedPhaseFavourable.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- One for a pending register.

Consumer: `pendCnt`. -/
def pl (c : Nat → Cell) (j : Nat) : Nat := if (c j).i.isP = true then 1 else 0

/-- The number of pending registers.

Consumer: `fs_count_step`. -/
def pendCnt (r : Nat) (c : Nat → Cell) : Nat := wsum (pl c) r

/-- The pending count only reads the first `r` registers.

Consumer: `fs_count_step`. -/
theorem pendCnt_congr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j) :
    pendCnt r c = pendCnt r c' := by
  unfold pendCnt
  apply wsum_congr
  intro k hk
  simp [pl, h k hk]

/-- Two `E/P` registers without carry keep their number of pending registers under one edge.

Consumer: `fs_pend_edge`. -/
theorem pair_ep_cnt (b : Bool) (x y : Cell) (hx : EP x) (hxc : x.c = .off) (hy : EP y)
    (hyc : y.c = .off) :
    (if (pair b false x y).1.i.isP = true then 1 else 0) +
      (if (pair b false x y).2.i.isP = true then 1 else 0) =
    (if x.i.isP = true then 1 else 0) + (if y.i.isP = true then 1 else 0) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  simp only at hxc hyc
  subst hxc hyc
  unfold EP at hx hy
  simp only at hx hy
  cases xi <;> cases yi <;> cases b <;>
    simp_all (config := { decide := true }) [EP, pair, inSlots, carries, Inp.isP, Inp.isS]

/-- **One window edge of a front window keeps the number of pending registers.**

Consumer: `fs_count_step`. -/
theorem fs_pend_edge (r p q : Nat) (cells : Nat → Cell) (hq : q + 1 < r) (h : FS r p cells) :
    pendCnt r (edgeStep r cells q) = pendCnt r cells := by
  obtain ⟨hpr, hL, hX, hR⟩ := h
  unfold edgeStep
  rw [if_pos hq]
  have hpat := pair_front_pat (decide (q = 0))
  have hident : pair (decide (q = 0)) false (cells q) (cells (q + 1)) = (cells q, cells (q + 1)) →
      pendCnt r (setTwo cells q (pair (decide (q = 0)) false (cells q) (cells (q + 1))).1
        (pair (decide (q = 0)) false (cells q) (cells (q + 1))).2) = pendCnt r cells := by
    intro hh; rw [hh, setTwo_self]
  by_cases hqp : q = p
  · subst hqp
    have hy := hR (q + 1) (by omega) hq
    have hpair : pair (decide (q = 0)) false (cells q) (cells (q + 1)) =
        ({ i := .e, c := .off }, { i := .x, c := .off }) := by
      rw [hX, hy]; exact hpat.2.1
    rw [hpair]
    simp only []
    unfold pendCnt
    have hw := wsum_edit (pl cells) (pl (setTwo cells q { i := .e, c := .off } { i := .x, c := .off }))
      q (fun k h1 h2 => by simp [pl, setTwo, h1, h2]) r (by omega)
    have e1 : pl cells q = 0 := by simp [pl, hX, Inp.isP]
    have e2 : pl cells (q + 1) = 0 := by simp [pl, hy, Inp.isP]
    have e3 : pl (setTwo cells q { i := .e, c := .off } { i := .x, c := .off }) q = 0 := by
      simp [pl, setTwo, Inp.isP]
    have e4 : pl (setTwo cells q { i := .e, c := .off } { i := .x, c := .off }) (q + 1) = 0 := by
      simp [pl, setTwo, Inp.isP]
    omega
  · by_cases hA : q + 1 < p
    · have hq1 := hL q (by omega)
      have hq2 := hL (q + 1) hA
      have hcnt := pair_ep_cnt (decide (q = 0)) (cells q) (cells (q + 1)) hq1.1 hq1.2 hq2.1 hq2.2
      unfold pendCnt
      have hw := wsum_edit (pl cells)
        (pl (setTwo cells q (pair (decide (q = 0)) false (cells q) (cells (q + 1))).1
          (pair (decide (q = 0)) false (cells q) (cells (q + 1))).2))
        q (fun k h1 h2 => by simp [pl, setTwo, h1, h2]) r (by omega)
      have e3 : pl (setTwo cells q (pair (decide (q = 0)) false (cells q) (cells (q + 1))).1
          (pair (decide (q = 0)) false (cells q) (cells (q + 1))).2) q =
          (if (pair (decide (q = 0)) false (cells q) (cells (q + 1))).1.i.isP = true then 1 else 0) := by
        simp [pl, setTwo]
      have e4 : pl (setTwo cells q (pair (decide (q = 0)) false (cells q) (cells (q + 1))).1
          (pair (decide (q = 0)) false (cells q) (cells (q + 1))).2) (q + 1) =
          (if (pair (decide (q = 0)) false (cells q) (cells (q + 1))).2.i.isP = true then 1 else 0) := by
        simp [pl, setTwo]
      have e1 : pl cells q = (if (cells q).i.isP = true then 1 else 0) := rfl
      have e2 : pl cells (q + 1) = (if (cells (q + 1)).i.isP = true then 1 else 0) := rfl
      omega
    · by_cases hB : q + 1 = p
      · have hq1 := hL q (by omega)
        have hy : cells (q + 1) = { i := .x, c := .off } := by rw [hB]; exact hX
        have hpair : pair (decide (q = 0)) false (cells q) (cells (q + 1)) =
            (cells q, cells (q + 1)) := by
          rw [hy]; exact hpat.1 (cells q) hq1.1 hq1.2
        exact hident hpair
      · have hC : p < q := by omega
        have hx := hR q hC (by omega)
        have hy := hR (q + 1) (by omega) hq
        have hq0 : decide (q = 0) = false := by simp; omega
        have hpair : pair (decide (q = 0)) false (cells q) (cells (q + 1)) =
            (cells q, cells (q + 1)) := by
          rw [hx, hy]
          exact hpat.2.2 hq0
        exact hident hpair

/-- **The terminal edge of a front window keeps the number of pending registers.**

Consumer: `fs_count_step`. -/
theorem fs_pend_term (r p : Nat) (cells : Nat → Cell) (hr : 1 ≤ r) (h : FS r p cells) :
    pendCnt r (edgeStep r cells (r - 1)) = pendCnt r cells := by
  obtain ⟨hpr, hL, hX, hR⟩ := h
  have hq : ¬ (r - 1 + 1 < r) := by omega
  unfold edgeStep
  rw [if_neg hq]
  by_cases hp : p = r - 1
  · subst hp
    have hpair := pair_term_front.1
    rw [hX, hpair]
    unfold pendCnt
    have hw := wsum_edit_one (pl cells) (pl (setOne cells (r - 1) { i := .e, c := .off }))
      (r - 1) (fun k h1 => by simp [pl, setOne, h1]) r (by omega)
    have e1 : pl cells (r - 1) = 0 := by simp [pl, hX, Inp.isP]
    have e2 : pl (setOne cells (r - 1) { i := .e, c := .off }) (r - 1) = 0 := by
      simp [pl, setOne, Inp.isP]
    omega
  · have hy := hR (r - 1) (by omega) (by omega)
    have hpair : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 = cells (r - 1) := by
      rw [hy]; exact pair_term_front.2
    rw [hpair, setOne_self]

/-- **The port letter that does not accept** leaves the window cells and the queue alone, whenever
the border register is carry-free.

Consumer: `fs_count_step`. -/
theorem port_noacc_facts {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (τ : Nat) (hc0 : (cellOf s Z 0).c = .off)
    (hnot : ¬ ((srcOf s Z (topClockSpan n - 1)).isD = true ∧ accOf s Z = true)) :
    (∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) j = cellOf s Z j) ∧
    paQ s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) τ = paQ s Z τ := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨e, he⟩ : ∃ e, e = certSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  have hy : ring.rightNeighbor e = winSite s 0 := by rw [he]; exact port_next_site ring hg.hn s
  have hxl : (Z.1.1 e).l = false := agent_l ring C s hg Z hreach _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Z hreach _
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hy, agent_beta ring C Z hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have hR : (traceReplay ring Z e).exported = none := by
    apply Classical.byContradiction
    intro hh
    apply hnot
    exact (port_acc_iff ring C s hg Z hreach).1 (by rw [← he]; exact hh)
  have hresp := siteCell_responder_terminal ring hn2 C Z e hxl hyl hyb
  rw [hy] at hresp
  have hresp' : cellOf s (topFixedTraceNext ring C Z e) 0 = portClean (cellOf s Z 0) ∨
      ∃ t, cellOf s (topFixedTraceNext ring C Z e) 0 = portAccept t (cellOf s Z 0) := hresp
  have hc0' : cellOf s (topFixedTraceNext ring C Z e) 0 = cellOf s Z 0 := by
    rcases hresp' with hc | ⟨t, hc⟩
    · rw [hc]; exact pu_port_clean _ hc0
    · by_cases hemp : cellOf s Z 0 = { i := .e, c := .off }
      · exfalso
        have hnewP : (cellOf s (topFixedTraceNext ring C Z e) 0).i.isP = true := by
          rw [hc, hemp]; cases t <;> simp [portAccept, Inp.isP]
        rw [cell_isP_iff, ← hy] at hnewP
        have hq := owner_qIn ring Z.1.1 e hxl hyl
        have hresp0 := topPortLiteralResponderFields ring hn2 C Z.1.1 e
        have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
            topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
        have hq2 : ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn =
            (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
              (Z.1.1 (ring.rightNeighbor e))).1.iY := by
          rw [hphys, hresp0.1, hq.2]
        have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
          (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
          (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
        have hiYP : (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
            (Z.1.1 (ring.rightNeighbor e))).1.iY.isP = true := by
          rw [← hq2]; exact hnewP
        rcases hjoint.2.1 hiYP with ⟨hyP, _⟩ | ⟨hb0, _⟩ | ⟨_, _, _, hacc2, _⟩
        · have : (cellOf s Z 0).i.isP = true := by rw [cell_isP_iff, ← hy]; exact hyP
          rw [hemp] at this
          simp [Inp.isP] at this
        · rw [hyb] at hb0; exact absurd hb0 (by decide)
        · have hex : (traceReplay ring Z e).exported ≠ none := hjoint.2.2.2 hacc2
          rw [hR] at hex
          exact hex rfl
      · rw [hc]; unfold portAccept; rw [if_neg hemp]
  have hdisj : ∀ j, 0 < j → j < topClockSpan n →
      winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
    intro j h0 hj
    refine ⟨?_, ?_⟩
    · intro h
      rw [he] at h
      exact win_ne_port hg.hn s j hj h
    · rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
  have hcells : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; exact hc0'
    · unfold cellOf
      exact siteCell_away ring C Z e _ (hdisj j (by omega) hj).1 (hdisj j (by omega) hj).2
  rw [he] at hcells hR
  refine ⟨hcells, ?_⟩
  unfold paQ
  rw [exportsAfter_step, hR]
  simp

/-- **The port letter that accepts a packet** makes the border register pending and adds one packet
to the queue.

Consumer: `fs_count_step`. -/
theorem port_acc_facts {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (τ : Nat) (hτ : τ ≤ Z.1.2.clock)
    (hD : (srcOf s Z (topClockSpan n - 1)).isD = true) (hacc : accOf s Z = true) :
    cellOf s Z 0 = { i := .e, c := .off } ∧
    (cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) 0).i.isP = true ∧
    (∀ j, 0 < j → j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) j = cellOf s Z j) ∧
    (paQ s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) τ).length =
      (paQ s Z τ).length + 1 := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨e, he⟩ : ∃ e, e = certSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  have hy : ring.rightNeighbor e = winSite s 0 := by rw [he]; exact port_next_site ring hg.hn s
  have hdst : ring.rightNeighbor e = certSite s (topClockSpan n) := by rw [hy]; rfl
  have hxl : (Z.1.1 e).l = false := agent_l ring C s hg Z hreach _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Z hreach _
  obtain ⟨v, t, hDq⟩ : ∃ v t, (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t := by
    unfold srcOf at hD
    rcases hq : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut with _ | _ | ⟨v, t⟩
    · rw [hq] at hD; simp [absOut, Tok.isD] at hD
    · rw [hq] at hD; simp [absOut, Tok.isD] at hD
    · exact ⟨v, t, rfl⟩
  have hexp : (traceReplay ring Z e).exported ≠ none := by
    rw [he]; exact (port_acc_iff ring C s hg Z hreach).2 ⟨hD, hacc⟩
  obtain ⟨ex, hR⟩ : ∃ ex, (traceReplay ring Z e).exported = some ex := by
    rcases hh : (traceReplay ring Z e).exported with _ | ex
    · rw [hh] at hexp; exact absurd rfl hexp
    · exact ⟨ex, rfl⟩
  have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
    (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
  have hacc2 := hjoint.2.2.1 hexp
  obtain ⟨_, hyE, hyOFF, _⟩ := qi_acc _ _ hxl hyl hacc2
  have hemp : cellOf s Z 0 = { i := .e, c := .off } := by
    have := siteCell_empty Z (ring.rightNeighbor e) hyE hyOFF
    rw [hy] at this
    exact this
  have hlink := port_accept_link ring C s Z hg hreach v t hDq hacc
  have hdisj : ∀ j, 0 < j → j < topClockSpan n →
      winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
    intro j h0 hj
    refine ⟨?_, ?_⟩
    · intro h
      rw [he] at h
      exact win_ne_port hg.hn s j hj h
    · rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ :=
    replay_exported_fields (c := compileAdvice (ceilLogTwo n)) .comparison (Z.1.2.clock + 1) e
      (ring.rightNeighbor e)
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
        (Z.1.1 (ring.rightNeighbor e)).beta)
      (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison ex hR
  have hcond : τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
      ex.destination = certSite s (topClockSpan n) :=
    ⟨by omega, by rw [hf1, he], by rw [hf2, hdst]⟩
  have hQex : topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ =
      topClockConcreteExportsAfter s Z τ ++ [ex] := by
    rw [exportsAfter_step, hR]
    simp [hcond]
  rw [← he] at hlink
  refine ⟨hemp, ?_, ?_, ?_⟩
  · rw [← he, hlink]; cases t <;> simp [Inp.isP]
  · intro j h0 hj
    rw [← he]
    unfold cellOf
    exact siteCell_away ring C Z e _ (hdisj j h0 hj).1 (hdisj j h0 hj).2
  · rw [← he]
    unfold paQ
    rw [hQex]
    simp

/-- Editing one weight below the bound, with the agreement only required below the bound.

Consumer: `fs_count_step`. -/
theorem wsum_edit_one_lt (f g : Nat → Nat) (p a : Nat) (hp : p < a)
    (h : ∀ k, k < a → k ≠ p → g k = f k) : wsum g a + f p = wsum f a + g p := by
  have key := wsum_edit_one (fun k => if k < a then f k else 0) (fun k => if k < a then g k else 0)
    p (fun k hk => by
      by_cases hka : k < a
      · simp [hka, h k hka hk]
      · simp [hka]) a (by omega)
  have e1 : wsum (fun k => if k < a then g k else 0) a = wsum g a :=
    wsum_congr _ _ a (fun k hk => by simp [hk])
  have e2 : wsum (fun k => if k < a then f k else 0) a = wsum f a :=
    wsum_congr _ _ a (fun k hk => by simp [hk])
  simp only [hp, if_true] at key
  omega

/-- The border register of a front window is carry-free.

Consumer: `fs_count_step`. -/
theorem fs_cell0_off (r p : Nat) (cells : Nat → Cell) (hr : 1 ≤ r) (h : FS r p cells) :
    (cells 0).c = .off := by
  obtain ⟨hpr, hL, hX, hR⟩ := h
  by_cases hp0 : p = 0
  · subst hp0; rw [hX]
  · exact (hL 0 (by omega)).2

/-- **One letter keeps `|Q| - (number of pending registers)` along a front window.**

Consumer: `Leader/L3/Top/PinnedPhaseFavourable.lean`. -/
theorem fs_count_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (hreach : topClockReached ring C Y)
    (τ : Nat) (hτ : τ ≤ Y.1.2.clock) (p : Nat) (hfs : FS (topClockSpan n) p (cellOf s Y))
    (e : Fin n) :
    (paQ s (topFixedTraceNext ring C Y e) τ).length + pendCnt (topClockSpan n) (cellOf s Y) =
      (paQ s Y τ).length + pendCnt (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) := by
  have hr3 := span_ge_three hg.hn
  by_cases hw : ∃ q, q < topClockSpan n ∧ e = winSite s q
  · obtain ⟨q, hq, rfl⟩ := hw
    have hQ := paQ_away ring C s Y (winSite s q) τ (win_ne_port hg.hn s q hq)
    have hag := link_window ring C s Y hg hreach q hq
    rw [hQ, pendCnt_congr _ _ _ hag]
    by_cases hq1 : q + 1 < topClockSpan n
    · rw [fs_pend_edge _ p q _ hq1 hfs]
    · have hedge : edgeStep (topClockSpan n) (cellOf s Y) q =
          edgeStep (topClockSpan n) (cellOf s Y) (topClockSpan n - 1) := by
        unfold edgeStep
        rw [if_neg hq1, if_neg (by omega)]
      rw [hedge, fs_pend_term _ p _ (by omega) hfs]
  · by_cases hb : e = certSite s (topClockSpan n - 1)
    · subst hb
      by_cases hDa : (srcOf s Y (topClockSpan n - 1)).isD = true ∧ accOf s Y = true
      · obtain ⟨hemp, hP0, haway, hQlen⟩ := port_acc_facts ring C s hg Y hreach τ hτ hDa.1 hDa.2
        rw [hQlen]
        have hcnt : pendCnt (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y
            (certSite s (topClockSpan n - 1)))) = pendCnt (topClockSpan n) (cellOf s Y) + 1 := by
          unfold pendCnt
          have hw1 := wsum_edit_one_lt (pl (cellOf s Y))
            (pl (cellOf s (topFixedTraceNext ring C Y (certSite s (topClockSpan n - 1))))) 0
            (topClockSpan n) (by omega)
            (fun k hk0 hk => by
              unfold pl
              rw [haway k (by omega) hk0])
          have e1 : pl (cellOf s Y) 0 = 0 := by simp [pl, hemp, Inp.isP]
          have e2 : pl (cellOf s (topFixedTraceNext ring C Y (certSite s (topClockSpan n - 1)))) 0 = 1 := by
            simp [pl, hP0]
          omega
        omega
      · obtain ⟨hcells, hQ⟩ := port_noacc_facts ring C s hg Y hreach τ
          (fs_cell0_off _ p _ (by omega) hfs) hDa
        rw [hQ, pendCnt_congr _ _ _ hcells]
    · have hcells := cells_frame ring C s Y hg e (fun q hq h => hw ⟨q, hq, h⟩) hb
      rw [paQ_away ring C s Y e τ hb, pendCnt_congr _ _ _ hcells]

end MarkedCells
end L3

#print axioms L3.MarkedCells.fs_count_step
