import Leader.L3.Top.PinnedPhaseSweepStep
import Leader.L3.Top.PinnedCarryTrace

/-!
# Q7 (P.12 preparation, lemma 2): the ledger invariant of the carry sweep

`SweepDyn` says that the host stands at register `k`, holds the ledger of `k + 1` uses (one per
register `0..k`, with the atom, value and tail of the register as recorded at the launch), and that
the registers behind the host still hold the settled non-tail input and ghost atom they had at the
launch.

Consumer: `Leader/L3/Top/PinnedPhaseCertificate.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The register `j` still holds the settled input and the ghost atom of the sample `sam j`.

Consumer: `SweepDyn`. -/
def RegData {n : Nat} (s : Fin n) (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (Y : TopFixedTraceState n) (j : Nat) : Prop :=
  (Y.1.1 (winSite s j)).qIn = .S (sam j).value (sam j).tail ∧
  (Y.1.1 (winSite s j)).qCarry = .OFF ∧
  (Y.1.2.current (winSite s j)).comparison.input = some (.sampled (sam j).id)

/-- A register away from the edge keeps its data.

Consumer: `sweep_keep`, `sweep_adv`. -/
theorem regdata_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n) (Y : TopFixedTraceState n)
    (j : Nat) (e : Fin n) (hx : winSite s j ≠ e) (hy : winSite s j ≠ ring.rightNeighbor e)
    (h : RegData s sam Y j) : RegData s sam (topFixedTraceNext ring C Y e) j := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨a, b, c⟩ := step_away ring C Y e _ hx hy
  exact ⟨a.trans h1, b.trans h2, c.trans h3⟩

/-- A settled non-tail register keeps its data on its own edge.

Consumer: `sweep_keep`. -/
theorem regdata_src {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (hreach : topClockReached ring C Y)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n) (j : Nat) (hj0 : 1 ≤ j)
    (hjr : j < topClockSpan n) (htail : (sam j).tail = false) (h : RegData s sam Y j) :
    RegData s sam (topFixedTraceNext ring C Y (winSite s j)) j := by
  obtain ⟨h1, h2, h3⟩ := h
  have hxl := agent_l ring C s hg Y hreach (winSite s j)
  have hyl := agent_l ring C s hg Y hreach (ring.rightNeighbor (winSite s j))
  have hxb : (Y.1.1 (winSite s j)).beta = false := by
    rw [agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad j hjr]
    simp; omega
  rw [htail] at h1
  obtain ⟨a, b, c⟩ := step_settled_x ring C Y (winSite s j) hxl hyl _ h1 h2 hxb
  refine ⟨?_, b, c.trans h3⟩
  rw [htail]
  exact a

/-- A settled non-tail register behind a settled non-tail register keeps its data.

Consumer: `sweep_keep`. -/
theorem regdata_resp {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (hreach : topClockReached ring C Y)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n) (j : Nat) (hj0 : 1 ≤ j)
    (hjr : j + 1 < topClockSpan n) (htail : (sam j).tail = false)
    (htail' : (sam (j + 1)).tail = false) (h : RegData s sam Y j) (h' : RegData s sam Y (j + 1)) :
    RegData s sam (topFixedTraceNext ring C Y (winSite s j)) (j + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have hxl := agent_l ring C s hg Y hreach (winSite s j)
  have hyl := agent_l ring C s hg Y hreach (ring.rightNeighbor (winSite s j))
  have hxb : (Y.1.1 (winSite s j)).beta = false := by
    rw [agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad j (by omega)]
    simp; omega
  have hnext : ring.rightNeighbor (winSite s j) = winSite s (j + 1) := winSite_next ring s j
  have hyb : (Y.1.1 (ring.rightNeighbor (winSite s j))).beta = false := by
    rw [hnext, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad (j + 1) hjr]
    simp
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  rw [htail] at h1
  rw [htail'] at h1'
  obtain ⟨a, b, c⟩ := step_settled_y ring hn2 C Y (winSite s j) hxl hyl _ _ h1 h2 hxb
    (by rw [hnext]; exact h1') (by rw [hnext]; exact h2') hyb
  rw [hnext] at a b c
  refine ⟨?_, b, c.trans h3'⟩
  rw [htail']
  exact a

/-- The host cell means a live physical carry.

Consumer: `sweep_adv`. -/
theorem host_isL {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (k : Nat)
    (h : cellOf s Y k = { i := .e, c := .fresh }) : (Y.1.1 (winSite s k)).qCarry.isL = true := by
  have h2 := congrArg Cell.c h
  unfold cellOf siteCell at h2
  simp only at h2
  rcases hq : (Y.1.1 (winSite s k)).qCarry with _ | ⟨a, b⟩
  · rw [hq] at h2; simp [absCar] at h2
  · rfl

/-- **The ledger of the host at register `k`**: one use per register `0..k`, in order.

Consumer: `SweepDyn`. -/
def SweepLedger {n : Nat} (s : Fin n) (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (Yl Y : TopFixedTraceState n) (k : Nat) : Prop :=
  ∃ U : List (DigitUse (compileAdvice (ceilLogTwo n)) n),
    (Y.1.2.current (winSite s k)).comparison.carry = some { inherited := none, uses := U } ∧
    U.length = k + 1 ∧
    (∀ j, j < k + 1 → ∃ u, U[j]? = some u ∧ u.target = winSite s j ∧
      u.operand = some (.sampled (sam j).id) ∧ u.value = (sam j).value ∧
      u.tail = (sam j).tail) ∧
    (∀ a ∈ U, Yl.1.2.clock < a.time ∧ a.time ≤ Y.1.2.clock) ∧
    U.Pairwise (fun a b => a.time < b.time)

/-- **The sweep invariant**: the host at register `k` with its ledger, the registers behind it
untouched.

Consumer: `sweep_adv`, `sweep_keep`. -/
def SweepDyn {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Yl : TopFixedTraceState n) (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) (Y : TopFixedTraceState n) : Prop :=
  topClockReached ring C Yl ∧ MarkedFrom ring C Yl Y ∧
    CarryShape (topClockSpan n) k (cellOf s Y) ∧ SweepLedger s sam Yl Y k ∧
    (∀ j, k < j → j < topClockSpan n → RegData s sam Y j)

/-- The clock after one letter.

Consumer: `sweep_adv`, `sweep_keep`. -/
theorem next_clock {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Y : TopFixedTraceState n) (e : Fin n) :
    (topFixedTraceNext ring C Y e).1.2.clock = Y.1.2.clock + 1 := by
  simp [topFixedTraceNext, digitAuditStep]

/-- **The host advances on its own edge**: the invariant holds one register further.

Consumer: `aligned_strict_cost`. -/
theorem sweep_adv {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Yl Y : TopFixedTraceState n)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n) (k : Nat)
    (htails : ∀ j, 1 ≤ j → j < topClockSpan n → (sam j).tail = false)
    (hD : SweepDyn ring C s Yl sam k Y) (hk1 : k + 1 < topClockSpan n) :
    SweepDyn ring C s Yl sam (k + 1) (topFixedTraceNext ring C Y (winSite s k)) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  obtain ⟨hYl, hfrom, hshape, ⟨U, hcarry, hlen, hU, hUt, hpw⟩, hreg⟩ := hD
  have hreach : topClockReached ring C Y := markedFrom_reached ring C Yl Y hfrom
  have hclock : Yl.1.2.clock ≤ Y.1.2.clock := markedFrom_clock ring C Yl Y hYl hfrom
  have hy := hreg (k + 1) (by omega) hk1
  have hnext : ring.rightNeighbor (winSite s k) = winSite s (k + 1) := winSite_next ring s k
  have hne : ring.rightNeighbor (winSite s k) ≠ winSite s k := rightNeighbor_ne ring hn2 _
  have hxl := agent_l ring C s hg Y hreach (winSite s k)
  have hyl := agent_l ring C s hg Y hreach (ring.rightNeighbor (winSite s k))
  have hyb : (Y.1.1 (ring.rightNeighbor (winSite s k))).beta = false := by
    rw [hnext, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad (k + 1) hk1]
    simp
  have hxk := host_isL s Y k hshape.2.2.1
  have hyk : (Y.1.1 (ring.rightNeighbor (winSite s k))).qCarry = .OFF := by
    rw [hnext]; exact hy.2.1
  have hys : (Y.1.1 (ring.rightNeighbor (winSite s k))).qIn.isS = true := by
    rw [hnext, hy.1]; rfl
  obtain ⟨u, hc1, hc2, ht, htg, hop, hval, htl⟩ := trace_advance_full ring C Y (winSite s k) hne
    hxl hyl hyb hxk hyk hys { inherited := none, uses := U } hcarry
  rw [hnext] at hc2 htg hop hval htl
  refine ⟨hYl, markedFrom_next ring C Yl Y _ hfrom, ?_, ?_, ?_⟩
  · exact (carry_next_carry ring C s hg Y hreach k hshape (winSite s k)).1 rfl hk1
  · refine ⟨U ++ [u], hc2, by simp [hlen], ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j < k + 1
      · obtain ⟨u', hu1, hu2, hu3, hu4, hu5⟩ := hU j hjk
        refine ⟨u', ?_, hu2, hu3, hu4, hu5⟩
        rw [List.getElem?_append_left (by omega)]
        exact hu1
      · have hj' : j = k + 1 := by omega
        subst hj'
        refine ⟨u, ?_, htg, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        · rw [hop]; exact hy.2.2
        · rw [hval, hy.1]; rfl
        · rw [htl, hy.1]; rfl
    · intro a ha
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · have := hUt a ha
        rw [next_clock]
        omega
      · rw [List.mem_singleton] at ha
        subst ha
        rw [next_clock, ht]
        omega
    · rw [List.pairwise_append]
      refine ⟨hpw, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      rw [ht]
      have := hUt a ha
      omega
  · intro j hj1 hj2
    have h1 : winSite s j ≠ winSite s k := fun h =>
      absurd (winSite_inj hg.hn s j k (by omega) (by omega) h) (by omega)
    have h2 : winSite s j ≠ ring.rightNeighbor (winSite s k) := by
      rw [hnext]
      intro h
      exact absurd (winSite_inj hg.hn s j (k + 1) (by omega) (by omega) h) (by omega)
    exact regdata_away ring C s sam Y j (winSite s k) h1 h2 (hreg j (by omega) hj2)

/-- **A letter off the host's edge keeps the invariant at the same register.**

Consumer: `aligned_strict_cost`. -/
theorem sweep_keep {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Yl Y : TopFixedTraceState n)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n) (k : Nat)
    (htails : ∀ j, 1 ≤ j → j < topClockSpan n → (sam j).tail = false)
    (hD : SweepDyn ring C s Yl sam k Y) (e : Fin n) (hne : e ≠ winSite s k) :
    SweepDyn ring C s Yl sam k (topFixedTraceNext ring C Y e) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨hYl, hfrom, hshape, ⟨U, hcarry, hlen, hU, hUt, hpw⟩, hreg⟩ := hD
  have hreach : topClockReached ring C Y := markedFrom_reached ring C Yl Y hfrom
  have hne' : ring.rightNeighbor e ≠ e := rightNeighbor_ne ring hn2 e
  have hxl := agent_l ring C s hg Y hreach e
  have hyl := agent_l ring C s hg Y hreach (ring.rightNeighbor e)
  refine ⟨hYl, markedFrom_next ring C Yl Y e hfrom,
    (carry_next_carry ring C s hg Y hreach k hshape e).2.2 hne, ?_, ?_⟩
  · refine ⟨U, ?_, hlen, hU, ?_, hpw⟩
    · by_cases hrn : ring.rightNeighbor e = winSite s k
      · have hyk : (Y.1.1 (ring.rightNeighbor e)).qCarry.isL = true := by
          rw [hrn]; exact host_isL s Y k hshape.2.2.1
        have := trace_host_keep ring C Y e hne' hxl hyl hyk
        rw [hrn] at this
        rw [this]; exact hcarry
      · rw [next_ghost_away ring C Y e _ (fun h => hne h.symm) (fun h => hrn h.symm)]
        exact hcarry
    · intro a ha
      have := hUt a ha
      rw [next_clock]
      omega
  · intro j hj1 hj2
    have hjr := hreg j hj1 hj2
    have hj0 : 1 ≤ j := by omega
    by_cases he1 : e = winSite s j
    · rw [he1]
      exact regdata_src ring C s hg Y hreach sam j hj0 hj2 (htails j hj0 hj2) hjr
    · by_cases he2 : ring.rightNeighbor e = winSite s j
      · -- the edge into register j comes from register j - 1
        have hej : e = winSite s (j - 1) := by
          apply certSite_pred ring s e (topClockSpan n + (j - 1))
          rw [he2]
          unfold winSite
          congr 1
          omega
        have hjk : j - 1 ≠ k := by
          intro h
          apply hne
          rw [hej, h]
        have hjk' : k < j - 1 := by omega
        have hprev := hreg (j - 1) hjk' (by omega)
        have hresp := regdata_resp ring C s hg Y hreach sam (j - 1) (by omega) (by omega)
          (htails (j - 1) (by omega) (by omega))
          (by rw [show j - 1 + 1 = j by omega]; exact htails j hj0 hj2) hprev
          (by rw [show j - 1 + 1 = j by omega]; exact hjr)
        rw [hej]
        rw [show j - 1 + 1 = j by omega] at hresp
        exact hresp
      · exact regdata_away ring C s sam Y j e (fun h => he1 h.symm) (fun h => he2 h.symm) hjr

end MarkedCells
end L3

#print axioms L3.MarkedCells.sweep_adv
#print axioms L3.MarkedCells.sweep_keep
