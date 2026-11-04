import Leader.L3.Top.PinnedPhaseSweep
import Leader.L3.Top.PinnedPhaseStop

/-!
# Q7 (P.12 preparation, lemma 2): the strict-terminal certificate of the aligned carry sweep

If the sweep invariant holds with the host at the last register, the next service (the terminal
edge of the window) records a terminal whose ledger has `r` uses, and together with the static data
of the launch state (the `r` samples, the `r` exports in reverse order with nothing foreign
between them) this is a strict cyclic comparison terminal.  With `NoPrefixStop` of the predecessor
it is a strict stop (`phase_stop_of_terminal`).

Consumer: `Leader/L3/Top/PinnedPhaseSweepCost.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The static data of the launch state**: the `r` samples of the aligned window and the `r`
exports that carried them, in reverse order, with nothing foreign between them.

Consumer: `sweep_strict`. -/
def SweepStatic {n : Nat} (s : Fin n) (Yl : TopFixedTraceState n)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (exs : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∀ j, j < topClockSpan n → DigitRecordedSample Yl.1.2 (sam j) ∧ (sam j).id.lane = .comparison ∧
    (sam j).id.site = certSite s j ∧ 0 < (sam j).id.time ∧ (sam j).tail = decide (j = 0)) ∧
  (∀ j, j < topClockSpan n → DigitRecordedExport Yl.1.2 (exs j) ∧ (exs j).lane = .comparison ∧
    (exs j).source = certSite s (topClockSpan n - 1) ∧
    (exs j).destination = certSite s (topClockSpan n) ∧
    (exs j).operand = some (.sampled (sam j).id) ∧ (exs j).value = (sam j).value ∧
    (exs j).tail = (sam j).tail ∧ (sam j).id.time < (exs j).time ∧
    (exs j).time ≤ Yl.1.2.clock) ∧
  (∀ i j, i < topClockSpan n → j < topClockSpan n → i < j → (exs j).time < (exs i).time) ∧
  (∀ other : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport Yl.1.2 other →
    other.lane = .comparison → other.source = certSite s (topClockSpan n - 1) →
    other.destination = certSite s (topClockSpan n) →
    (exs (topClockSpan n - 1)).time ≤ other.time → other.time ≤ (exs 0).time →
    ∃ j, j < topClockSpan n ∧ other = exs j)

/-- The audit start of a run is the projection of the entrance configuration.

Consumer: `sweep_strict`. -/
theorem run_start {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (w : List (Fin n)) : (topFixedTraceRun ring C w).1.2.start = piD C := by
  have key : ∀ (v : List (Fin n)) (Z : TopFixedTraceState n), Z.1.2.start = piD C →
      (v.foldl (topFixedTraceNext ring C) Z).1.2.start = piD C := by
    intro v
    induction v with
    | nil => intro Z h; exact h
    | cons e v ih => intro Z h; exact ih _ (by simp [topFixedTraceNext, digitAuditStep, h])
  exact key w _ rfl

/-- A recorded sample persists to the extended audit.

Consumer: `sweep_strict`. -/
theorem rec_sample_ext {c : Compiled} {n : Nat} {A B : DigitAudit c n} (h : PhaseAuditExt A B)
    {x : DigitSample c n} (hx : DigitRecordedSample A x) : DigitRecordedSample B x := by
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := hx
  exact ⟨f, (h.2.2.1 f hf).1, h1, h2, h3, h4⟩

/-- A recorded export persists to the extended audit.

Consumer: `sweep_strict`. -/
theorem rec_export_ext {c : Compiled} {n : Nat} {A B : DigitAudit c n} (h : PhaseAuditExt A B)
    {x : DigitExport c n} (hx : DigitRecordedExport A x) : DigitRecordedExport B x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := hx
  exact ⟨f, (h.2.2.1 f hf).1, h1, h2, h3⟩

/-- A recorded export of the longer audit within the clock of the shorter one is recorded in it.

Consumer: `sweep_strict`. -/
theorem rec_export_restrict {c : Compiled} {n : Nat} {A B : DigitAudit c n} (h : PhaseAuditExt A B)
    {x : DigitExport c n} (hx : DigitRecordedExport B x) (ht : x.time ≤ A.clock) :
    DigitRecordedExport A x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := hx
  exact ⟨f, phase_frame_restrict h f hf (by omega), h1, h2, h3⟩

/-- **The retiring carry records a strict cyclic terminal** (when the sweep invariant holds with
the host at the last register), and with `NoPrefixStop` of the predecessor it is a strict stop.

Consumer: `aligned_strict_cost`. -/
theorem sweep_strict {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Yl Y : TopFixedTraceState n)
    (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (exs : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hstat : SweepStatic s Yl sam exs)
    (hD : SweepDyn ring C s Yl sam (topClockSpan n - 1) Y) (hN : NoPrefixStop ring C s Y) :
    topFixedStrictStop ring C s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨hYl, hfrom, hshape, ⟨U, hcarry, hlen, hU, hUt, hpw⟩, _⟩ := hD
  have hreach : topClockReached ring C Y := markedFrom_reached ring C Yl Y hfrom
  obtain ⟨e, he⟩ : ∃ e, e = winSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  rw [← he]
  rw [← he] at hcarry
  have hxl := agent_l ring C s hg Y hreach e
  have hyl := agent_l ring C s hg Y hreach (ring.rightNeighbor e)
  have hnext : ring.rightNeighbor e = winSite s (topClockSpan n) := by
    rw [he, winSite_next]
    congr 1
    omega
  have hyb : (Y.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hnext, agent_beta ring C Y hreach]
    exact winSite_term_beta C s hg.hbad
  have hxk := host_isL s Y (topClockSpan n - 1) hshape.2.2.1
  rw [← he] at hxk
  obtain ⟨t, hrec, hlane, htime, hsrc, hdst, hledger⟩ :=
    trace_carry_terminal ring C Y e hxl hyl hyb hxk
  have hclockY : Y.1.2.clock = Y.2.length := by
    have := phase_clock_run ring C Y.2
    rw [← hreach] at this
    exact this
  have hextN : PhaseAuditExt Yl.1.2 (topFixedTraceNext ring C Y e).1.2 := by
    obtain ⟨w, hw⟩ := markedFrom_next ring C Yl Y e hfrom
    have := phase_ext_run ring C Yl.2 w
    rw [← hYl, ← hw] at this
    exact this
  apply phase_stop_of_terminal ring C s Y e hN t _ (by rw [htime, hclockY]) hsrc
  have hdstE : t.destination = certSite s (2 * topClockSpan n) := by
    rw [hdst, hnext]
    unfold winSite
    congr 1
    omega
  have hsrcE : t.source = certSite s (2 * topClockSpan n - 1) := by
    rw [hsrc, he]
    unfold winSite
    congr 1
    omega
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hstat
  have hsel : ∀ j : Fin (topClockSpan n), ∃ u, U[j.val]? = some u ∧ u.target = winSite s j.val ∧
      u.operand = some (.sampled (sam j.val).id) ∧ u.value = (sam j.val).value ∧
      u.tail = (sam j.val).tail := fun j => hU j.val (by have hj2 : j.val < topClockSpan n := j.2; omega)
  have hrN := topClockReachedNext ring C Y e hreach
  have hst := run_start ring C (topFixedTraceNext ring C Y e).2
  rw [← hrN] at hst
  refine ⟨hst, hg.hbad.1, hrec, hlane, hsrcE, hdstE, ?_⟩
  refine ⟨by show 0 < topClockSpan n; omega, { inherited := none, uses := U },
    fun j => sam j.val, fun j => exs j.val, fun j => Classical.choose (hsel j), ?_⟩
  dsimp only
  have hspec := fun j : Fin (topClockSpan n) => Classical.choose_spec (hsel j)
  refine ⟨by rw [hledger, hcarry], rfl, by show U.length = topClockSpan n; simp [hlen]; omega, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨r1, r2, r3, r4, r5⟩ := hs1 j.val j.2
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hs2 j.val j.2
    obtain ⟨u1, u2, u3, u4, u5⟩ := hspec j
    have hmem : Classical.choose (hsel j) ∈ U := List.mem_of_getElem? u1
    obtain ⟨m1, m2⟩ := hUt _ hmem
    refine ⟨rec_sample_ext hextN r1, r2, r3, r4, r5, rec_export_ext hextN q1, q2, q3, q4, q5, q6, q7,
      u1, u2, u3, u4, u5, q8, by omega, ?_⟩
    rw [htime]
    omega
  · intro i j hij
    obtain ⟨u1, _⟩ := hspec i
    obtain ⟨v1, _⟩ := hspec j
    refine ⟨hs3 i.val j.val i.2 j.2 hij, ?_⟩
    have hpw' := List.pairwise_iff_getElem.1 hpw
    have hi : i.val < U.length := by have hi2 : i.val < topClockSpan n := i.2; omega
    have hj : j.val < U.length := by have hj2 : j.val < topClockSpan n := j.2; omega
    have := hpw' i.val j.val hi hj hij
    have e1 : U[i.val] = Classical.choose (hsel i) := by
      have := List.getElem?_eq_getElem hi
      rw [u1] at this
      exact (Option.some.inj this).symm
    have e2 : U[j.val] = Classical.choose (hsel j) := by
      have := List.getElem?_eq_getElem hj
      rw [v1] at this
      exact (Option.some.inj this).symm
    rw [e1, e2] at this
    exact this
  · intro other hother hl hsrc2 hdst2 hle hge
    have hext2 : other.time ≤ Yl.1.2.clock := by
      have := (hs2 0 (by omega)).2.2.2.2.2.2.2.2
      omega
    obtain ⟨j, hj, hjo⟩ := hs4 other (rec_export_restrict hextN hother hext2) hl hsrc2 hdst2 hle hge
    exact ⟨⟨j, hj⟩, hjo⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.sweep_strict
