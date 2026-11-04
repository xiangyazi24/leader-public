import Leader.L3.Top.FreshTailJointDrift
import Leader.L3.ProbStages

/-!
Q7c P.3 J4 anchor clock. From the
actual fixed-public audit start, under the original topFixedTraceNext
and the uniform scheduler, the first strict stop or genuine border-tail
acceptance P_a is reached in expected time at most n * topClockF r.

The stopped joint potential (zero at P_a) is run through
Prob.costNumerator_le_of_nominated_edge on the subtype of reached cuts
whose strict prefixes avoid a genuine tail; the transition is frozen at
P_a, which does not change the first-hit cost. Every cut's Psi is at most
8r^3 + A(r+2) + (r^2+3r) <= topClockF r.

Scope: this is the anchor P_a, not TopClockFreshTailPhase's
permanent firstTail cut, which is the separate J5 obligation.
-/

namespace L3

open Classical
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- P_a = strict stop or genuine first border tail accepted. -/
def topFreshTailJointAnchorHit
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFixedTraceState n → Prop :=
  topClockStopOr ring C s (topClockGenuineTailAccepted C s)

/-- Stopped joint potential: zero at P_a, Psi elsewhere. -/
noncomputable def topFreshTailJointStoppedPotential
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Nat :=
  if topFreshTailJointAnchorHit ring C s Z then 0
  else topFreshTailJointPotential ring C s Z

/-- Reached cut whose strict prefixes avoid a genuine border tail. -/
def TopFreshTailJointPreAnchor
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 → suffix ≠ [] →
    ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre)

/-- A pre-anchor cut that has not hit P_a has its whole history,
including itself, free of a genuine tail.
Consumer: topFreshTailJointPreAnchorNext and the drift in
topFreshTailJointAnchorCostFromReachedDrift. -/
theorem topFreshTailJointPreAnchorFull
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hZ : TopFreshTailJointPreAnchor ring C s Z)
    (hnot : ¬ topFreshTailJointAnchorHit ring C s Z) :
    ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre) :=
  topFreshTailJointPrefixFull ring C s Z hZ.1 hZ.2 (fun hg => hnot (Or.inr hg))

/-- Every actual edge out of a pre-anchor cut that has not hit P_a
lands on a pre-anchor cut. Consumer: topFreshTailJointCutNext. -/
theorem topFreshTailJointPreAnchorNext
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hZ : TopFreshTailJointPreAnchor ring C s Z)
    (hnot : ¬ topFreshTailJointAnchorHit ring C s Z) (e : Fin n) :
    TopFreshTailJointPreAnchor ring C s (topFixedTraceNext ring C Z e) :=
  ⟨topClockReachedNext ring C Z e hZ.1,
    topFreshTailJointPrefixStep ring C s Z e
      (topFreshTailJointPreAnchorFull ring C s Z hZ hnot)⟩

/-- The actual transition on pre-anchor cuts, frozen once P_a holds. -/
noncomputable def topFreshTailJointCutNext
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    {Z : TopFixedTraceState n // TopFreshTailJointPreAnchor ring C s Z} →
      Fin n →
      {Z : TopFixedTraceState n // TopFreshTailJointPreAnchor ring C s Z} :=
  fun x e =>
    if h : topFreshTailJointAnchorHit ring C s x.1 then x
    else ⟨topFixedTraceNext ring C x.1 e,
      topFreshTailJointPreAnchorNext ring C s x.1 x.2 h e⟩

/-- Freezing the transition at P_a leaves the first-hit cost of the
original topFixedTraceNext unchanged.
Consumer: topFreshTailJointAnchorCostFromReachedDrift. -/
theorem topFreshTailJointCutCost
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    ∀ (T : Nat)
      (x : {Z : TopFixedTraceState n // TopFreshTailJointPreAnchor ring C s Z}),
      costNumerator (topFreshTailJointCutNext ring C s)
          (fun y => topFreshTailJointAnchorHit ring C s y.1) x T =
        costNumerator (topFixedTraceNext ring C)
          (topFreshTailJointAnchorHit ring C s) x.1 T := by
  intro T
  induction T with
  | zero =>
      intro x
      rfl
  | succ T ih =>
      intro x
      by_cases hp : topFreshTailJointAnchorHit ring C s x.1
      · rw [costNumerator_terminal (topFreshTailJointCutNext ring C s)
            (fun y => topFreshTailJointAnchorHit ring C s y.1) x hp,
          costNumerator_terminal (topFixedTraceNext ring C)
            (topFreshTailJointAnchorHit ring C s) x.1 hp]
      · rw [costNumerator_succ (topFreshTailJointCutNext ring C s)
            (fun y => topFreshTailJointAnchorHit ring C s y.1) x hp,
          costNumerator_succ (topFixedTraceNext ring C)
            (topFreshTailJointAnchorHit ring C s) x.1 hp]
        have hfun : (fun e : Fin n =>
              costNumerator (topFreshTailJointCutNext ring C s)
                (fun y => topFreshTailJointAnchorHit ring C s y.1)
                (topFreshTailJointCutNext ring C s x e) T) =
            (fun e : Fin n =>
              costNumerator (topFixedTraceNext ring C)
                (topFreshTailJointAnchorHit ring C s)
                (topFixedTraceNext ring C x.1 e) T) := by
          funext e
          rw [ih]
          simp only [topFreshTailJointCutNext, dif_neg hp]
        rw [hfun]

/-- Section 5: every cut's joint potential fits the P.3 budget,
Psi <= 8r^3 + A(r+2) + (r^2+3r) <= (r^2+1) B + 8r^3 <= topClockF r.
Consumer: topFreshTailJointAnchorClock. -/
theorem topFreshTailJointPotentialWithinF
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n) :
    topFreshTailJointPotential ring C s Z ≤ topClockF (topClockSpan n) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hc := topFreshTailPrepaidPotentialLe ring C s hn Z
  have hW := topPortPotential_le s Z
  have hsq := Nat.pow_two (topClockSpan n)
  rw [hsq] at hW
  have h3 : 3 * topClockSpan n ≤ topClockSpan n * topClockSpan n :=
    Nat.mul_le_mul_right _ hr
  have hA : topFreshTailJointVoucherCap (topClockSpan n) ≤
      topClockSpan n * topClockSpan n := by
    unfold topFreshTailJointVoucherCap
    omega
  have hV : (topClockSpan n + 2) *
        (topFreshTailJointVoucherCap (topClockSpan n) -
          topFreshTailPortReceiptCount s Z) ≤
      (topClockSpan n + 2) * (topClockSpan n * topClockSpan n) :=
    Nat.mul_le_mul_left _ (Nat.le_trans (Nat.sub_le _ _) hA)
  have hB : topClockB (topClockSpan n) =
      3 * (topClockSpan n * topClockSpan n) + 4 * topClockSpan n + 2 := by
    unfold topClockB
    rw [hsq]
  have hrB : topClockSpan n + 2 ≤ topClockB (topClockSpan n) := by
    rw [hB]
    omega
  have hWB : topClockSpan n * topClockSpan n + 3 * topClockSpan n ≤
      topClockB (topClockSpan n) := by
    rw [hB]
    omega
  have hcomm : (topClockSpan n + 2) * (topClockSpan n * topClockSpan n) ≤
      (topClockSpan n * topClockSpan n) * topClockB (topClockSpan n) := by
    rw [Nat.mul_comm (topClockSpan n + 2)]
    exact Nat.mul_le_mul_left _ hrB
  have hF : topClockF (topClockSpan n) =
      2 * ((topClockSpan n * topClockSpan n) * topClockB (topClockSpan n)) +
        topClockB (topClockSpan n) + 8 * topClockSpan n ^ 3 := by
    unfold topClockF
    rw [hsq, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  unfold topFreshTailJointPotential
  rw [hF]
  omega

/-- Section 6 item 8. From the actual fixed-public audit start of
a leaderless bad complete pair, the first-hit cost of P_a (strict stop
or genuine first border tail) under the original topFixedTraceNext is
bounded by the scaled stopped joint potential, via
Prob.costNumerator_le_of_nominated_edge with the adapted nominated edge
of topFreshTailJointNominatedEdge.
Consumer: topFreshTailJointAnchorClock (P.3 anchor clock). -/
theorem topFreshTailJointAnchorCostFromReachedDrift
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false) :
    ∀ T : Nat,
      costNumerator (topFixedTraceNext ring C)
          (topFreshTailJointAnchorHit ring C s)
          ((C, digitAuditInitial (piD C)), []) T ≤
        n ^ T * (n * topFreshTailJointStoppedPotential ring C s
          ((C, digitAuditInitial (piD C)), [])) := by
  intro T
  have hinit : TopFreshTailJointPreAnchor ring C s
      ((C, digitAuditInitial (piD C)), []) := by
    refine ⟨by unfold topClockReached; rfl, ?_⟩
    intro pre suffix h hne
    have hnil : pre ++ suffix = [] := h
    exact absurd (List.append_eq_nil_iff.mp hnil).2 hne
  have hdrop : ∀ x : {Z : TopFixedTraceState n //
        TopFreshTailJointPreAnchor ring C s Z},
      ¬ topFreshTailJointAnchorHit ring C s x.1 →
      topFreshTailJointStoppedPotential ring C s
          (topFreshTailJointCutNext ring C s x
            (topFreshTailJointNominatedEdge ring C s x.1)).1 + 1 ≤
        topFreshTailJointStoppedPotential ring C s x.1 := by
    intro x hx
    simp only [topFreshTailJointCutNext, dif_neg hx]
    have hfull := topFreshTailJointPreAnchorFull ring C s x.1 x.2 hx
    unfold topFreshTailJointStoppedPotential
    rw [if_neg hx]
    by_cases hnext : topFreshTailJointAnchorHit ring C s
        (topFixedTraceNext ring C x.1 (topFreshTailJointNominatedEdge ring C s x.1))
    · rw [if_pos hnext]
      have hpos := topFreshTailJointPrepaidPos ring C s hn x.1
      unfold topFreshTailJointPotential
      omega
    · rw [if_neg hnext]
      exact topFreshTailJointNominatedDrop ring C s hn hbad hleader x.1 x.2.1
        hfull (fun hg => hnext (Or.inr hg))
  have hnoninc : ∀ x : {Z : TopFixedTraceState n //
        TopFreshTailJointPreAnchor ring C s Z},
      ¬ topFreshTailJointAnchorHit ring C s x.1 → ∀ e : Fin n,
      topFreshTailJointStoppedPotential ring C s
          (topFreshTailJointCutNext ring C s x e).1 ≤
        topFreshTailJointStoppedPotential ring C s x.1 := by
    intro x hx e
    simp only [topFreshTailJointCutNext, dif_neg hx]
    have hfull := topFreshTailJointPreAnchorFull ring C s x.1 x.2 hx
    unfold topFreshTailJointStoppedPotential
    rw [if_neg hx]
    by_cases hnext : topFreshTailJointAnchorHit ring C s
        (topFixedTraceNext ring C x.1 e)
    · rw [if_pos hnext]
      exact Nat.zero_le _
    · rw [if_neg hnext]
      have h := topFreshTailJointHistoryReserveStep ring C s hn hbad hleader
        x.1 x.2.1 hfull e (fun hg => hnext (Or.inr hg))
      omega
  have hcost := L3.Prob.costNumerator_le_of_nominated_edge
    (topFreshTailJointCutNext ring C s)
    (fun y => topFreshTailJointAnchorHit ring C s y.1)
    (fun y => topFreshTailJointStoppedPotential ring C s y.1)
    (fun y => topFreshTailJointNominatedEdge ring C s y.1)
    hdrop hnoninc ⟨((C, digitAuditInitial (piD C)), []), hinit⟩ T
  rw [topFreshTailJointCutCost ring C s T] at hcost
  exact hcost

/-- Section 5 / section 6 item 8: the P.3 anchor clock. From the
actual fixed-public audit start of a leaderless bad complete pair, the
first strict stop or genuine first border-tail acceptance is reached
under the uniform scheduler in expected time at most n * topClockF r.
This is the anchor P_a only; identifying it with the permanent firstTail
cut of TopClockFreshTailPhase is the separate J5 obligation.
Consumer: P.3 first-tail clock (TopClockFreshTailPhase), after J5. -/
theorem topFreshTailJointAnchorClock
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockGenuineTailAccepted C s))
      ((C, digitAuditInitial (piD C)), [])
      ((n * topClockF (topClockSpan n) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s (topClockGenuineTailAccepted C s))
    (by omega) ((C, digitAuditInitial (piD C)), [])
    (n * topClockF (topClockSpan n))).2
  intro T
  have hcost := topFreshTailJointAnchorCostFromReachedDrift ring C s hn hbad
    hleader T
  have hle : topFreshTailJointStoppedPotential ring C s
      ((C, digitAuditInitial (piD C)), []) ≤ topClockF (topClockSpan n) := by
    unfold topFreshTailJointStoppedPotential
    split
    · exact Nat.zero_le _
    · exact topFreshTailJointPotentialWithinF ring C s hn _
  exact Nat.le_trans hcost
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle))

end L3

#print axioms L3.topFreshTailJointPreAnchorFull
#print axioms L3.topFreshTailJointPreAnchorNext
#print axioms L3.topFreshTailJointCutCost
#print axioms L3.topFreshTailJointPotentialWithinF
#print axioms L3.topFreshTailJointAnchorCostFromReachedDrift
#print axioms L3.topFreshTailJointAnchorClock
