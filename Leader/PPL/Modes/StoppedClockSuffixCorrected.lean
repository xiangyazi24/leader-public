import Leader.PPL.Modes.StoppedClockInterfacesCorrected
import Leader.PPL.Probability.MarkedWordTransfer
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.TransitionFacts

namespace PPL.Probability

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-- The second clause of the corrected stopped-clock interface, kept verbatim
from the source interface. It bounds the raw scheduler words whose clock suffix
has at most `E` H/T marks and at least `M` physical ticks by the binary lottery
tail at the actual post-epoch hit count. -/
def StoppedClockSuffixBoundsCorrectedConjunct2 : Prop :=
  forall (n psi kappa T E M : Nat),
    2 <= n -> 2 <= psi ->
    forall (ring : DirectedRing n)
      (C0 : PPLConfig n psi kappa)
      (x : Fin n) (pre : DetSchedule n),
      ClockEpochStart ring C0 x pre ->
        let C := runPPL ring C0 pre
        stoppedClockSuffixUpperFailureCount ring C x T E M *
              2 ^ E <=
          n ^ T *
            lotteryAtLeastWordCount
              psi (C x).hits.val E M

theorem stoppedClockSuffixBoundsCorrected_conjunct2_of_interface
    (h : StoppedClockSuffixBoundsCorrected) :
    StoppedClockSuffixBoundsCorrectedConjunct2 := h.2

/-- Raw scheduler words for which the next-reset-frozen bit stream is short
enough and the corresponding lottery already has at least `M` wins. -/
def stoppedClockSuffixFrozenLotteryCount
    {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (x : Fin n) (T E M : Nat) : Nat :=
  (allSchedules n T).countP (fun word =>
    let bits := clockSuffixBits ring C x word
    decide
      (bits.length <= E /\
        M <=
          (lotteryRun psi (lotteryOffset (C x).hits.val) bits).wins))

/-- Letter-dependent freeze transfer: on every raw process prefix state, the
short frozen-stream/large-lottery event is dominated by the length-`E` binary
lottery tail. The stop decision is made from the current physical state and
the selected scheduler letter inside `clockSuffixBits`. -/
def StoppedClockSuffixLetterDependentFreezeTransfer : Prop :=
  forall (n psi kappa T E M : Nat),
    2 <= n -> 2 <= psi ->
    forall (ring : DirectedRing n)
      (C : PPLConfig n psi kappa) (x : Fin n),
      stoppedClockSuffixFrozenLotteryCount ring C x T E M * 2 ^ E <=
        n ^ T * lotteryAtLeastWordCount psi (C x).hits.val E M

/-- The scheduler-freeze transfer alone leaves the two-state physical
tick-to-lottery bridge as a separate boundary case. -/
def StoppedClockSuffixTickLotteryBridgeAtTwo : Prop :=
  forall (psi kappa : Nat),
    2 <= psi ->
    forall (ring : DirectedRing 2)
      (C : PPLConfig 2 psi kappa) (x : Fin 2)
      (word : DetSchedule 2),
      clockSuffixTicks ring C x word <=
        (lotteryRun psi (lotteryOffset (C x).hits.val)
          (clockSuffixBits ring C x word)).wins

/-- Exact remaining transfer obligation packaged with the n=2 bridge needed
to consume it. Together they imply the canonical second conjunct. -/
def StoppedClockSuffixBoundsCorrectedLetterDependentFreezeResidual : Prop :=
  StoppedClockSuffixLetterDependentFreezeTransfer /\
    StoppedClockSuffixTickLotteryBridgeAtTwo

private theorem countP_mono_of_imp
    {A : Type} (xs : List A) (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;> simp [hp, hq] <;> omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

private def correctedArmedSignalVal {psi kappa : Nat}
    (q : PPL.State psi kappa) : Nat :=
  if q.leader = true then kappa else q.signalR.val

private theorem determineMode_clocks_zero_of_reset_signal
    {psi kappa : Nat} (l r : PPL.State psi kappa)
    (hsignal : 0 < correctedArmedSignalVal l \/ 0 < r.signalR.val) :
    (PPL.determineMode l r).1.clock.val = 0 /\
      (PPL.determineMode l r).2.clock.val = 0 := by
  cases hlead : l.leader with
  | false =>
      have hline : 0 < l.signalR.val \/ 0 < r.signalR.val := by
        simpa [correctedArmedSignalVal, hlead] using hsignal
      simp [PPL.determineMode, hlead] <;>
        unfoldFinishModes <;> split <;> simp <;> split <;> simp <;>
          split <;> simp
  | true =>
      have hline : 0 < kappa \/ 0 < r.signalR.val := by
        simpa [correctedArmedSignalVal, hlead] using hsignal
      simp [PPL.determineMode, hlead] <;>
        unfoldFinishModes <;> split <;> simp <;> split <;> simp <;>
          split <;> simp

/-- The physical clause is valid on the transition's declared domain: a
positive armed signal on either endpoint enters DetermineMode's line 39 branch,
which sets both endpoint clocks to zero. The endpoint projection carries this
fact through the later token passes. -/
theorem stoppedClockSuffixBoundsCorrected_conjunct1 :
    forall (n psi kappa : Nat)
      (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
      (x e : Fin n),
      2 <= psi ->
      clockResetAt ring C0 x e = true ->
        (pplStep ring C0 e x).clock.val = 0 := by
  intro n psi kappa ring C0 x e hpsi hreset
  have hresetProp :
      (x = e \/ x = ring.rightNeighbor e) /\
        (0 < correctedArmedSignalVal (C0 e) \/
          0 < (C0 (ring.rightNeighbor e)).signalR.val) := by
    change decide
      ((x = e \/ x = ring.rightNeighbor e) /\
        (0 < correctedArmedSignalVal (C0 e) \/
          0 < (C0 (ring.rightNeighbor e)).signalR.val)) = true at hreset
    exact of_decide_eq_true hreset
  have hmode := determineMode_clocks_zero_of_reset_signal
    (C0 e) (C0 (ring.rightNeighbor e)) hresetProp.2
  have hpair := clockSuffixPairProjection hpsi
    (C0 e) (C0 (ring.rightNeighbor e))
  dsimp only at hpair
  by_cases hxe : x = e
  · subst x
    have hclock :
        (pplStep ring C0 e e).clock.val = 0 := by
      simpa [pplStep, PopulationProtocol.step, PPL.protocol,
        PPL.transition, hpsi] using
        (congrArg Fin.val hpair.1).trans hmode.1
    exact hclock
  · have hxr : x = ring.rightNeighbor e := by
      rcases hresetProp.1 with h | h
      · exact (hxe h).elim
      · exact h
    subst x
    have hne : ring.rightNeighbor e ≠ e := hxe
    simpa [pplStep, PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi, hne] using
      (congrArg Fin.val hpair.2.2.1).trans hmode.2

/-- At each fixed `psi` with `2 ≤ psi`, inserting that already available
premise does not change the reset-clause instance. The second clause is copied
unchanged in `StoppedClockSuffixBoundsCorrectedConjunct2`. -/
theorem stoppedClockSuffixResetClause_iff_corrected_at_psi_ge2
    (n psi kappa : Nat) (hpsi : 2 <= psi) :
    (forall (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
      (x e : Fin n),
      clockResetAt ring C0 x e = true ->
        (pplStep ring C0 e x).clock.val = 0) <->
    (forall (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
      (x e : Fin n),
      2 <= psi -> clockResetAt ring C0 x e = true ->
        (pplStep ring C0 e x).clock.val = 0) := by
  constructor
  · intro h ring C0 x e _ hr
    exact h ring C0 x e hr
  · intro h ring C0 x e hr
    exact h ring C0 x e hpsi hr

/-- Convert the independent edge-stop counting estimate into the requested
clock-failure bound. For `n ≥ 3` this uses the checked tick bridge; the exact
two-state bridge is the second field of the residual. -/
theorem stoppedClockSuffixBoundsCorrected_of_letterDependentFreezeTransfer
    (h : StoppedClockSuffixBoundsCorrectedLetterDependentFreezeResidual) :
    StoppedClockSuffixBoundsCorrected := by
  rcases h with ⟨hfreeze, hbridge2⟩
  refine ⟨stoppedClockSuffixBoundsCorrected_conjunct1, ?_⟩
  intro n psi kappa T E M hn2 hpsi ring C0 x pre hstart
  let C := runPPL ring C0 pre
  have hevent :
      (allSchedules n T).countP (fun word =>
        let bits := clockSuffixBits ring C x word
        decide
          (bits.length <= E /\
            M <= clockSuffixTicks ring C x word)) <=
      stoppedClockSuffixFrozenLotteryCount ring C x T E M := by
    apply countP_mono_of_imp
    intro word hbad
    dsimp only at hbad
    have hbad' := of_decide_eq_true hbad
    have htick :
        clockSuffixTicks ring C x word <=
          (lotteryRun psi (lotteryOffset (C x).hits.val)
            (clockSuffixBits ring C x word)).wins := by
      by_cases hn3 : 3 <= n
      · exact clockSuffixTickLotteryBridge n psi kappa hn3
          ring C x word
      · have hnEq : n = 2 := by omega
        subst n
        exact hbridge2 psi kappa hpsi ring C x word
    change decide
      (And ((clockSuffixBits ring C x word).length <= E)
        (M <=
          (lotteryRun psi (lotteryOffset (C x).hits.val)
            (clockSuffixBits ring C x word)).wins)) = true
    exact decide_eq_true ⟨hbad'.1, Nat.le_trans hbad'.2 htick⟩
  have hscaled := Nat.mul_le_mul_right (2 ^ E) hevent
  have hfreezeBound :=
    hfreeze n psi kappa T E M hn2 hpsi ring C x
  change
    stoppedClockSuffixUpperFailureCount ring C x T E M * 2 ^ E <=
      n ^ T * lotteryAtLeastWordCount psi (C x).hits.val E M
  exact Nat.le_trans hscaled hfreezeBound

#print axioms PPL.Probability.stoppedClockSuffixBoundsCorrected_conjunct1
#print axioms PPL.Probability.stoppedClockSuffixResetClause_iff_corrected_at_psi_ge2
#print axioms PPL.Probability.stoppedClockSuffixBoundsCorrected_of_letterDependentFreezeTransfer

end PPL.Probability
