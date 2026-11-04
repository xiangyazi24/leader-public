import Leader.PPL.Modes.StoppedClockInterfaces

/-!
# Corrected stopped-clock interface

`StoppedClockSuffixBounds` is false: its first conjunct fails at psi = 1, where
`PPL.transition` is the identity (`stoppedClockSuffixBounds_not_true`).  Any statement taking it as a premise is
vacuous.  This is the corrected interface: `2 <= psi` guards the reset clause;
the second conjunct is unchanged (it already carries `2 <= psi`).
-/

namespace PPL.Probability

set_option autoImplicit false

def StoppedClockSuffixBoundsCorrected : Prop :=
  (forall (n psi kappa : Nat)
      (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
      (x e : Fin n),
      2 <= psi ->
      clockResetAt ring C0 x e = true ->
        (pplStep ring C0 e x).clock.val = 0) /\
  (forall (n psi kappa T E M : Nat),
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
                psi (C x).hits.val E M)

theorem stoppedClockSuffixBounds_imp_corrected
    (h : StoppedClockSuffixBounds) : StoppedClockSuffixBoundsCorrected :=
  ⟨fun n psi kappa ring C0 x e _ hr => h.1 n psi kappa ring C0 x e hr, h.2⟩

end PPL.Probability

#print axioms PPL.Probability.stoppedClockSuffixBounds_imp_corrected
