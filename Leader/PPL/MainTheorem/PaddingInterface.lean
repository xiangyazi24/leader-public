import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.Whp
import Leader.PPL.ReachCPB.MismatchCompletionHistPhase
import Leader.PPL.Elim.OneLeaderBoundClosed

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1Padded.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1PaddedLiteralL1Decidable`, `theorem1_sum_if_count`, `theorem1_countP_take_pad`, `theorem1_mul_sum_le_length_mul`, `theorem1_fixedCutPaddedBound`, `theorem1L16PaddedBound_of_steps`, `theorem1L5iPaddedBound_of_lemma5Bridge`, `Theorem1L17FirstHitCutAdapter`, `theorem1L17DynamicPaddedBound_of_cutPadding`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Missing variable-cut padding for L5(ii), L17, L18 -/

/--
The exact generic counting seam needed by the three dynamic events.

stop p = true means that p is a minimal stopping prefix: in the use case
it is the prefix ending at the first C_mid hit. The first hypothesis makes
these stopping prefixes prefix-free. phaseBad p is the bad event for the phase
started from the state reached by p. The third hypothesis says that every
global bad word factors through one such stopping prefix, one T-letter bad
phase word, and an arbitrary tail.

The conclusion is precisely the coefficient-preserving padding statement.
Its proof is the finite prefix-free cylinder/Kraft sum: for each p there are
at most the phase bad count times n^(H-p.length-T) completions, and the
prefix-free cylinders satisfy sum_p n^(H-p.length) <= n^H.
-/
def Theorem1DynamicCutPadding : Prop :=
  forall {n H T c : Nat}
    (stop : DetSchedule n -> Bool)
    (phaseBad :
      DetSchedule n ->
      DetSchedule n ->
      Bool)
    (globalBad : DetSchedule n -> Bool),
    (forall p q : DetSchedule n,
      stop p = true ->
      stop q = true ->
      List.IsPrefix p q ->
      p = q) ->
    (forall p : DetSchedule n,
      stop p = true ->
      p.length + T <= H ->
      n *
          (allSchedules n T).countP
            (phaseBad p) <=
        c * n ^ T) ->
    (forall word : DetSchedule n,
      word ∈ allSchedules n H ->
      globalBad word = true ->
      exists p : DetSchedule n,
        exists phase : DetSchedule n,
          exists pad : DetSchedule n,
            stop p = true ∧
              phase ∈ allSchedules n T ∧
                word = p ++ phase ++ pad ∧
                  phaseBad p phase = true) ->
    n *
        (allSchedules n H).countP
          globalBad <=
      c * n ^ H

/-! ## Dynamic L17 padding -/

/--
The exact H17-letter literal-elimination miss event begun at a stopped full
P_PL prefix.  This is the countP-side event that must be compared with L17's
current stopping-tree l17FailureCount.
-/
def theorem1L17PhaseBad
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  !(@decide
    (PPL.LiteralL1
      (PPL.Probability.runPopulationSchedule
        PPL.Elim.protocolE ring
        (PPL.Elim.viewConfig
          (PPL.Probability.runPPL ring C0 p))
        phase))
    (theorem1LiteralL1Decidable _))

end PPL
