import Leader.PPL.Modes.DetectionEntryClockRise
import Leader.PPL.Modes.DetectionEntryClockSplit
import Leader.PPL.Modes.DetectionEntryCoverage
import Leader.PPL.Modes.DetectionEntryCounting
import Leader.PPL.Modes.EarlyLeaderStop
import Leader.PPL.Modes.SignalAbsorptionClosed

/-!
# P_PL Lemma 6, unconditional

All five split pieces are proved (leaderless signal coverage, signal clearance
count, clock failure split, clock rise count, two-block bind), as are
EarlyLeaderStopBounds, SignalLineageOwnership and Lemma 9.
-/

namespace PPL.Modes.Lemma6

set_option autoImplicit false

theorem lemma6DeterministicBridge : Lemma6DeterministicBridge :=
  lemma6Bridge_of_split
    lemma6LeaderlessSignalCoverage
    lemma6SignalClearanceCount
    lemma6ClockFailureSplit
    lemma6ClockRiseCount
    lemma6TwoBlockBind

/-- Paper Lemma 6 in finite-word Nat form, no hypotheses beyond parameters. -/
theorem lemma6_wordBound_closed
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= c)
    (hkappa : kappa = 8 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Lemma6WordBound ring C c :=
  lemma6_wordBound PPL.Probability.earlyLeaderStopBounds
    lemma6DeterministicBridge
    hn3 hpsi hc hkappa hnpow ring C
    (PPL.Modes.SignalLineage.signalLineageOwnership ring)
    (fun i hsignal =>
      PPL.Modes.Lemma9.lemma9_wordBound_closed
        hn3 hpsi hc hkappa hnpow ring C i hsignal)

end PPL.Modes.Lemma6

#print axioms PPL.Modes.Lemma6.lemma6DeterministicBridge
#print axioms PPL.Modes.Lemma6.lemma6_wordBound_closed
