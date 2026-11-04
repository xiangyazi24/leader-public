import Leader.PPL.Modes.SignalAbsorptionLineage
import Leader.PPL.Modes.SignalAbsorptionEncounter
import Leader.PPL.Modes.SignalAbsorptionLottery
import Leader.PPL.Modes.SignalLineageClosed

/-!
# P_PL Lemma 9, unconditional

All three split pieces are proved (lineage split, encounter lower tail,
lottery lower tail), as are SignalLineageOwnership and ModeStoppedTreeTransfer.
-/

namespace PPL.Modes.Lemma9

set_option autoImplicit false

open PPL.Probability

theorem lemma9DeterministicBridge : Lemma9DeterministicBridge :=
  lemma9Bridge_of_split
    lemma9LineageFailureSplit
    lemma9EncounterLowerTail
    lemma9LotteryLowerTail

/-- Paper Lemma 9 in finite-word Nat form, no hypotheses beyond parameters. -/
theorem lemma9_wordBound_closed
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= c)
    (hkappa : kappa = 8 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (hsignal : 0 < (C i).signalR.val) :
    Lemma9WordBound ring C i c :=
  lemma9_wordBound modeStoppedTreeTransfer lemma9DeterministicBridge
    hn3 hpsi hc hkappa hnpow ring C i hsignal
    (PPL.Modes.SignalLineage.signalLineageOwnership ring)

end PPL.Modes.Lemma9

#print axioms PPL.Modes.Lemma9.lemma9DeterministicBridge
#print axioms PPL.Modes.Lemma9.lemma9_wordBound_closed
