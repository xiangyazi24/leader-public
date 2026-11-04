import Leader.Wu.Epoch.FilterSweep
import Leader.Wu.Protocol.RepairRegression

/-!
# Hostile regressions for the P_PLL-derived epoch filter

The epoch filter must satisfy two opposite checks.  It must genuinely consume
some result of the integrated P_PLL transition, rather than merely rename the
pure epoch protocol; and it must suppress unsafe P_PLL leader outputs before
they become observable.  T8 supplies the retained-data positive control, while
T1 supplies the output-sanitization negative control.
-/

namespace PPLLDerivedEpochRegression

open PPLL PPLLRepair PPLLRepairRegression PPLLProtectedEpochProtocol
  PPLLDerivedEpochRepair

/-- T8's interacting finite cores equipped with their physical ring positions
as slots. -/
def t8EpochLeft : EpochAgentState 4 2 10 :=
  ⟨t8FiniteConfig 2, 2⟩

def t8EpochRight : EpochAgentState 4 2 10 :=
  ⟨t8FiniteConfig 3, 3⟩

/-- P_PLL-derived filtered result on T8's orphan-write pair. -/
def filteredT8EpochPair : EpochAgentState 4 2 10 × EpochAgentState 4 2 10 :=
  ppllEpochFilterTransition (by omega) 10 (by omega)
    t8EpochLeft t8EpochRight

/-- Pure epoch result on the same physical epoch states. -/
def pureT8EpochPair : EpochAgentState 4 2 10 × EpochAgentState 4 2 10 :=
  epochTransition (by omega) t8EpochLeft t8EpochRight

/-- The derived protocol is not the pure epoch protocol in disguise: T8's
integrated bit proposal survives the filter and differs from pure sanitation of
the raw input.  This is a retained-data fact, not approval of the orphan write
lifecycle. -/
theorem filtered_epoch_really_consumes_integrated_t8_bit :
    filteredT8EpochPair.2.core.bit ≠ pureT8EpochPair.2.core.bit := by
  decide

/-- T1's finite comparison pair with consistent physical slots. -/
def t1EpochLeft : EpochAgentState 4 2 10 :=
  ⟨t1FiniteConfig 2, 2⟩

def t1EpochRight : EpochAgentState 4 2 10 :=
  ⟨t1FiniteConfig 3, 3⟩

/-- Filtered result on T1's forged complete comparison carrier. -/
def filteredT1EpochPair : EpochAgentState 4 2 10 × EpochAgentState 4 2 10 :=
  ppllEpochFilterTransition (by omega) 10 (by omega)
    t1EpochLeft t1EpochRight

/-- The underlying integrated P_PLL core creates a leader on T1, but the epoch
filter recomputes the initiator role from nonzero slot two before exposing the
output. -/
theorem filtered_epoch_suppresses_integrated_t1_leader :
    (integratedBoundedTransition (by omega : 2 > 0) 10
        t1EpochLeft.core t1EpochRight.core).1.leader = true ∧
      filteredT1EpochPair.1.core.leader = false := by
  decide

/-- Canonical sanitation of the finite T1 cores provides an explicit inhabited
protected set for the P_PLL-derived protocol. -/
def filteredCanonicalT1 : Fin 4 → EpochAgentState 4 2 10 :=
  canonicalEpochConfig t1FiniteConfig

/-- The repaired legitimate predicate is concretely inhabited. -/
theorem filteredCanonicalT1_protected :
    ProtectedEpoch (by omega : 4 > 0) PPLLCounterexample.ring4
      filteredCanonicalT1 :=
  canonicalEpochConfig_protected (by omega) PPLLCounterexample.ring4
    t1FiniteConfig

/-- The concrete inhabited protected configuration is Definition-1 safe for
the P_PLL-derived filtered protocol. -/
theorem filteredCanonicalT1_isSafe :
    PopulationProtocol.IsSafe
      (ppllEpochFilterProtocol (by omega) 10 (by omega))
      PPLLCounterexample.ring4 filteredCanonicalT1 isLeaderOutput :=
  ppllEpochFilter_isSafe (by omega) 10 PPLLCounterexample.ring4
    filteredCanonicalT1_protected

end PPLLDerivedEpochRegression
