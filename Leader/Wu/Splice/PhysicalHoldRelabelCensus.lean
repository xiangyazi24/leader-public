import Leader.Wu.Splice.PhysicalHoldWordProjection
import Leader.Wu.Splice.FenceHandoffTable

set_option autoImplicit false

/-! Census: on the 24 x 24 leaderless base pairs built from the n = 3 fixture cores (labels 0/1,
probe and phase bits varied), does the physical host row ever equal the MOVE-COMMIT relabel
(l, relabelResponder l r)?  Result (2026-09-13): never.  Of the 288 barrier pairs, 144 create a
leader (the physical birth), 144 do not; the 288 non-barrier pairs create no leader and are not
identities either.  Output format: ((barrier, rowEqualsRelabel, rowIsIdentity, rowCreatesLeader), count). -/

namespace B9V10eRowVsRelabelCensus
open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV10b B9SpliceV10eWordProjection
private theorem hTwo : 0 < 2 := by decide
private theorem hOne : 0 < 1 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
instance instDecBarrier (a b : AgentState 2) : Decidable (isBarrier hTwo a b) := by
  unfold isBarrier; infer_instance
def b0 : ExpiringAgentState 2 1 1 := (q11874StartV10b 0).carrier.splice.base
def b1 : ExpiringAgentState 2 1 1 := (q11874StartV10b 1).carrier.splice.base
def b2 : ExpiringAgentState 2 1 1 := (q11874StartV10b 2).carrier.splice.base
def setLPP (u : ExpiringAgentState 2 1 1) (lab : Fin 2) (pr ph : Bool) : ExpiringAgentState 2 1 1 :=
  { u with core := { u.core with core := { u.core.core with label := lab, probe := pr, phase := ph } } }
def variants (u : ExpiringAgentState 2 1 1) : List (ExpiringAgentState 2 1 1) :=
  [0,1].flatMap (fun l => [false,true].flatMap (fun pr => [false,true].map (fun ph => setLPP u l pr ph)))
def bases : List (ExpiringAgentState 2 1 1) := variants b0 ++ variants b1 ++ variants b2
-- for each leaderless pair (l, r): is the physical host row equal to (l, relabelResponder l r)?

end B9V10eRowVsRelabelCensus
