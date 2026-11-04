import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.WaitPassiveHost

/-! Width-two terminal consumer at the parameter witness psi = 3, kappa = 3, tau = 48: the row on the internal edge
(label 0, label 1) of an aligned equal CHECK train.  Without the crossing permit on the label-0 component both
endpoints leave the row in `equal` (the chain can continue to label 2); with the permit (what every crossed train
carries) the authorized CMP_UPDATE fresh start leaves both in `congest`. -/

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthWaitPassive

namespace B6CheckClobberConsumer

def regsB (lab : Fin 3) (b : Bool) : Registers 3 :=
  { label := lab, h := false, carry := false, reset := false, count := 0, wait := true,
    bit := b, phase := false, writer := .none }

def withPath (lab : Fin 3) (b : Bool) : AgentState 3 :=
  { cell (regsB lab b) with path := .some lab.val (if b then 1 else 0) }

theorem dom_path (lab : Fin 3) (b : Bool) : (withPath lab b).inProtocolDomain 3 := by
  have h := lab.isLt
  cases b <;> simp [withPath, cell, regsB, AgentState.inProtocolDomain, h]

def tok (lab : Fin 3) (b crossed : Bool) : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain (withPath lab b) (dom_path lab b), crossed⟩, Fin.last 48⟩

theorem uncrossed_row_keeps_equal :
    let q := BirthShortDoneTerminalHost.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (tok 0 true false) (tok 1 false false)
    q.1.core.core.state = .equal ∧ q.2.core.core.state = .equal := by
  decide +kernel

theorem crossed_row_leaves_congest :
    let q := BirthShortDoneTerminalHost.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (tok 0 true true) (tok 1 false false)
    q.1.core.core.state = .congest ∧ q.2.core.core.state = .congest ∧ q.2.core.core.leader = false := by
  decide +kernel

end B6CheckClobberConsumer
