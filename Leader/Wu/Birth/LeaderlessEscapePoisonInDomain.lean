import Leader.Wu.Birth.LeaderlessEscapePoisonStuck

set_option autoImplicit false
set_option Elab.async false

namespace ZZDomainPoison

open PPLL PPLLRepair
open ZZPoison5All8

/-- The poison cell satisfies the protocol-domain predicate, component by
component: every `match` clause holds on its concrete fields. -/
theorem poison_in_domain_zero :
    @AgentState.inProtocolDomain 2 2 (poisonCell 0) := by
  unfold AgentState.inProtocolDomain poisonCell poison
  decide

theorem poison_in_domain_one :
    @AgentState.inProtocolDomain 2 2 (poisonCell 1) := by
  unfold AgentState.inProtocolDomain poisonCell poison
  decide

#print axioms ZZDomainPoison.poison_in_domain_zero
#print axioms ZZDomainPoison.poison_in_domain_one

end ZZDomainPoison
