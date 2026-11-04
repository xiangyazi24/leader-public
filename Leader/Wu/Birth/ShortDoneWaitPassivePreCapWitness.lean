import Leader.Wu.Birth.ShortDoneWaitPassivePreCap

namespace BirthShortDoneWaitPassiveR1Audit

open PPLL PPLLDomain PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair BirthWaitPassive BirthShortWait
  BirthShortDoneWaitPassiveR1

set_option autoImplicit false
set_option pp.structureInstances false

def preA : Registers 3 :=
  ⟨0, false, true, true, 0, true, false, false, .none⟩

def preB : Registers 3 :=
  ⟨1, false, true, true, 0, true, true, true, .depart⟩

theorem preA_domain : (cell preA).inProtocolDomain 1 := by
  simp [cell, preA, AgentState.inProtocolDomain]

theorem preB_domain : (cell preB).inProtocolDomain 1 := by
  simp [cell, preB, AgentState.inProtocolDomain]

/-- Finite full-host endpoints; authorization and stall values intentionally differ. -/
def preL : ExpiringAgentState 3 1 2 :=
  ⟨⟨BoundedAgentState.ofDomain (cell preA) preA_domain, false⟩,
    ⟨2, by decide⟩⟩

def preR : ExpiringAgentState 3 1 2 :=
  ⟨⟨BoundedAgentState.ofDomain (cell preB) preB_domain, true⟩,
    ⟨1, by decide⟩⟩

theorem preL_raw : raw preL = cell preA := by
  change (BoundedAgentState.ofDomain (cell preA) preA_domain).erase = cell preA
  exact BoundedAgentState.erase_ofDomain _ _

theorem preR_raw : raw preR = cell preB := by
  change (BoundedAgentState.ofDomain (cell preB) preB_domain).erase = cell preB
  exact BoundedAgentState.erase_ofDomain _ _

theorem pre_registers :
    preA.wait = true ∧ preB.wait = true ∧
    preA.writer = .none ∧ preB.writer = .depart ∧
    preA.carry = true ∧ preA.reset = true ∧
    preB.carry = true ∧ preB.reset = true := by
  decide

theorem pre_sources_passive : Passive (raw preL) ∧ Passive (raw preR) := by
  rw [preL_raw, preR_raw]
  simp [Passive, Metadata, InertWriter, preA, preB, cell, registers]

theorem pre_cyclic :
    preB.label =
      ⟨(preA.label.val + 1) % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩ := by
  decide

theorem pre_preCap :
    PreCap2 (by decide : 0 < 3) (by decide : 2 <= 3) 1
      (cell preA) (cell preB) := by
  unfold PreCap2
  decide

theorem pre_writer_image :
    let w := waitWidth (psi := 3) (width := 2)
      (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 2 <= 3)
      1 (cell preA) (cell preB)
    let d := writerRegs (by decide : 0 < 3) (registers w.1) (registers w.2)
    d.1.writer = .none ∧ d.2.writer = .depart := by
  decide

/-- Concrete satisfiable instance of the exact frozen full-row theorem. -/
theorem finite_full_host_preCap :
    let w := waitWidth (psi := 3) (width := 2)
      (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 2 <= 3)
      1 (cell preA) (cell preB)
    let q := row2 (kappa := 1) (tau := 2)
      (by decide : 0 < 3) (by decide : 2 <= 3) preL preR
    clock (raw q.1) = clock w.1 ∧ clock (raw q.2) = clock w.2 ∧
      Passive (raw q.1) ∧ Passive (raw q.2) := by
  exact full_row2_preCap
    (by decide : 0 < 3) (by decide : 2 <= 3) 1 2
    preL preR preA preB preL_raw preR_raw
    (by decide) (by decide)
    (Or.inl rfl) (Or.inr rfl)
    pre_cyclic pre_preCap

/-- The supplied kappa=0 cap pair is precisely outside the theorem's branch. -/
theorem supplied_cap_excluded :
    ¬ PreCap2 (by decide : 0 < 3) (by decide : 2 <= 3) 0
      (cell capA) (cell capB) := by
  unfold PreCap2
  decide

/-- Scope guard: this is the old short dispatcher, nothing stronger. -/
theorem dispatcher_scope {psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    row2 hpsi h2 l r = BirthShortDoneDispatcher.row
      (width := 2) hpsi (by decide) h2 l r :=
  row2_eq_actual hpsi h2 l r

#print axioms finite_full_host_preCap
#print axioms supplied_cap_excluded
#print axioms dispatcher_scope

end BirthShortDoneWaitPassiveR1Audit
