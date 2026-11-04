import Leader.Wu.Safety.PermitRepairQuietLap

namespace R1CandidateNotClosed

open PPLLExpiringComparisonRepair R1CandidateKernel

set_option autoImplicit false
set_option Elab.async false

-- All original witness fields are retained except site 1's signal_ws.
def signalSeed (i : Fin 9) : ExpiringAgentState 3 3 48 :=
  let u := R1CandidateKernel.witness i
  if i = 1 then
    let b := { u.core.core with
      signal_ws := true
    }
    ⟨⟨b, u.core.path0Crossed⟩, u.stall⟩
  else u

-- Compute the existing Boolean checker, not a new weakened predicate.
theorem signalSeed_bool :
    candR1B (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing signalSeed = true := by
  decide +kernel

theorem signalSeed_mem :
    CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing signalSeed :=
  (candR1B_iff (by decide) (by decide)
    witnessRing signalSeed).1 signalSeed_bool

def signalAfter : FC 9 3 3 48 :=
  BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
    (by decide : 2 ≤ 3) witnessRing signalSeed (0 : Fin 9)

-- Only one output cell is evaluated; no whole-configuration simp call.
theorem signalAfter_armed :
    (signalAfter (0 : Fin 9)).core.core.gen_ws = true := by
  decide +kernel

-- Prove the projection on abstract records before using the fixture.
private theorem candidate_gen_ws_false
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hC : CandR1 hpsi h2 ring C)
    (i : Fin n) : (C i).core.core.gen_ws = false := by
  obtain ⟨root, hA⟩ := hC
  exact (hA.2.2.2.1 i).2.1.2.2.2

-- Subsequent reasoning must not execute the fixture through whnf.
attribute [local irreducible]
  signalSeed BirthCheckPermitRepairLeaf.step1 BirthCheckPermitRepair.row

theorem signalAfter_not_candidate :
    ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing signalAfter := by
  intro hC
  have hz := candidate_gen_ws_false (by decide) (by decide)
    witnessRing signalAfter hC (0 : Fin 9)
  have hbad : false = true := hz.symm.trans signalAfter_armed
  cases hbad

/-- Concrete existential escape, with the requested parameters and step. -/
theorem candR1_not_closed :
    ∃ (C : FC 9 3 3 48) (e : Fin 9),
      CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing C ∧
      ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing
        (BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
          (by decide : 2 ≤ 3) witnessRing C e) := by
  exact ⟨signalSeed, (0 : Fin 9), signalSeed_mem,
    signalAfter_not_candidate⟩

end R1CandidateNotClosed
