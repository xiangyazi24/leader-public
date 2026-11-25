import Leader.L4.PhysicalCustodyCommutation
import Leader.L4.PhysicalCustodyHistorical

namespace L4.PhysicalCustody

/-- Each physical cut and every actual continuation end in the same full
raw configuration as a common replay. The advancing suffix is not commuted. -/
theorem replay_same_cuts {s n : Nat} (x : Raw s n)
    {u v u' v' : List (Fin n)} (hu : Commuted u u') (hv : Commuted v v') :
    rawRun x u = rawRun x u' ∧
      ∀ tail, rawRun x ((u ++ v) ++ tail) = rawRun x ((u' ++ v') ++ tail) := by
  have first := rawRun_of_commuted x hu
  exact ⟨first, fun tail => by
    unfold rawRun at *
    simp only [BStarResetSchedule.run_append]
    rw [first]
    exact congrArg (fun z => rawRun z tail) (rawRun_of_commuted (rawRun x u') hv)⟩

/-- The historic replay in the existing custody witness can certify a
sampled endpoint if each shared cut is obtained by physical commutations. -/
theorem custody_of_commuted_replay {s n : Nat} {x : Raw s n}
    (g : CustodyWitness x) (u v : List (Fin n))
    (hu : Commuted u g.u) (hv : Commuted v g.v) :
    Custody (rawRun g.initial ((u ++ v) ++ g.past)) := by
  rw [(replay_same_cuts g.initial hu hv).2 g.past, g.here]
  exact ⟨g⟩

#print axioms replay_same_cuts
#print axioms custody_of_commuted_replay
end L4.PhysicalCustody
