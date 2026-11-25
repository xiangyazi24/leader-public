import Leader.L4.RestartMean
import Leader.L4.RestartFailure
import Leader.L4.TripleAssembly

namespace L4.RestartClosure
open RankPhysical RestartMachine RestartSerial TripleResidual Classical

/-- Literal restart observer with a single explicit timing premise.
All routing, interruption, finite-word composition and protected
failure estimates are derived on the original pair transition. -/
noncomputable def observerOfTripleClock {p c n : Nat} (x : Config p c n)
    (hq : QuietEntrance x) (hr : 2≤rank x)
    (P : Params p c n (rank x)) (clock : ConcreteTripleSharpClock) :
    VerifiedObserver x where
  State := {s : RestartMachine.State p c n (rank x) // rank s.config≤rank x}
  start := ⟨RestartMachine.start x hq hr,Nat.le_refl _⟩
  next := RestartMachine.next P
  project := fun s => s.val.config
  done := fun s => doneMode s.val.mode=true
  failed := fun s => failedMode s.val.mode=true
  initial := rfl
  projectStep := step_project P
  quiet := fun s => s.val.quiet
  doneAbsorbs := terminal_sticky P
  terminalFailure := fun y hy hD => terminals y.val hD hy
  mean := RestartMean.start_mean x hq hr P clock
  failure := by
    intro t
    have h := RestartFailure.start_failure_bound x hq hr P t
    change 1000*RankRenewal.endpointSum (RestartMachine.next P) RestartFailure.failScore t
      ⟨RestartMachine.start x hq hr,Nat.le_refl _⟩≤11*n^t at h
    rw [show RestartFailure.failScore (p:=p) (c:=c) (n:=n) (r:=rank x) =
        (fun s => @ite Nat (failedMode s.val.mode=true) (Classical.propDecidable _) 1 0) by
      funext s
      by_cases z : failedMode s.val.mode=true <;> simp [RestartFailure.failScore,z]] at h
    exact h

theorem concreteRestartTrial_of_triple_clock (clock : ConcreteTripleSharpClock) :
    RootIndependentRestartTrial := by
  apply concreteRestartTrial_of_verified_observers
  intro p c n x hp hc hn hq hr
  exact ⟨observerOfTripleClock x hq hr ⟨hp,hc,hn,hr⟩ clock⟩

theorem concreteRestartTrial_of_physical_stageB (h : TripleAssembly.ConcretePhysicalStageB) :
    RootIndependentRestartTrial :=
  concreteRestartTrial_of_triple_clock (TripleAssembly.sharp_clock_of_physical_stageB h)

end L4.RestartClosure

#print axioms L4.RestartClosure.observerOfTripleClock
#print axioms L4.RestartClosure.concreteRestartTrial_of_triple_clock
#print axioms L4.RestartClosure.concreteRestartTrial_of_physical_stageB
