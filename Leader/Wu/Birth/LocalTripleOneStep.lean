import Leader.Wu.Birth.ReacquireReentryMass
import Leader.Wu.Birth.IncreaseOrCapReacquireCounterexample

namespace BirthB1Local3OneStep

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- The cap branch is historical and therefore survives one more letter. -/
theorem target_true_one_step
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u : List (Fin n)) (e : Fin n)
    (ht : BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true) :
    BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C (u ++ [e]) = true := by
  apply (BirthPhaseWait2BlockProgress.target_true_iff
    hpsi h2 kappa ring C (u ++ [e])).2
  rcases (BirthPhaseWait2BlockProgress.target_true_iff
    hpsi h2 kappa ring C u).1 ht with ⟨pre, a, post, hword, hcap⟩
  refine ⟨pre, a, post ++ [e], ?_, hcap⟩
  calc
    u ++ [e] = (pre ++ (a :: post)) ++ [e] := by rw [hword]
    _ = pre ++ (a :: (post ++ [e])) := by simp [List.append_assoc]

/-- A chronological no-cap word forbids a cap at every displayed prefix. -/
private theorem noCap_hit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (pre : List (Fin n)) (e : Fin n) (post : List (Fin n))
    (h : BirthPhaseB3ReacquireSide.NoCapAlong
      hpsi h2 kappa ring C (pre ++ (e :: post))) :
    ¬ BirthShortDoneTerminalPassiveR4.RowCap2 hpsi h2 kappa ring
      (pre.foldl (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C) e := by
  induction pre generalizing C with
  | nil => exact h.1
  | cons a pre ih =>
      change (¬ BirthShortDoneTerminalPassiveR4.RowCap2
        hpsi h2 kappa ring C a) /\
        BirthPhaseB3ReacquireSide.NoCapAlong hpsi h2 kappa ring
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C a)
          (pre ++ (e :: post)) at h
      simpa only [List.foldl_cons] using
        ih (C := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C a) h.2

private theorem target_false_of_noCap
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u : List (Fin n))
    (h : BirthPhaseB3ReacquireSide.NoCapAlong hpsi h2 kappa ring C u) :
    BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = false := by
  classical
  have hf : ¬ BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi h2 kappa ring C u := by
    rintro ⟨pre, e, post, hword, hcap⟩
    exact (noCap_hit hpsi h2 kappa ring C pre e post
      (by simpa [hword] using h)) hcap
  simp [BirthPhaseWait2BlockProgress.target, hf]

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 2

private def regs (lab : Fin 2) (hh : Bool) : Registers 2 where
  label := lab; h := hh; carry := false; reset := false; count := 0
  wait := true; bit := false; phase := false; writer := .none

private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0 false)
  else if i = 1 then { cell (regs 1 false) with reset_cmd := true }
  else if i = 2 then cell (regs 0 true)
  else cell (regs 1 true)

private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]

private def source : FC 4 2 2 0 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩

private def prefix4 : List (Fin 4) := [(2 : Fin 4), (1 : Fin 4)]
private def undo4 : Fin 4 := 2

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
/-- 0 -> 1 on edge 2, transport the reset on edge 1, then edge 2 resets 1 -> 0. -/
theorem literal_count_trace :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 source = 0 /\
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (BirthB1ReacquireReentryMass.prefixEndpoint hpsi2 h2 ring4 source prefix4) = 1 /\
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (BirthB1ReacquireReentryMass.prefixEndpoint hpsi2 h2 ring4 source
        (prefix4 ++ [undo4])) = 0 := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
private theorem literal_noCap :
    BirthPhaseB3ReacquireSide.NoCapAlong hpsi2 h2 2 ring4 source
      (prefix4 ++ [undo4]) := by
  decide

/-- Literal refutation of arbitrary one-step stability of `Resolves`. -/
theorem resolves_not_one_step_stable :
    BirthPhaseB3ReacquireEvent.Resolves hpsi2 h2 2 ring4 anchor4 source prefix4 /\
    ¬ BirthPhaseB3ReacquireEvent.Resolves hpsi2 h2 2 ring4 anchor4 source
      (prefix4 ++ [undo4]) := by
  rcases literal_count_trace with ⟨h0, h1, h2c⟩
  have ht := target_false_of_noCap hpsi2 h2 2 ring4 source
    (prefix4 ++ [undo4]) literal_noCap
  constructor
  · right
    change BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 source <
      BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
        (BirthB1ReacquireReentryMass.prefixEndpoint hpsi2 h2 ring4 source prefix4)
    omega
  · rintro (htar | hinc)
    · rw [ht] at htar
      cases htar
    · change BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 source <
        BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
          (BirthB1ReacquireReentryMass.prefixEndpoint hpsi2 h2 ring4 source
            (prefix4 ++ [undo4])) at hinc
      omega

/-- Least stopped/right-extension closure of the current endpoint predicate. -/
def StoppedResolves
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  ∃ pre post, u = pre ++ post /\
    BirthPhaseB3ReacquireEvent.Resolves hpsi h2 kappa ring anchor C pre

theorem stoppedResolves_one_step
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n) (C : FC n psi kappa tau)
    (u : List (Fin n)) (e : Fin n)
    (h : StoppedResolves hpsi h2 kappa ring anchor C u) :
    StoppedResolves hpsi h2 kappa ring anchor C (u ++ [e]) := by
  rcases h with ⟨pre, post, hword, hres⟩
  refine ⟨pre, post ++ [e], ?_, hres⟩
  calc
    u ++ [e] = (pre ++ post) ++ [e] := by rw [hword]
    _ = pre ++ (post ++ [e]) := by rw [List.append_assoc]

end BirthB1Local3OneStep

#print axioms BirthB1Local3OneStep.target_true_one_step
#print axioms BirthB1Local3OneStep.literal_count_trace
#print axioms BirthB1Local3OneStep.resolves_not_one_step_stable
#print axioms BirthB1Local3OneStep.stoppedResolves_one_step
