import Std
import Leader.Wu.Entrance.FirstHitAdmissionMass


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace ZZKeepClosedSet


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open Q11593SpliceControllerDesign
open B9ControllerRecovery
open BirthTwoStageEscape
open B9FullCarrierHost
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


/-! ## Exact controller round trip used by every full-carrier plan. -/


section RoundTrip


variable {P : Type} {psi kappa tau : Nat}


@[simp] theorem ofOldWith_toOld_self
    (laws : PhysCarrierLaws P psi kappa tau) (u : CellP P) :
    ofOldWith (toOld laws u) u.phys = u := by
  cases u
  rfl


@[simp] theorem ofOldWith_toOld_pending
    (laws : PhysCarrierLaws P psi kappa tau) (u : CellP P) (p : P) :
    (ofOldWith (toOld laws u) p).repairPending = u.repairPending := by
  rfl


@[simp] theorem ofOldWith_toOld_role
    (laws : PhysCarrierLaws P psi kappa tau) (u : CellP P) (p : P) :
    (ofOldWith (toOld laws u) p).spliceRole = u.spliceRole := by
  rfl


@[simp] theorem ofOldWith_toOld_ticket
    (laws : PhysCarrierLaws P psi kappa tau) (u : CellP P) (p : P) :
    (ofOldWith (toOld laws u) p).acquireTicket = u.acquireTicket := by
  rfl


end RoundTrip


/-! ## One-site installed closed bad set. -/


private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide


def ring1 : DirectedRing 1 := ⟨by decide⟩


def base : ExpiringAgentState 3 3 48 :=
  QuietPairCounterexample.quietBase 0


def r2 : R2.Cell 3 3 48 :=
  ⟨base, 0⟩


/-- Inner R2C controller is deliberately not open. -/
def inner : R2Coherence.Cell 3 3 48 :=
  ⟨r2, ⟨.closing, .none⟩⟩


/-- Outer controller is exactly the legal V7 host-fence shape. -/
def cell : Cell 3 3 48 :=
  ⟨inner, .none, false, true⟩


def C : Config 1 3 3 48 :=
  fun _ => cell


 theorem right_self (e : Fin 1) : ring1.rightNeighbor e = e := by
  apply Fin.ext
  simp [DirectedRing.rightNeighbor]


 theorem cell_follower : outputFinal cell = false := by
  decide +kernel


 theorem no_leader : ¬ HasLeader C := by
  intro h
  rcases h with ⟨i, hi⟩
  have hi0 : i = (0 : Fin 1) := by
    apply Fin.ext
    omega
  subst i
  have hf : outputFinal (C 0) = false := by
    simpa [C] using cell_follower
  have hbad : false = true := hf.symm.trans hi
  cases hbad


 theorem not_all_open : ¬ FinalAllOpen C := by
  intro h
  have h0 := h (0 : Fin 1)
  unfold R2Coherence.OpenControl at h0
  have hm := h0.1
  change R2Coherence.Mark.closing = R2Coherence.Mark.open at hm
  cases hm


 theorem not_admitted :
    ¬ ConcreteB7AdmittedPassive h3 h23 ring1 C := by
  intro h
  exact not_all_open h.2.2.1


 theorem old_host_fence :
    B9SpliceControllerR1TableV7.HostFenceShapeV7
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) := by
  unfold B9SpliceControllerR1TableV7.HostFenceShapeV7
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · decide +kernel


 theorem old_not_bad_ticket :
    ¬ B9ControllerRecovery.BadTicket
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) := by
  intro h
  exact h.2 (Or.inr old_host_fence)


 theorem old_not_pending :
    ¬ B9ControllerRecovery.Pending
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) := by
  intro h
  have hr := h.1
  change SpliceRole.none = SpliceRole.predecessorArmed at hr
  cases hr


 theorem old_not_bad_backing :
    ¬ B9ControllerRecovery.BadBacking
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell)
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) := by
  intro h
  exact old_not_pending h.1


 theorem old_pair_covered :
    B9ControllerRecovery.PairCovered
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell)
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) := by
  unfold B9ControllerRecovery.PairCovered
  exact Or.inl (Or.inr old_host_fence)


 theorem old_not_hole :
    ¬ B9ControllerRecovery.Hole h3
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell)
      (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) := by
  intro h
  exact h.2 old_pair_covered


 theorem not_garbage : ¬ FinalGarbage h3 cell cell := by
  intro h
  change B9ControllerRecovery.Garbage h3
    (FinalCandidateR2C.FinalCandidateR2C.oldCell cell)
    (FinalCandidateR2C.FinalCandidateR2C.oldCell cell) at h
  unfold B9ControllerRecovery.Garbage B9ControllerRecovery.ScrubGarbage at h
  rcases h with hs | hh
  · rcases hs with hL | hR | hB
    · exact old_not_bad_ticket hL
    · exact old_not_bad_ticket hR
    · exact old_not_bad_backing hB
  · exact old_not_hole hh


/-- Every scheduler letter fixes C.  This is the closure fact. -/
theorem step_stutters (e : Fin 1) :
    stepConcrete (κ := 3) (τ := 48) h3 h23 ring1 C e = C := by
  unfold stepConcrete stepFinal
  rw [if_pos (right_self e)]
  have hg : ¬ FinalGarbage h3 (C e) (C e) := by
    simpa [C] using not_garbage
  rw [if_neg hg]


/-- Singleton bad family. -/
def ClosedBad (D : Config 1 3 3 48) : Prop :=
  D = C


theorem closedBad_nonempty : ClosedBad C := by
  rfl


theorem closedBad_leaderless
    (D : Config 1 3 3 48) (hD : ClosedBad D) :
    ¬ HasLeader D := by
  unfold ClosedBad at hD
  rw [hD]
  exact no_leader


theorem closedBad_not_admitted
    (D : Config 1 3 3 48) (hD : ClosedBad D) :
    ¬ ConcreteB7AdmittedPassive h3 h23 ring1 D := by
  unfold ClosedBad at hD
  rw [hD]
  exact not_admitted


/-- Closure under every edge letter, not merely one selected edge. -/
theorem closedBad_closed
    (D : Config 1 3 3 48) (hD : ClosedBad D) (e : Fin 1) :
    ClosedBad
      (stepConcrete (κ := 3) (τ := 48) h3 h23 ring1 D e) := by
  unfold ClosedBad at hD ⊢
  rw [hD]
  exact step_stutters e


/-- Explicit nonempty closed leaderless class. -/
theorem exists_closed_bad :
    ∃ D : Config 1 3 3 48,
      ClosedBad D ∧
      ¬ HasLeader D ∧
      (∀ e : Fin 1,
        ClosedBad
          (stepConcrete (κ := 3) (τ := 48) h3 h23 ring1 D e)) := by
  refine ⟨C, closedBad_nonempty, no_leader, ?_⟩
  intro e
  exact closedBad_closed C closedBad_nonempty e


end ZZKeepClosedSet


#print axioms ZZKeepClosedSet.closedBad_closed
#print axioms ZZKeepClosedSet.exists_closed_bad
