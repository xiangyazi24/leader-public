import Leader.Wu.Entrance.PassivePost


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost
open WriterProducerRepair
open BirthLeaderlessBirthMassRenewal


variable {n ψ κ τ : Nat}


/-- Inner R2C all-open preservation for one concrete passive-admitted service.
The proof uses the served-pair R2C control frame and literal untouched sites. -/
theorem concreteB7PassiveAllOpenPost
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ConcreteB7PassiveAllOpenPostObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hg : ¬ FinalGarbage hψ (C e) (C e) := by
      have h := (hA.2.2.2 e).1
      simpa only [hs] using h
    have hstep :
        stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e = C := by
      unfold stepConcrete stepFinal
      rw [if_pos hs, if_neg hg]
    rw [hstep]
    exact hA.2.2.1
  · have hedge := hA.2.2.2 e
    have hg := hedge.1
    have ha :
        (concretePort (κ := κ) (τ := τ) hψ h2).action
            (C e) (C (ring.rightNeighbor e)) = .host := by
      simpa only [concretePort, concretePortLocal] using hedge.2.1
    have hfa :
        finalAction hψ h2
          (concretePort (κ := κ) (τ := τ) hψ h2)
          (C e) (C (ring.rightNeighbor e)) = .host := by
      unfold finalAction
      rw [if_neg hg, ha]
    have hrow :
        rowFinal hψ h2
          (concretePort (κ := κ) (τ := τ) hψ h2)
          (C e) (C (ring.rightNeighbor e)) =
        (concretePort (κ := κ) (τ := τ) hψ h2).row
          (C e) (C (ring.rightNeighbor e)) := by
      unfold rowFinal
      rw [hfa]
    have hstep :
        stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e =
          B9FullCarrierHost.writeAtP ring C e
            ((concretePort (κ := κ) (τ := τ) hψ h2).row
              (C e) (C (ring.rightNeighbor e))) := by
      unfold stepConcrete stepFinal
      rw [if_neg hs, hrow]
    have hOpenL := hA.2.2.1 e
    have hOpenR := hA.2.2.1 (ring.rightNeighbor e)
    rcases hOpenL with ⟨hLM, hLN⟩
    rcases hOpenR with ⟨hRM, hRN⟩
    have hNo :
        R2Coherence.NoHazardAt hψ h2 ring (physicalConfig C) e := by
      exact hedge.2.2
    have hc := R2Coherence.row_control_eq_of_open_no_write
      hψ (by decide : 0 < 2) h2
      (C e).phys (C (ring.rightNeighbor e)).phys
      hLM hRM hLN hRN hNo
    have hp :=
      (concretePort (κ := κ) (τ := τ) hψ h2).physical_spec
        (C e) (C (ring.rightNeighbor e))
    simp only [ha] at hp
    have hCtlL :
        ((concretePort (κ := κ) (τ := τ) hψ h2).row
          (C e) (C (ring.rightNeighbor e))).1.phys.ctl =
        (C e).phys.ctl := by
      calc
        ((concretePort (κ := κ) (τ := τ) hψ h2).row
          (C e) (C (ring.rightNeighbor e))).1.phys.ctl =
            (R2Coherence.row hψ (by decide : 0 < 2) h2
              (C e).phys (C (ring.rightNeighbor e)).phys).1.ctl := by
          have hx := congrArg
            (fun u : R2Coherence.Cell ψ κ τ => u.ctl) hp.1
          simpa [hostR2C] using hx
        _ = (C e).phys.ctl := hc.1
    have hCtlR :
        ((concretePort (κ := κ) (τ := τ) hψ h2).row
          (C e) (C (ring.rightNeighbor e))).2.phys.ctl =
        (C (ring.rightNeighbor e)).phys.ctl := by
      calc
        ((concretePort (κ := κ) (τ := τ) hψ h2).row
          (C e) (C (ring.rightNeighbor e))).2.phys.ctl =
            (R2Coherence.row hψ (by decide : 0 < 2) h2
              (C e).phys (C (ring.rightNeighbor e)).phys).2.ctl := by
          have hx := congrArg
            (fun u : R2Coherence.Cell ψ κ τ => u.ctl) hp.2
          simpa [hostR2C] using hx
        _ = (C (ring.rightNeighbor e)).phys.ctl := hc.2
    have hOutL :
        R2Coherence.OpenControl
          ((concretePort (κ := κ) (τ := τ) hψ h2).row
            (C e) (C (ring.rightNeighbor e))).1.phys := by
      unfold R2Coherence.OpenControl
      rw [hCtlL]
      exact ⟨hLM, hLN⟩
    have hOutR :
        R2Coherence.OpenControl
          ((concretePort (κ := κ) (τ := τ) hψ h2).row
            (C e) (C (ring.rightNeighbor e))).2.phys := by
      unfold R2Coherence.OpenControl
      rw [hCtlR]
      exact ⟨hRM, hRN⟩
    intro i
    by_cases hi : i = e
    · subst i
      rw [hstep]
      simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
      exact hOutL
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        rw [hstep]
        simp only [B9FullCarrierHost.writeAtP, if_neg hs, if_pos rfl]
        exact hOutR
      · rw [hstep]
        simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]
        exact hA.2.2.1 i


/-- Outer-controller component needed by the passive closure on the
leaderless-successor branch.  This is intentionally only a named Prop here. -/
def ConcreteB7PassiveOuterNeutralPostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    FinalLeaderless D →
      ∀ i : Fin n,
        (D i).spliceRole = .none ∧
        (D i).repairPending = false ∧
        (D i).acquireTicket = false


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C


