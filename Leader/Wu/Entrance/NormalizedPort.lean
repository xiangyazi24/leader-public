import Leader.Wu.Entrance.ConcretePort
import Leader.Wu.Entrance.FinalRowNormalized
import Leader.Wu.Entrance.AdmissionCyclicRuler


set_option autoImplicit false
set_option Elab.async false


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open B9Host B9FullCarrierHost
open BirthTwoStageEscape


variable {n ψ κ τ : Nat}


/--
Shadow analogue of `concretePort`: freeze exactly the accepted complete B9
port.  The semantic change is intentionally one layer above the `Port` record,
where `rowFinalNormalized` wraps this frozen port.
-/
noncomputable def normalizedConcretePort
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    Port (κ := κ) (τ := τ) hψ h2 :=
  concretePort (κ := κ) (τ := τ) hψ h2


/--
Shadow scheduler.  Its self-edge branch is byte-for-byte `stepFinal`; only the
non-self local row is replaced by `rowFinalNormalized`.
-/
noncomputable def shadowStep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) (e : Fin n) : Config n ψ κ τ := by
  classical
  exact if ring.rightNeighbor e = e then
    if FinalGarbage hψ (C e) (C e) then
      B9FullCarrierHost.writeAtP ring C e
        (clearFinalControl (C e), C e)
    else C
  else
    B9FullCarrierHost.writeAtP ring C e
      (rowFinalNormalized hψ h2
        (normalizedConcretePort (κ := κ) (τ := τ) hψ h2)
        (C e) (C (ring.rightNeighbor e)))


/--
Step-level safety seam: if none of the three normalization lanes fires on the
served pair, the shadow scheduler is exactly the accepted `stepConcrete`.
Garbage needs no extra premise because both schedulers take the same recovery
branch before non-recovery normalization.
-/
theorem shadowStep_eq_stepConcrete_of_no_normalization
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) (e : Fin n)
    (hs : ¬ finalMalformedActiveSweep
      (C e).phys (C (ring.rightNeighbor e)).phys)
    (hr : ¬ finalMalformedActiveRelease
      (C e).phys (C (ring.rightNeighbor e)).phys)
    (hm : ¬ finalTokenFreeMixed
      (C e).phys (C (ring.rightNeighbor e)).phys) :
    shadowStep (κ := κ) (τ := τ) hψ h2 ring C e =
      stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e := by
  classical
  have hrow :
      rowFinalNormalized hψ h2
          (normalizedConcretePort (κ := κ) (τ := τ) hψ h2)
          (C e) (C (ring.rightNeighbor e)) =
        rowFinal hψ h2
          (concretePort (κ := κ) (τ := τ) hψ h2)
          (C e) (C (ring.rightNeighbor e)) := by
    unfold normalizedConcretePort
    by_cases hg : FinalGarbage hψ (C e) (C (ring.rightNeighbor e))
    · simp [rowFinalNormalized, hg]
    · exact rowFinalNormalized_eq_rowFinal_of_no_normalization
        hψ h2 (concretePort (κ := κ) (τ := τ) hψ h2)
        (C e) (C (ring.rightNeighbor e)) hg hs hr hm
  unfold shadowStep stepConcrete stepFinal
  by_cases he : ring.rightNeighbor e = e
  · simp [he]
  · rw [if_neg he, if_neg he, hrow]


/-! ## Closed ψ=3, n=6 payoff witness -/


private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring6 : DirectedRing 6 := ⟨by decide⟩


private abbrev FCell := Cell 3 3 48
private abbrev FCfg := Config 6 3 3 48


private def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


private def frozenR2C (lab : Fin 3) : P 3 3 48 :=
  ⟨literalFollower lab, ⟨.closing, .none⟩⟩


private def frozenFinalCell (lab : Fin 3) : FCell :=
  ⟨frozenR2C lab, .none, false, false⟩


private def labAt (i : Fin 6) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ h3⟩


private def concreteFrozenC : FCfg :=
  fun i => frozenFinalCell (labAt i)


/-- Auditable physical-clean clause for the concrete family. -/
def ConcreteFrozenPhysicalClean (u : FCell) : Prop :=
  let b := R2Coherence.raw u.phys
  b.leader = false ∧
    b.state = .none ∧ b.path = .bot ∧
    b.path3 = none ∧ b.write_state = .none ∧ b.write = .none


theorem concreteFrozen_clean (i : Fin 6) :
    ConcreteFrozenPhysicalClean (concreteFrozenC i) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem concreteFrozen_leaderless :
    FinalLeaderless concreteFrozenC := by
  intro i
  rfl


theorem concreteFrozen_uniformClosing (e : Fin 6) :
    finalTokenFreeUniformClosing
      (concreteFrozenC e).phys
      (concreteFrozenC (ring6.rightNeighbor e)).phys := by
  exact ⟨rfl, rfl, rfl, rfl⟩


private theorem concreteFrozen_neutral (i : Fin 6) :
    NeutralController (concreteFrozenC i) :=
  ⟨rfl, rfl, rfl⟩


theorem concreteFrozen_cyclicRuler :
    CFinalJ2Edge2.FinalCyclicRuler h3 ring6 concreteFrozenC := by
  intro a
  apply Fin.ext
  change ((a.val + 1) % 6) % 3 = (a.val % 3 + 1) % 3
  omega


private theorem concreteFrozen_noGarbage (e : Fin 6) :
    ¬ FinalGarbage h3
      (concreteFrozenC e)
      (concreteFrozenC (ring6.rightNeighbor e)) := by
  exact CFinalJ2Edge.no_finalGarbage_of_neutral_noHole h3
    (concreteFrozen_neutral e)
    (concreteFrozen_neutral (ring6.rightNeighbor e))
    (CFinalJ2Edge2.no_finalHole_of_cyclicRuler
      h3 ring6 concreteFrozenC concreteFrozen_cyclicRuler e)


private theorem ring01 :
    ring6.rightNeighbor (0 : Fin 6) = 1 := by
  decide


private theorem ring0ne :
    ring6.rightNeighbor (0 : Fin 6) ≠ 0 := by
  decide


/-- One concrete non-self service already leaves the frozen family. -/
theorem concretePsi3N6_shadow_edge0_not_identity :
    shadowStep (κ := 3) (τ := 48) h3 h23 ring6
      concreteFrozenC 0 ≠ concreteFrozenC := by
  intro hstep
  have hpairNe :
      rowFinalNormalized h3 h23
          (normalizedConcretePort (κ := 3) (τ := 48) h3 h23)
          (concreteFrozenC 0) (concreteFrozenC 1) ≠
        (concreteFrozenC 0, concreteFrozenC 1) := by
    apply rowFinalNormalized_uniformClosing_not_identity
      h3 h23
      (normalizedConcretePort (κ := 3) (τ := 48) h3 h23)
    · simpa [ring01] using concreteFrozen_noGarbage (0 : Fin 6)
    · simpa [ring01] using concreteFrozen_uniformClosing (0 : Fin 6)
  have h0 := congrFun hstep (0 : Fin 6)
  have h1 := congrFun hstep (1 : Fin 6)
  unfold shadowStep at h0 h1
  rw [if_neg ring0ne] at h0 h1
  have hL :
      (rowFinalNormalized h3 h23
        (normalizedConcretePort (κ := 3) (τ := 48) h3 h23)
        (concreteFrozenC 0) (concreteFrozenC 1)).1 =
        concreteFrozenC 0 := by
    simpa [B9FullCarrierHost.writeAtP, ring01] using h0
  have hR :
      (rowFinalNormalized h3 h23
        (normalizedConcretePort (κ := 3) (τ := 48) h3 h23)
        (concreteFrozenC 0) (concreteFrozenC 1)).2 =
        concreteFrozenC 1 := by
    simpa [B9FullCarrierHost.writeAtP, ring01] using h1
  exact hpairNe (Prod.ext hL hR)


/--
Payoff in the requested all-word-fixed shape: the concrete frozen family cannot
be fixed by every one-letter shadow service.
-/
theorem concretePsi3N6_uniformClosing_shadow_not_all_fixed :
    (∀ e : Fin 6,
      shadowStep (κ := 3) (τ := 48) h3 h23 ring6
        concreteFrozenC e = concreteFrozenC) → False := by
  intro hfixed
  exact concretePsi3N6_shadow_edge0_not_identity (hfixed 0)


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
