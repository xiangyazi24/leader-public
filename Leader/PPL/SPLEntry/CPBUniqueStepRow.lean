import Leader.PPL.SPLEntry.SublistBridge
import Leader.PPL.Convergence.ForcedConstructProtocol
import Leader.PPL.Elim.LiteralBridges
import Leader.PPL.Elim.PBClosure


namespace PPL.Convergence.L18Bridge


set_option autoImplicit false
set_option Elab.async false


open PPL
open PPL.Convergence.L18


/-- On the Lemma-18 paper domain, the scheduled directed edge is not a self-edge. -/
theorem l18RightNeighbor_ne_self
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) :
    Ne (ring.rightNeighbor e) e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


/-- One P_PL-prime step projects exactly to one literal row-E step. -/
theorem l18PPrimeStep_projects
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) (e : Fin n) :
    PPL.Elim.viewConfig (pprimeStep ring C e) =
      PPL.literalElim ring (PPL.Elim.viewConfig C) e := by
  rw [PPL.Convergence.PrimeUnify.pprimeStep_eq_primeStep ring C e]
  exact
    PPL.Convergence.LiteralEliminationBridges.primeStep_projects
      hpsi ring C e


/-- Literal row E cannot create a new leader at any site. -/
theorem l18LiteralElim_no_new_leader
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (e i : Fin n)
    (hi : (PPL.literalElim ring C e i).leader = true) :
    (C i).leader = true := by
  have hne : Ne (ring.rightNeighbor e) e :=
    l18RightNeighbor_ne_self hn3 ring e
  by_cases hie : i = e
  · subst i
    simpa [PPL.literalElim, PPL.Convergence.LDLocal.stepE,
      PopulationProtocol.step, PPL.Elim.protocolE] using hi
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      cases hpre : (C (ring.rightNeighbor e)).leader with
      | true =>
          rfl
      | false =>
          have hfalse :
              (PPL.literalElim ring C e
                (ring.rightNeighbor e)).leader = false := by
            simpa [PPL.literalElim, PPL.Convergence.LDLocal.stepE,
              PopulationProtocol.step, PPL.Elim.protocolE, hne] using
              (PPL.Elim.rowE_right_leader_false_of_false
                (C e) (C (ring.rightNeighbor e)) hpre)
          rw [hi] at hfalse
          cases hfalse
    · simpa [PPL.literalElim, PPL.Convergence.LDLocal.stepE,
        PopulationProtocol.step, hie, hir] using hi


/-- P_PL-prime therefore cannot create a new leader either. -/
theorem l18PPrimeStep_no_new_leader
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hi : (pprimeStep ring C e i).leader = true) :
    (C i).leader = true := by
  have hproj :
      PPL.Elim.viewConfig (pprimeStep ring C e) =
        PPL.literalElim ring (PPL.Elim.viewConfig C) e :=
    l18PPrimeStep_projects hpsi ring C e
  have hview :
      (PPL.Elim.viewConfig (pprimeStep ring C e) i).leader = true := by
    simpa [PPL.Elim.viewConfig, PPL.Elim.view4] using hi
  rw [hproj] at hview
  have hbefore :
      (PPL.Elim.viewConfig C i).leader = true :=
    l18LiteralElim_no_new_leader
      hn3 ring (PPL.Elim.viewConfig C) e i hview
  simpa [PPL.Elim.viewConfig, PPL.Elim.view4] using hbefore


/-- The L18 insertion-frame state row: CPB and the same unique root survive
one arbitrary P_PL-prime interaction. -/
theorem l18CPBUniqueStepRow_proved :
    L18CPBUniqueStepRow := by
  unfold L18CPBUniqueStepRow
  intro n psi kappa hn3 hpsi ring root C e hCPB hUnique
  have hPB :
      PPL.Elim.PB ring (PPL.Elim.viewConfig C) :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge
      ring C).mp hCPB
  have hPBStep :
      PPL.Elim.PB ring
        (PPL.literalElim ring (PPL.Elim.viewConfig C) e) := by
    simpa [PPL.literalElim] using
      (PPL.Convergence.LDLocal.pbStepClosure
        ring (PPL.Elim.viewConfig C) e hPB)
  have hproj :
      PPL.Elim.viewConfig (pprimeStep ring C e) =
        PPL.literalElim ring (PPL.Elim.viewConfig C) e :=
    l18PPrimeStep_projects hpsi ring C e
  have hPBPrime :
      PPL.Elim.PB ring
        (PPL.Elim.viewConfig (pprimeStep ring C e)) := by
    rw [hproj]
    exact hPBStep
  have hCPBPrime :
      CPB ring (pprimeStep ring C e) :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge
      ring (pprimeStep ring C e)).mpr hPBPrime
  rcases hPBPrime.1 with ⟨j, hjView⟩
  have hj :
      (pprimeStep ring C e j).leader = true := by
    simpa [PPL.Elim.viewConfig, PPL.Elim.view4] using hjView
  have hjBefore :
      (C j).leader = true :=
    l18PPrimeStep_no_new_leader
      hn3 hpsi ring C e j hj
  have hjRoot : j = root :=
    (hUnique j).mp hjBefore
  have hrootAfter :
      (pprimeStep ring C e root).leader = true := by
    simpa [hjRoot] using hj
  refine And.intro hCPBPrime ?_
  intro i
  constructor
  · intro hi
    have hbefore :
        (C i).leader = true :=
      l18PPrimeStep_no_new_leader
        hn3 hpsi ring C e i hi
    exact (hUnique i).mp hbefore
  · intro hir
    rw [hir]
    exact hrootAfter


end PPL.Convergence.L18Bridge


#print axioms PPL.Convergence.L18Bridge.l18RightNeighbor_ne_self
#print axioms PPL.Convergence.L18Bridge.l18PPrimeStep_projects
#print axioms PPL.Convergence.L18Bridge.l18LiteralElim_no_new_leader
#print axioms PPL.Convergence.L18Bridge.l18PPrimeStep_no_new_leader
#print axioms PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
