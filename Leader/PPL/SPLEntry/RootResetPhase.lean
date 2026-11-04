import Leader.PPL.SPLEntry.SublistBridge
import Leader.PPL.Convergence.ForcedConstructProtocol
import Leader.PPL.Elim.LiteralBridges
import Leader.PPL.Elim.PBClosure
import Leader.PPL.TransitionFacts
import Init.Omega


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false


open PPL


/-- On the Lemma-18 paper domain, a directed ring edge is not a self-edge. -/
theorem l18RootReset_rightNeighbor_ne_self
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


/-- One executable L18 P_PL-prime step projects exactly to literal row E. -/
theorem l18RootReset_pprime_projects
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) (e : Fin n) :
    PPL.Elim.viewConfig (pprimeStep ring C e) =
      PPL.literalElim ring (PPL.Elim.viewConfig C) e := by
  rw [PPL.Convergence.PrimeUnify.pprimeStep_eq_primeStep ring C e]
  exact
    PPL.Convergence.LiteralEliminationBridges.primeStep_projects
      hpsi ring C e


/-- Literal Algorithm 5 cannot create a leader at any site. -/
theorem l18RootReset_literal_no_new_leader
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C : PPL.LiteralElimConfig n)
    (e i : Fin n)
    (hi : (PPL.literalElim ring C e i).leader = true) :
    (C i).leader = true := by
  have hne :
      ring.rightNeighbor e ≠ e :=
    l18RootReset_rightNeighbor_ne_self hn3 ring e
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
theorem l18RootReset_pprime_no_new_leader
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hi : (pprimeStep ring C e i).leader = true) :
    (C i).leader = true := by
  have hproj :
      PPL.Elim.viewConfig (pprimeStep ring C e) =
        PPL.literalElim ring (PPL.Elim.viewConfig C) e :=
    l18RootReset_pprime_projects hpsi ring C e
  have hview :
      (PPL.Elim.viewConfig (pprimeStep ring C e) i).leader = true := by
    simpa [PPL.Elim.viewConfig, PPL.Elim.view4] using hi
  rw [hproj] at hview
  have hbefore :
      (PPL.Elim.viewConfig C i).leader = true :=
    l18RootReset_literal_no_new_leader
      hn3 ring (PPL.Elim.viewConfig C) e i hview
  simpa [PPL.Elim.viewConfig, PPL.Elim.view4] using hbefore


/-- CPB and the identity of the unique root survive one P_PL-prime step. -/
theorem l18RootReset_cpb_unique_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    CPB ring (pprimeStep ring C e) ∧
      L18UniqueLeaderAt (pprimeStep ring C e) root := by
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
    l18RootReset_pprime_projects hpsi ring C e
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
    l18RootReset_pprime_no_new_leader
      hn3 hpsi ring C e j hj
  have hjRoot : j = root :=
    (hUnique j).mp hjBefore
  have hrootAfter :
      (pprimeStep ring C e root).leader = true := by
    simpa [hjRoot] using hj
  refine ⟨hCPBPrime, ?_⟩
  intro i
  constructor
  · intro hi
    have hbefore :
        (C i).leader = true :=
      l18RootReset_pprime_no_new_leader
        hn3 hpsi ring C e i hi
    exact (hUnique i).mp hbefore
  · intro hir
    rw [hir]
    exact hrootAfter


/-- The predecessor edge used by phase 1 has root as responder. -/
theorem l18RootReset_predecessor_edge
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n) (root : Fin n) :
    ring.rightNeighbor (PPL.shiftLeft ring root 1) = root := by
  apply Fin.ext
  simp only [DirectedRing.rightNeighbor, PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
  by_cases hzero : root.val = 0
  · rw [hzero, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have heq : n - 1 + 1 = n := by
      omega
    rw [heq, Nat.mod_self]
  · have hpos : 0 < root.val := by
      omega
    have heq :
        root.val + n - 1 = n + (root.val - 1) := by
      omega
    rw [heq, Nat.add_mod_left]
    rw [Nat.mod_eq_of_lt (by omega : root.val - 1 < n)]
    have hsum : root.val - 1 + 1 = root.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt root.isLt]


/-- Root is distinct from its predecessor on the Lemma-18 paper domain. -/
theorem l18RootReset_root_ne_predecessor
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n) (root : Fin n) :
    root ≠ PPL.shiftLeft ring root 1 := by
  intro h
  have hself :
      ring.rightNeighbor root = root := by
    calc
      ring.rightNeighbor root =
          ring.rightNeighbor (PPL.shiftLeft ring root 1) :=
        congrArg ring.rightNeighbor h
      _ = root :=
        l18RootReset_predecessor_edge hn3 ring root
  exact
    (l18RootReset_rightNeighbor_ne_self hn3 ring root)
      hself


/-- DetermineMode leaves the responder leader bit unchanged. -/
theorem l18RootReset_determineMode_responder_leader
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    (PPL.determineMode l r).2.leader = r.leader := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals rfl


/-- A forced-Construct primed MoveToken call never changes responder.dist. -/
theorem l18RootReset_pprimeMoveToken_responder_dist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    (pprimeMoveToken hpsi kind l r).2.dist = r.dist := by
  unfold pprimeMoveToken
  dsimp only
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l { r with mode := false }
    with h | h
  · have hd :=
      congrArg
        (fun q : PPL.State psi kappa => q.dist) h
    cases kind <;>
      simpa [PPL.eraseKindTokenId, PPL.eraseKindToken] using hd
  · have hd :=
      congrArg
        (fun q : PPL.State psi kappa => q.dist) h
    cases kind <;>
      simpa [PPL.eraseKindTokenId, PPL.eraseKindToken,
        PPL.birthFields] using hd


/--
If the responder is a leader before the interaction, P_PL-prime Algorithm 2
writes zero to its distance, and both Algorithm-3 passes preserve that write.
-/
theorem l18RootReset_pprimeCreateLeader_responder_dist_zero
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hr : r.leader = true) :
    (pprimeCreateLeader hpsi l r).2.dist.val = 0 := by
  have hdet :
      (PPL.determineMode l r).2.leader = true := by
    rw [l18RootReset_determineMode_responder_leader]
    exact hr
  simp only [pprimeCreateLeader, hdet, if_pos]
  rw [l18RootReset_pprimeMoveToken_responder_dist]
  rw [l18RootReset_pprimeMoveToken_responder_dist]
  rfl


/-- Literal Algorithm 5 frames the responder distance written by Algorithms 2-3. -/
theorem l18RootReset_pprimePpl_responder_dist_zero
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hr : r.leader = true) :
    (pprimePpl hpsi l r).2.dist.val = 0 := by
  have hcreate :
      (pprimeCreateLeader hpsi l r).2.dist.val = 0 :=
    l18RootReset_pprimeCreateLeader_responder_dist_zero
      hpsi l r hr
  have hframe :=
    PPL.Elim.otherView_eliminateLeaders_right
      (pprimeCreateLeader hpsi l r).1
      (pprimeCreateLeader hpsi l r).2
  have hdist :=
    congrArg
      (fun q : PPL.Elim.OtherFields psi kappa =>
        q.dist.val) hframe
  have hppl :
      (pprimePpl hpsi l r).2.dist.val =
        (pprimeCreateLeader hpsi l r).2.dist.val := by
    simpa [pprimePpl, PPL.Elim.otherView] using hdist
  exact hppl.trans hcreate


/-- The actual singleton phase-1 P_PL-prime step resets root.dist. -/
theorem l18RootReset_selected_dist_zero
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hroot : (C root).leader = true) :
    (pprimeStep ring C (PPL.shiftLeft ring root 1) root).dist.val = 0 := by
  have hedge :
      ring.rightNeighbor (PPL.shiftLeft ring root 1) = root :=
    l18RootReset_predecessor_edge hn3 ring root
  have hne :
      root ≠ PPL.shiftLeft ring root 1 :=
    l18RootReset_root_ne_predecessor hn3 ring root
  have hpair :
      (pprimePpl hpsi
          (C (PPL.shiftLeft ring root 1))
          (C root)).2.dist.val = 0 :=
    l18RootReset_pprimePpl_responder_dist_zero
      hpsi
      (C (PPL.shiftLeft ring root 1))
      (C root)
      hroot
  simpa [pprimeStep, pprimeProtocol,
    PopulationProtocol.step, pprimeTransition,
    hpsi, hedge, hne] using hpair


theorem l18RootResetPhase_proved :
    L18RootResetPhase := by
  unfold L18RootResetPhase
  intro n psi kappa hn3 hpsi ring root C
  intro hCPB hUnique
  have hstate :
      CPB ring
          (pprimeStep ring C
            (PPL.shiftLeft ring root 1)) ∧
        L18UniqueLeaderAt
          (pprimeStep ring C
            (PPL.shiftLeft ring root 1))
          root :=
    l18RootReset_cpb_unique_step
      hn3 hpsi ring root C
      (PPL.shiftLeft ring root 1)
      hCPB hUnique
  have hroot :
      (C root).leader = true :=
    (hUnique root).mpr rfl
  have hdist :
      (pprimeStep ring C
        (PPL.shiftLeft ring root 1) root).dist.val = 0 :=
    l18RootReset_selected_dist_zero
      hn3 hpsi ring root C hroot
  have hresult :
      CPB ring
          (pprimeStep ring C
            (PPL.shiftLeft ring root 1)) ∧
        L18UniqueLeaderAt
          (pprimeStep ring C
            (PPL.shiftLeft ring root 1))
          root ∧
        (pprimeStep ring C
          (PPL.shiftLeft ring root 1) root).dist.val = 0 :=
    ⟨hstate.1, hstate.2, hdist⟩
  simpa [l18RootResetWord, runPPrime] using hresult


end PPL.Convergence.L18


#print axioms PPL.Convergence.L18.l18RootResetPhase_proved
