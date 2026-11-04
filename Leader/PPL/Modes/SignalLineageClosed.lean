import Leader.PPL.Modes.SignalLineageLocal
import Leader.PPL.Modes.SignalLineageProof
import Leader.PPL.TransitionFacts

namespace PPL.Modes.SignalLineage

set_option autoImplicit false
set_option Elab.async false

/-! The remaining global ghost-lineage clauses follow from the literal
two-site owner update and the DetermineMode signal/hits projection. -/

/-- A leader arm replaces, rather than revives, the old tag at its site. -/
theorem rearmTerminatesPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) :
    RearmTerminatesPreserved (psi := psi) (kappa := kappa) ring := by
  intro g e _ hself hwf hlead t he k
  by_cases hke : k = e
  · subst k
    simp [ghostStep_initiator_owner_none]
  by_cases hkj : k = ring.rightNeighbor e
  · subst k
    intro hk
    have hwin := responder_winner_of_some ring g e hself t hk
    by_cases hcmp :
        (g.physical (ring.rightNeighbor e)).signalR.val ≤ armedTTL g e
    · have ht : freshTag g e = t := by
        have hs : some (freshTag g e) = some t := by
          simpa [winnerOwner, hcmp, armedOwner, hlead] using hwin
        exact Option.some.inj hs
      have hnot := freshTag_not_preowned g e hwf.2.2 e
      exact hnot (by simpa [ht] using he)
    · have hj : g.owner (ring.rightNeighbor e) = some t := by
        simpa [winnerOwner, hcmp] using hwin
      have heq := hwf.2.1 e (ring.rightNeighbor e) t he hj
      exact hself heq.symm
  · rw [ghostStep_owner_other ring g e k hke hkj]
    intro hk
    have heq := hwf.2.1 e k t he hk
    exact hke heq.symm

/-- In a leaderless configuration, every surviving tag was already owned
before the step and therefore traces to the designated start state. -/
theorem leaderlessCoveragePreserved {n psi kappa : Nat}
    (ring : DirectedRing n) :
    LeaderlessCoveragePreserved (psi := psi) (kappa := kappa) ring := by
  intro start g e _ hself _ hfrom hleader
  intro k t hk
  by_cases hke : k = e
  · subst k
    have hbad : False := by
      simpa [ghostStep_initiator_owner_none] using hk
    exact hbad.elim
  by_cases hkj : k = ring.rightNeighbor e
  · subst k
    have hwin := responder_winner_of_some ring g e hself t hk
    rcases winnerOwner_some_cases g e (ring.rightNeighbor e) t hwin with hf | ho
    · have hfalse := hleader e
      rw [hfalse] at hf
      cases hf.1
    · rcases ho with he | hj
      · exact hfrom e t he
      · exact hfrom (ring.rightNeighbor e) t hj
  · have hold : g.owner k = some t := by
      rw [← ghostStep_owner_other ring g e k hke hkj]
      exact hk
    exact hfrom k t hold

/-- A nonleader's tag can move to the responder only when its own signal
wins the maximum-TTL comparison; DetermineMode resets that winner's hits. -/
theorem movedWinnerHitsResetPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) :
    MovedWinnerHitsResetPreserved (psi := psi) (kappa := kappa) ring := by
  intro g e hpsi hself hwf hlead t he hnew
  let j := ring.rightNeighbor e
  have hwin := responder_winner_of_some ring g e hself t hnew
  have hcmp : (g.physical j).signalR.val ≤ armedTTL g e := by
    by_cases hc : (g.physical j).signalR.val ≤ armedTTL g e
    · exact hc
    · have hj : g.owner j = some t := by
        dsimp [j] at hc ⊢
        simpa [winnerOwner, hc] using hwin
      have heq := hwf.2.1 e j t he hj
      exact False.elim (hself heq.symm)
  have hpos : 0 < (g.physical e).signalR.val := by
    by_cases hz : (g.physical e).signalR.val = 0
    · have hn := (hwf.1 e).2 hz
      rw [hn] at he
      cases he
    · omega
  have hleft :
      0 < armedSignalVal (g.physical e) ∧
      (g.physical j).signalR.val ≤ armedSignalVal (g.physical e) := by
    constructor
    · simpa [armedSignalVal, hlead] using hpos
    · simpa [armedTTL, armedSignalVal, hlead] using hcmp
  have hd := determineModeSignalProjection hpsi
    (g.physical e) (g.physical j)
  have hs := step_signal_projection_of_stable
    postDetermineModeSignalStable hpsi ring g.physical e hself
  dsimp only at hd hs
  rcases hd.2.2 with hz | hl | hr
  · omega
  · change (step ring g.physical e j).hits.val = 0
    rw [hs.2.2.2]
    exact hl.2.2.2
  · omega

private theorem old_owner_signal_pos {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) (hwf : LineageWellFormed g)
    (i : Fin n) (t : SignalTag n) (hown : g.owner i = some t) :
    0 < (g.physical i).signalR.val := by
  by_cases hz : (g.physical i).signalR.val = 0
  · have hn := (hwf.1 i).2 hz
    rw [hn] at hown
    cases hown
  · omega

/-- A surviving old tag keeps its previous TTL away from the interaction;
at the responder it either keeps the left winner's TTL or retains/decrements
the right winner's TTL. Fresh leader arms cannot equal an issued old tag. -/
theorem tagTTLNonincreasePreserved {n psi kappa : Nat}
    (ring : DirectedRing n) :
    TagTTLNonincreasePreserved (psi := psi) (kappa := kappa) ring := by
  intro g e hpsi hself hwf i k t hown hnew
  let j := ring.rightNeighbor e
  by_cases hke : k = e
  · subst k
    have hbad : False := by
      simpa [ghostStep_initiator_owner_none] using hnew
    exact hbad.elim
  by_cases hkj : k = j
  · subst k
    have hwin := responder_winner_of_some ring g e hself t hnew
    have hd := determineModeSignalProjection hpsi
      (g.physical e) (g.physical j)
    have hs := step_signal_projection_of_stable
      postDetermineModeSignalStable hpsi ring g.physical e hself
    dsimp only at hd hs
    change (step ring g.physical e j).signalR.val ≤
      (g.physical i).signalR.val
    rw [hs.2.2.1]
    by_cases hcmp : (g.physical j).signalR.val ≤ armedTTL g e
    · by_cases hlead : (g.physical e).leader = true
      · have ht : freshTag g e = t := by
          have hw : some (freshTag g e) = some t := by
            dsimp [j] at hcmp
            simpa [winnerOwner, hcmp, armedOwner, hlead] using hwin
          exact Option.some.inj hw
        have hnot := freshTag_not_preowned g e hwf.2.2 i
        exact False.elim (hnot (by simpa [ht] using hown))
      · have he : g.owner e = some t := by
          dsimp [j] at hcmp
          simpa [winnerOwner, hcmp, armedOwner, hlead] using hwin
        have hie := hwf.2.1 i e t hown he
        subst i
        have hp := old_owner_signal_pos g hwf e t he
        have hcmp' : (g.physical j).signalR.val ≤
            armedSignalVal (g.physical e) := by
          simpa [armedTTL, armedSignalVal, hlead] using hcmp
        rcases hd.2.2 with hz | hl | hr
        · have ha : 0 < armedSignalVal (g.physical e) := by
            simpa [armedSignalVal, hlead] using hp
          omega
        · rw [hl.2.2.1]
          simpa [armedSignalVal, hlead]
        · omega
    · have hj : g.owner j = some t := by
        dsimp [j] at hcmp ⊢
        simpa [winnerOwner, hcmp] using hwin
      have hij := hwf.2.1 i j t hown hj
      subst i
      have hp := old_owner_signal_pos g hwf j t hj
      have hcmp' : armedSignalVal (g.physical e) <
          (g.physical j).signalR.val := by
        simpa [armedTTL, armedSignalVal] using (show armedTTL g e <
          (g.physical j).signalR.val by omega)
      rcases hd.2.2 with hz | hl | hr
      · omega
      · omega
      · rw [hr.2.1]
        split <;> omega
  · have hold : g.owner k = some t := by
      rw [← ghostStep_owner_other ring g e k hke hkj]
      exact hnew
    have hik := hwf.2.1 i k t hown hold
    subst i
    change (step ring g.physical e k).signalR.val ≤
      (g.physical k).signalR.val
    rw [(step_signal_hits_away ring g.physical e k hke hkj).1]
    exact Nat.le_refl _

/-- The full ownership interface now follows from the four lineage clauses
above, the local owner/signal projection, and the accepted ghost invariants. -/
theorem signalLineageOwnership {n psi kappa : Nat}
    (ring : DirectedRing n) :
    SignalLineageOwnership (psi := psi) (kappa := kappa) ring := by
  exact ⟨ownerMatchesPreserved ring,
    noCloningPreserved ring,
    issuedPreserved ring,
    maxTTLClause_holds ring,
    rearmTerminatesPreserved ring,
    tagTTLNonincreasePreserved ring,
    movedWinnerHitsResetPreserved ring,
    leaderlessCoveragePreserved ring⟩

#print axioms PPL.Modes.SignalLineage.rearmTerminatesPreserved
#print axioms PPL.Modes.SignalLineage.leaderlessCoveragePreserved
#print axioms PPL.Modes.SignalLineage.movedWinnerHitsResetPreserved
#print axioms PPL.Modes.SignalLineage.tagTTLNonincreasePreserved
#print axioms PPL.Modes.SignalLineage.signalLineageOwnership

end PPL.Modes.SignalLineage
