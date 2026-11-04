import Leader.Wu.Splice.RecoveryGate

set_option autoImplicit false
set_option Elab.async false

namespace B9RecoveryJ3Direct

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableHost B9SpliceV10hControllerRowsSafe
open B9ControllerRecovery B9FullCarrierRows B9SpliceTableV10g
open BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n ψ κ τ : Nat}

abbrev FCell (ψ κ τ : Nat) := FinalCandidateR2C.Cell ψ κ τ
abbrev FConfig (n ψ κ τ : Nat) := FinalCandidateR2C.Config n ψ κ τ

section GarbageProjection

attribute [local irreducible]
  B9FullCarrierRows.fullRowPort concretePort

@[simp] private theorem oldCell_clearFinalControl_direct
    (u : FCell ψ κ τ) :
    oldCell (clearFinalControl u) = clearControlV6 (oldCell u) := rfl

@[simp] private theorem oldCell_coverFinal_left_direct
    (l r : FCell ψ κ τ) :
    oldCell (coverFinal l r).1 = (coverWrite (oldCell l) (oldCell r)).1 := rfl

@[simp] private theorem oldCell_coverFinal_right_direct
    (l r : FCell ψ κ τ) :
    oldCell (coverFinal l r).2 = (coverWrite (oldCell l) (oldCell r)).2 := rfl

private theorem oldConfig_writeAtP_direct
    (ring : DirectedRing n) (C : FConfig n ψ κ τ) (e : Fin n)
    (w : FCell ψ κ τ × FCell ψ κ τ) :
    oldConfig (B9FullCarrierHost.writeAtP ring C e w) =
      B9SpliceV10hControllerRowsSafe.writeAt ring (oldConfig C) e
        (oldCell w.1, oldCell w.2) := by
  funext i
  by_cases hi : i = e
  · simp [oldConfig, B9FullCarrierHost.writeAtP,
      B9SpliceV10hControllerRowsSafe.writeAt, hi]
  · by_cases hj : i = ring.rightNeighbor e
    · by_cases hs : ring.rightNeighbor e = e
      · exact (hi (hj.trans hs)).elim
      · simp [oldConfig, B9FullCarrierHost.writeAtP,
          B9SpliceV10hControllerRowsSafe.writeAt, hi, hj, hs]
    · simp [oldConfig, B9FullCarrierHost.writeAtP,
        B9SpliceV10hControllerRowsSafe.writeAt, hi, hj]

/-- Only the five recovery guards are unfolded.  The RHS is first routed
through the public exact-old recovery representative. -/
private theorem recoverPair_old_to_rowRecover_direct
    (oldHost : HostRow (OldPhys ψ κ τ)) (hψ : 0 < ψ)
    (l r : FCell ψ κ τ) (hg : FinalGarbage hψ l r) :
    (oldCell (recoverPair hψ l r).1, oldCell (recoverPair hψ l r).2) =
      rowRecoverH oldHost hψ (oldCell l) (oldCell r) := by
  classical
  have href := B9FullCarrierRows.rowRecoverOldP_toOld oldHost hψ
    (B9FullCarrierHost.oldToP (oldCell l))
    (B9FullCarrierHost.oldToP (oldCell r))
  simp only [B9FullCarrierHost.toOld_oldToP] at href
  change Garbage hψ (oldCell l) (oldCell r) at hg
  calc
    (oldCell (recoverPair hψ l r).1,
      oldCell (recoverPair hψ l r).2) =
        (B9FullCarrierHost.toOld B9FullCarrierHost.oldLaws
            (B9FullCarrierRows.rowRecoverOldP oldHost hψ
              (B9FullCarrierHost.oldToP (oldCell l))
              (B9FullCarrierHost.oldToP (oldCell r))).1,
         B9FullCarrierHost.toOld B9FullCarrierHost.oldLaws
            (B9FullCarrierRows.rowRecoverOldP oldHost hψ
              (B9FullCarrierHost.oldToP (oldCell l))
              (B9FullCarrierHost.oldToP (oldCell r))).2) := by
      by_cases hL : BadTicket (oldCell l)
      · simp [recoverPair, FinalBadTicket, B9FullCarrierRows.rowRecoverOldP,
          B9FullCarrierRows.exactOldRowP, rowRecoverH, hL]
      · by_cases hR : BadTicket (oldCell r)
        · simp [recoverPair, FinalBadTicket, B9FullCarrierRows.rowRecoverOldP,
            B9FullCarrierRows.exactOldRowP, rowRecoverH, hL, hR]
        · by_cases hB : BadBacking (oldCell l) (oldCell r)
          · simp [recoverPair, FinalBadTicket, FinalBadBacking,
              B9FullCarrierRows.rowRecoverOldP,
              B9FullCarrierRows.exactOldRowP, rowRecoverH, hL, hR, hB]
          · have hH : Hole hψ (oldCell l) (oldCell r) := by
              rcases hg with (a | a | a) | a
              · exact (hL a).elim
              · exact (hR a).elim
              · exact (hB a).elim
              · exact a
            simp [recoverPair, FinalBadTicket, FinalBadBacking, FinalHole,
              B9FullCarrierRows.rowRecoverOldP,
              B9FullCarrierRows.exactOldRowP, rowRecoverH,
              hL, hR, hB, hH]
    _ = rowRecoverH oldHost hψ (oldCell l) (oldCell r) := href

private theorem oldConfig_stepFinal_garbage_direct
    (oldHost : HostRow (OldPhys ψ κ τ))
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : FConfig n ψ κ τ) (e : Fin n)
    (hg : FinalGarbage hψ (C e) (C (ring.rightNeighbor e))) :
    oldConfig (stepFinal hψ h2 port ring C e) =
      stepRecover oldHost hψ ring (oldConfig C) e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hg0 : FinalGarbage hψ (C e) (C e) := by simpa [hs] using hg
    have hgo : Garbage hψ ((oldConfig C) e) ((oldConfig C) e) := hg0
    unfold stepFinal stepRecover
    rw [if_pos hs, if_pos hg0, if_pos hs, if_pos hgo,
      oldConfig_writeAtP_direct]
    change
      B9SpliceV10hControllerRowsSafe.writeAt ring (oldConfig C) e
          (clearControlV6 (oldCell (C e)), oldCell (C e)) =
        B9SpliceV10hControllerRowsSafe.writeAt ring (oldConfig C) e
          (clearControlV6 (oldCell (C e)), oldCell (C e))
    rfl
  · have hfa : finalAction hψ h2 port
        (C e) (C (ring.rightNeighbor e)) = .recovery := by
      simp [finalAction, hg]
    have hrow : rowFinal hψ h2 port
        (C e) (C (ring.rightNeighbor e)) =
        recoverPair hψ (C e) (C (ring.rightNeighbor e)) := by
      unfold rowFinal
      rw [hfa]
    unfold stepFinal stepRecover
    rw [if_neg hs, if_neg hs, hrow, oldConfig_writeAtP_direct]
    apply congrArg (fun w =>
      B9SpliceV10hControllerRowsSafe.writeAt ring (oldConfig C) e w)
    exact recoverPair_old_to_rowRecover_direct oldHost hψ
      (C e) (C (ring.rightNeighbor e)) hg

/-- Exact projection needed by the direct J3 proof.  The frozen port stays
opaque because garbage selects recovery before any port action/row is read. -/
theorem stepConcrete_oldConfig_eq_stepRecover_of_finalGarbage
    (oldHost : HostRow (OldPhys ψ κ τ))
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FConfig n ψ κ τ) (e : Fin n)
    (hg : FinalGarbage hψ (C e) (C (ring.rightNeighbor e))) :
    oldConfig (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) =
      stepRecover oldHost hψ ring (oldConfig C) e := by
  simpa only [stepConcrete] using
    (oldConfig_stepFinal_garbage_direct
      (κ := κ) (τ := τ) oldHost hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring C e hg)

end GarbageProjection

private theorem localDanger_iff_at_direct
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ) (e : Fin n) :
    LocalDanger hψ (C e) (C (ring.rightNeighbor e)) ↔
      PreparedDangerAt hψ ring
        (B9SpliceControllerR1TableV6.projectV6 C) e := by
  rfl

private theorem pairCovered_iff_at_direct
    (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ) (e : Fin n) :
    PairCovered (C e) (C (ring.rightNeighbor e)) ↔
      ProtectedSpliceEdgeV7g ring C e := by
  rfl

private theorem safe_of_no_garbage_direct
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ)
    (hN : ∀ e, ¬ Garbage hψ (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hψ ring C := by
  classical
  constructor
  · intro e hd
    have hld : LocalDanger hψ (C e) (C (ring.rightNeighbor e)) :=
      (localDanger_iff_at_direct hψ ring C e).mpr hd
    by_cases hc : PairCovered (C e) (C (ring.rightNeighbor e))
    · exact (pairCovered_iff_at_direct ring C e).mp hc
    · exact False.elim (hN e (Or.inr ⟨hld, hc⟩))
  · constructor
    · intro i ht
      by_cases hs :
          ReservedFrontHoldGuard (C i).carrier ∨ HostFenceShapeV7 (C i)
      · exact hs
      · exact False.elim (hN i (Or.inl (Or.inl ⟨ht, hs⟩)))
    · intro i hr hp
      by_cases hb :
          ReservedFrontHoldGuard (C (ring.rightNeighbor i)).carrier ∧
            (C (ring.rightNeighbor i)).acquireTicket = false
      · exact hb
      · exact False.elim
          (hN i (Or.inl (Or.inr (Or.inr ⟨⟨hr, hp⟩, hb⟩))))

private theorem garbage_exists_of_not_safe_direct
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ)
    (hS : ¬ SpliceSafeV7g hψ ring C) :
    ∃ e, Garbage hψ (C e) (C (ring.rightNeighbor e)) := by
  classical
  by_cases h : ∃ e, Garbage hψ (C e) (C (ring.rightNeighbor e))
  · exact h
  · exact False.elim (hS (safe_of_no_garbage_direct hψ ring C
      (fun e hg => h ⟨e, hg⟩)))

noncomputable def finalRecoveryRankJ3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : FConfig n ψ κ τ) : Nat :=
  recoveryRank hψ ring (oldConfig C)

theorem finalRecoveryRankJ3_le
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : FConfig n ψ κ τ) :
    finalRecoveryRankJ3 hψ ring C ≤ RecoveryB n := by
  unfold finalRecoveryRankJ3
  simpa [RecoveryB] using
    (recoveryRank_le_six_mul hψ ring (oldConfig C))

/-- Every non-target final state has a concrete scheduler letter that strictly
lowers the accepted old stopped rank.  It is chosen to be a garbage edge. -/
theorem finalRecoveryRankJ3_descent
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FConfig n ψ κ τ)
    (hnot : ¬ FinalRecoveryTarget hψ ring C) :
    ∃ e : Fin n,
      finalRecoveryRankJ3 hψ ring
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) <
        finalRecoveryRankJ3 hψ ring C := by
  have hnotOld : ¬ RecoveryTarget hψ ring (oldConfig C) :=
    fun h => hnot
      ((B9RecoveryGate.finalRecoveryTarget_iff_oldConfig hψ ring C).mpr h)
  have hns : ¬ SpliceSafeV7g hψ ring (oldConfig C) :=
    fun hS => hnotOld (Or.inl hS)
  obtain ⟨e, hg⟩ :=
    garbage_exists_of_not_safe_direct hψ ring (oldConfig C) hns
  have hgF : FinalGarbage hψ
      (C e) (C (ring.rightNeighbor e)) := hg
  let host := B9Host.r1Host (kappa := κ) (tau := τ) hψ h2
  have hproj := stepConcrete_oldConfig_eq_stepRecover_of_finalGarbage
    (κ := κ) (τ := τ) host hψ h2 ring C e hgF
  have hdrop := recoveryRank_drop_active
    host hψ ring (oldConfig C) e hnotOld hg
  refine ⟨e, ?_⟩
  unfold finalRecoveryRankJ3
  rw [hproj]
  exact hdrop

theorem finalRecovery_first_hit_mass_j3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FConfig n ψ κ τ) :
    RecoveryQ n * avoidCount
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
        (fun _ : FConfig n ψ κ τ => True)
        (FinalRecoveryTarget hψ ring) C (RecoveryB n) ≤
      (RecoveryQ n - 1) * n ^ RecoveryB n := by
  classical
  let B := RecoveryB n
  have hRank : finalRecoveryRankJ3 hψ ring C ≤ B := by
    dsimp only [B]
    exact finalRecoveryRankJ3_le hψ ring C
  by_cases hT : FinalRecoveryTarget hψ ring C
  · have hz := avoidCount_zero_of
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      (fun _ : FConfig n ψ κ τ => True)
      (FinalRecoveryTarget hψ ring) C (fun h => h.2 hT) B
    unfold RecoveryQ
    change n ^ B * avoidCount
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      (fun _ : FConfig n ψ κ τ => True)
      (FinalRecoveryTarget hψ ring) C B ≤ (n ^ B - 1) * n ^ B
    rw [hz]
    simp
  · have hlt := B9ControllerRecovery.avoidCount_lt_pow_of_rank_descent
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      (FinalRecoveryTarget hψ ring)
      (finalRecoveryRankJ3 hψ ring) ring.hn
      (fun X hX => finalRecoveryRankJ3_descent
        (κ := κ) (τ := τ) hψ h2 ring X hX)
      B C hRank hT
    have hle : avoidCount
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
        (fun _ : FConfig n ψ κ τ => True)
        (FinalRecoveryTarget hψ ring) C B ≤ n ^ B - 1 := by
      exact Nat.le_sub_one_of_lt hlt
    unfold RecoveryQ
    change n ^ B * avoidCount
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      (fun _ : FConfig n ψ κ τ => True)
      (FinalRecoveryTarget hψ ring) C B ≤ (n ^ B - 1) * n ^ B
    calc
      n ^ B * avoidCount
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
          (fun _ : FConfig n ψ κ τ => True)
          (FinalRecoveryTarget hψ ring) C B
          ≤ n ^ B * (n ^ B - 1) := Nat.mul_le_mul_left _ hle
      _ = (n ^ B - 1) * n ^ B := Nat.mul_comm _ _

/-- J3 closes without whole-port normalization or exact trajectory commute. -/
theorem c2J3OldToFinalRecoveryMass_direct
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    B9RecoveryGate.C2J3OldToFinalRecoveryMass
      (kappa := κ) (tau := τ) hψ h2 ring := by
  unfold B9RecoveryGate.C2J3OldToFinalRecoveryMass
  intro _hHold _hCompletion C _hPassive _hOld
  unfold B9RecoveryGate.C2FinalRecoveryMass
  dsimp only
  exact finalRecovery_first_hit_mass_j3
    (κ := κ) (τ := τ) hψ h2 ring C

end B9RecoveryJ3Direct
