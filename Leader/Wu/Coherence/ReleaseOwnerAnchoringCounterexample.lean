import Leader.Wu.Coherence.ReachableReleaseOwnerAdjacentRoot
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableReleaseOwner2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachableReleaseOwner


namespace ProbePsi2AdjacentRoots


private theorem hψ : 0 < 2 := by decide
private theorem h2 : 2 ≤ 2 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩


private def literal (lab : Fin 2) (leader : Bool := false) :
    R2.Cell 2 2 32 :=
  let seed := WriterProducerRegression.clean hψ (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 2 2 := {
    b with
      leader := leader
      shield := leader
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
  ⟨⟨⟨b', false⟩, 32⟩, 0⟩


private def preQ : FC 3 2 2 32 := fun i =>
  match i.val with
  | 0 => ⟨literal 0 true,  ⟨.open, .none⟩⟩
  | 1 => ⟨literal 1 false, ⟨.open, .none⟩⟩
  | _ => ⟨literal 0 false, ⟨.open, .none⟩⟩


private def Q0 : FC 3 2 2 32 := quarantineInitV31 preQ
private def Q1 := stepV3 hψ h2 ring3 Q0 0
private def Q2 := stepV3 hψ h2 ring3 Q1 0
private def Q3 := stepV3 hψ h2 ring3 Q2 0
private def Q4 := stepV3 hψ h2 ring3 Q3 0
private def Q5 := stepV3 hψ h2 ring3 Q4 0
private def Q6 := stepV3 hψ h2 ring3 Q5 0


theorem q6_pending_owner0 : PendingOpenROwnerV31 ring3 Q6 0 := by
  unfold PendingOpenROwnerV31
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · decide +kernel


theorem q6_adjacent_roots :
    atRootB (Q6 2) = true ∧ atRootB (Q6 0) = true ∧
    ring3.rightNeighbor 2 = 0 := by
  decide +kernel


theorem q6_incoming_window :
    R2Coherence.groupStart ring3 (eraseCfgV3 Q6) 2 = 2 ∧
    R2Coherence.groupPos ring3 (eraseCfgV3 Q6) 2 1 = 0 := by
  decide +kernel


theorem q6_not_incomingWindowAnchored :
    ¬ ReleasePsi2IncomingWindowAnchoredV31 ring3 Q6 0 := by
  unfold ReleasePsi2IncomingWindowAnchoredV31
  intro h
  have hs := h 2 q6_incoming_window.2
  have h20 : (2 : Fin 3) = 0 := q6_incoming_window.1.symm.trans hs
  exact (by decide : (2 : Fin 3) ≠ 0) h20


theorem q6_predecessor_mainClear : MainClearV3 (Q6 2) := by
  decide +kernel


theorem q6_incomingOverlapMainClear :
    ReleasePsi2IncomingOverlapMainClearV31 ring3 Q6 0 := by
  unfold ReleasePsi2IncomingOverlapMainClearV31
  intro j hhit hne
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hj with h0 | h1 | h2
  · have hj0 : j = (0 : Fin 3) := Fin.ext h0
    subst j
    have hn :
        R2Coherence.groupPos ring3 (eraseCfgV3 Q6) 0 1 ≠ 0 := by
      decide +kernel
    exact False.elim (hn hhit)
  · have hj1 : j = (1 : Fin 3) := Fin.ext h1
    subst j
    have hn :
        R2Coherence.groupPos ring3 (eraseCfgV3 Q6) 1 1 ≠ 0 := by
      decide +kernel
    exact False.elim (hn hhit)
  · have hj2 : j = (2 : Fin 3) := Fin.ext h2
    subst j
    rw [q6_incoming_window.1]
    exact q6_predecessor_mainClear


theorem q6_adjacentRootPredecessorMainClear :
    AdjacentRootPredecessorMainClearPsi2V31 ring3 Q6 := by
  unfold AdjacentRootPredecessorMainClearPsi2V31
  intro p hp hnext
  have hpc : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 := by omega
  rcases hpc with h0 | h1 | h2
  · have hp0 : p = (0 : Fin 3) := Fin.ext h0
    subst p
    have hn :
        atRootB (Q6 (ring3.rightNeighbor (0 : Fin 3))) ≠ true := by
      decide +kernel
    exact False.elim (hn hnext)
  · have hp1 : p = (1 : Fin 3) := Fin.ext h1
    subst p
    have hn : atRootB (Q6 (1 : Fin 3)) ≠ true := by
      decide +kernel
    exact False.elim (hn hp)
  · have hp2 : p = (2 : Fin 3) := Fin.ext h2
    subst p
    exact q6_predecessor_mainClear


end ProbePsi2AdjacentRoots
end R2CoherenceV31ReachableReleaseOwner2
