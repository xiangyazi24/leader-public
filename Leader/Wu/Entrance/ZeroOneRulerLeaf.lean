import Leader.Wu.Entrance.SanitationRelative
import Leader.Wu.Entrance.LocalRulerExceptional

set_option autoImplicit false
set_option Elab.async false

namespace B6ZeroOneRulerLeaf

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2

variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}

/-- The one extra ruler service required by the relative recut. -/
def zeroOneWord (ring : DirectedRing n) (I : Interval ring) :
    List (Fin n) :=
  [cell ring I.first 0]

@[simp] theorem zeroOneWord_length
    (ring : DirectedRing n) (I : Interval ring) :
    (zeroOneWord ring I).length = 1 := by
  simp [zeroOneWord]

private theorem comparisonClean_prepare_eq
    (hpsi : 0 < psi) (q : ExpiringAgentState psi kappa tau)
    (hq : ComparisonCleanCell q) :
    prepareExpiringDisposal hpsi q = q := by
  have hclear :
      pendingTerminalDisposal hpsi q.core.erase.core = false := by
    simp only [ComparisonCleanCell, B6Sanitation.rawCell] at hq
    rcases hq with ⟨_, _, hpath2, _, _, _, _, _⟩
    simp [pendingTerminalDisposal, hpath2]
  unfold prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hpsi q.core hclear]

private theorem comparisonClean_preparedDeletion_inactive
    (hpsi : 0 < psi) (q : ExpiringAgentState psi kappa tau)
    (hq : ComparisonCleanCell q) :
    deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi q).core.erase) = false := by
  rw [comparisonClean_prepare_eq hpsi q hq]
  simp only [ComparisonCleanCell, B6Sanitation.rawCell] at hq
  rcases hq with ⟨hstate, hpath, _, _, _, _, _, _⟩
  simp [normalizeDeletion, deletionActive, pathPresent, hstate, hpath]

private theorem comparisonClean_preparedOrdinaryOpen
    (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : ComparisonCleanCell l) (hr : ComparisonCleanCell r) :
    BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi l r := by
  unfold BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
  dsimp only
  exact ⟨comparisonClean_preparedDeletion_inactive hpsi r hr,
    comparisonClean_preparedDeletion_inactive hpsi l hl⟩

private theorem cell_zero_ne_one
    (ring : DirectedRing n) (I : Interval ring) (hW : 2 ≤ I.size) :
    cell ring I.first 0 ≠ cell ring I.first 1 := by
  intro h
  have hf := B6LocalReverseFill.interval_cells_injective I
    (⟨0, by omega⟩ : Fin I.size)
    (⟨1, by omega⟩ : Fin I.size) h
  have hv : (0 : Nat) = 1 := congrArg Fin.val hf
  omega

private theorem erase_leader_frame
    (q : AuthorizedBoundedAgentState psi kappa) :
    q.erase.core.leader = q.core.leader := by
  rfl

private theorem zeroOneWord_internal
    (ring : DirectedRing n) (I : Interval ring) (hW : 2 ≤ I.size) :
    InternalWord I (zeroOneWord ring I) := by
  intro e he
  simp only [zeroOneWord, List.mem_singleton] at he
  subst e
  exact B6LocalRuler.internal_cell_edge ring I 0 (by omega)

/--
A drained core needs exactly one extra service before the existing sharp ruler
word: service the first core edge once.  The result either already contains a
leader or satisfies the missing `0 -> 1` ruler relation.
-/
theorem zeroOneRulerLeaf_one_service
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi kappa tau))
    (hK2 : K2DrainedAt (fun q : Phys psi kappa tau => q) WP X C) :
    ∃ w : List (Fin n),
      InternalWord X.core.J w ∧
      w.length = 1 ∧
      (B6LocalRuler.WorkspaceLeader ring X.core.J
          (runR hpsi h2 ring w C) ∨
       B6PreparedRelativeContract.ZeroOneRulerLeaf hpsi ring X.core.J
          (runR hpsi h2 ring w C)) := by
  have hW : 2 ≤ X.core.J.size := by
    rw [X.core.size_eq]
    unfold coreWidth
    have hp : 1 ≤ psi := by omega
    calc
      2 ≤ 4 * psi := by omega
      _ ≤ 4 * psi * psi := Nat.le_mul_of_pos_right _ hp

  let I := X.core.J
  have hWI : 2 ≤ I.size := hW
  let e := cell ring I.first 0
  let l := C (cell ring I.first 0)
  let r := C (cell ring I.first 1)

  have hs0 : support I (cell ring I.first 0) = true :=
    support_cell I (by omega)
  have hs1 : support I (cell ring I.first 1) = true :=
    support_cell I (by omega)

  have hc0 : ComparisonCleanCell l := hK2.1.2 _ hs0
  have hc1 : ComparisonCleanCell r := hK2.1.2 _ hs1

  have hk0 := hK2.2 _ hs0
  have hk1 := hK2.2 _ hs1

  have hl : l.core.core.leader = false := by
    have h := hk0.1
    exact (erase_leader_frame (l.core)).symm ▸ h

  have hr : r.core.core.leader = false := by
    have h := hk1.1
    exact (erase_leader_frame (r.core)).symm ▸ h

  have hopen := comparisonClean_preparedOrdinaryOpen hpsi l r hc0 hc1

  have hp := B6LocalRulerE.r1_ordinary_label_or_leader
    hpsi h2 l r hl hr hopen

  let D : PConfig n (Phys psi kappa tau) := step1 hpsi h2 ring C e
  let q := BirthCheckPermitRepair.row
    hpsi (by decide : 0 < 2) h2 l r

  have hleft : D (cell ring I.first 0) = q.1 := by
    dsimp [D, e, q, l, r]
    simpa only [right_cell] using
      (BirthCheckChainR1Ring.step1_left hpsi h2 ring C
        (cell ring I.first 0))

  have hne : ring.rightNeighbor (cell ring I.first 0) ≠
      cell ring I.first 0 := by
    rw [right_cell]
    exact (cell_zero_ne_one ring I hW).symm

  have hright : D (cell ring I.first 1) = q.2 := by
    dsimp [D, e, q, l, r]
    simpa only [right_cell] using
      (BirthCheckChainR1Ring.step1_right hpsi h2 ring C
        (cell ring I.first 0) hne)

  have hout :
      B6LocalRuler.WorkspaceLeader ring I D ∨
      B6PreparedRelativeContract.ZeroOneRulerLeaf hpsi ring I D := by
    rcases hp with hL | hR | hlabels
    · left
      exact ⟨0, by omega, by simpa [hleft] using hL⟩
    · left
      exact ⟨1, by omega, by simpa [hright] using hR⟩
    · right
      unfold B6PreparedRelativeContract.ZeroOneRulerLeaf
      rw [hleft, hright, hlabels.1]
      exact hlabels.2

  refine ⟨zeroOneWord ring I,
    zeroOneWord_internal ring I hW,
    zeroOneWord_length ring I, ?_⟩
  simpa [zeroOneWord, runR, I, D, e] using hout

end B6ZeroOneRulerLeaf
