import Leader.Wu.Entrance.StageLawProducers
import Leader.Wu.Entrance.PermitRowWriterLaw
import Leader.Wu.Entrance.PassiveAdmission


set_option autoImplicit false
set_option Elab.async false


namespace B6EntranceLawsWiring2


open B6EntranceV2
open B6LocalReverseFill
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {n psi : Nat}
variable {ring : DirectedRing n}


/-- Concrete C4 writer-protection witness.  This is the existing R1
writer-silence predicate with the landed internal-service preservation law. -/
def WPfinal (ring : DirectedRing n) :
    WriterProtected ring psi (Phys psi psi (16 * psi)) :=
  B6EntranceV2K2R1Law.r1WriterProtected ring


private theorem finalBase_path3_none
    (C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (hPassive : FinalWriterPassive C) (i : Fin n) :
    (B6WriterSilentGuarded.raw (finalBase C i)).path3 = none := by
  have hp := (hPassive i).1
  unfold R2Coherence.raw at hp
  unfold B6WriterSilentGuarded.raw B6Sanitation.rawCell
  unfold finalBase R2Coherence.baseProject
  dsimp only [physicalConfig]
  unfold PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase
  simp only [BoundedAgentState.erase, hp, Option.map]

/-- Final-carrier writer passivity is stronger than the empty-writer branch
of `WPfinal`; only the `path3 = none` component is needed here. -/
theorem writerProtected_of_finalWriterPassive_and_X
    (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (hPassive : FinalWriterPassive C)
    (X : Workspace ring psi) :
    WriterAt (WPfinal (psi := psi) ring) X (finalBase C) := by
  change B6WriterSilentGuarded.WriterSilent' ring X.env.I (finalBase C)
  apply B6WriterSilentGuarded.writerSilent'_of_prefixEmpty
  · unfold B6WriterSilentGuarded.GuardShape
    constructor
    · rw [X.env.size_eq]
      unfold envelopeWidth coreWidth collarWidth
      omega
    · exact X.env.proper
  · unfold B6WriterSilentGuarded.PrefixEmpty
    intro k _hk
    unfold B6WriterSilence.EmptyWriter
    exact finalBase_path3_none C hPassive
      (B6WriterSilentGuarded.pos ring X.env.I k)


/-- `WriterSilent'` depends only on cells in its interval. -/
private theorem writerSilent'_of_agreeOn
    (X : Workspace ring psi)
    (C D : PConfig n (Phys psi psi (16 * psi)))
    (hCD : AgreeOn X.env.I C D)
    (hC : B6WriterSilentGuarded.WriterSilent' ring X.env.I C) :
    B6WriterSilentGuarded.WriterSilent' ring X.env.I D := by
  rcases hC with ⟨hShape, hEmpty | hBlocked⟩
  · refine ⟨hShape, Or.inl ?_⟩
    unfold B6WriterSilentGuarded.PrefixEmpty at hEmpty ⊢
    intro k hk
    have hmem :
        support X.env.I
          (B6WriterSilentGuarded.pos ring X.env.I k) = true :=
      B6LocalReverseFill.support_cell X.env.I (by omega)
    have hEq := hCD (B6WriterSilentGuarded.pos ring X.env.I k) hmem
    rw [← hEq]
    exact hEmpty k hk
  · rcases hBlocked with ⟨hLift, hAll⟩
    refine ⟨hShape, Or.inr ⟨hLift, ?_⟩⟩
    unfold B6WriterSilentGuarded.BlockedAll at hAll ⊢
    intro k hk
    have hmem :
        support X.env.I
          (B6WriterSilentGuarded.pos ring X.env.I k) = true :=
      B6LocalReverseFill.support_cell X.env.I hk
    have hEq := hCD (B6WriterSilentGuarded.pos ring X.env.I k) hmem
    rw [← hEq]
    exact hAll k hk


/-- First C4 host law for the now-fixed writer-protection witness. -/
theorem hostWriterProtectedLocal_WPfinal
    (ring : DirectedRing n) :
    HostWriterProtectedLocal (WPfinal (psi := psi) ring) := by
  intro X C D hCD
  change
    B6WriterSilentGuarded.WriterSilent' ring X.env.I C ↔
      B6WriterSilentGuarded.WriterSilent' ring X.env.I D
  constructor
  · intro hC
    exact writerSilent'_of_agreeOn X C D hCD hC
  · intro hD
    apply writerSilent'_of_agreeOn X D C
    · intro i hi
      exact (hCD i hi).symm
    · exact hD



private theorem support_eq_true_exists_cell
    (I : Interval ring) (i : Fin n) (hi : support I i = true) :
    ∃ k : Nat, k < I.size ∧
      i = BirthCheckChainR1Ring.cell ring I.first k := by
  change (List.range I.size).any
      (fun k => decide
        (i = BirthCheckChainR1Ring.cell ring I.first k)) = true at hi
  obtain ⟨k, hk, he⟩ := List.any_eq_true.mp hi
  exact ⟨k, List.mem_range.mp hk, of_decide_eq_true he⟩

private theorem mod_add_mod_left (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod (a % m) b m, Nat.mod_mod]
  exact (Nat.add_mod a b m).symm

private theorem cell_cell_add
    (ring : DirectedRing n) (s : Fin n) (a b : Nat) :
    BirthCheckChainR1Ring.cell ring
        (BirthCheckChainR1Ring.cell ring s a) b =
      BirthCheckChainR1Ring.cell ring s (a + b) := by
  apply Fin.ext
  simp only [BirthCheckChainR1Ring.cell]
  rw [mod_add_mod_left]
  rw [Nat.add_assoc]

private theorem protectedBitsAgree_coreBitsAgree
    (X : Workspace ring psi)
    (C D : PConfig n (Phys psi psi (16 * psi)))
    (hBits : B6WriterSilentGuarded.ProtectedBitsAgree
      ring X.env.I C D) :
    CoreBitsAgree (fun q : Phys psi psi (16 * psi) => q) X C D := by
  intro i hi
  obtain ⟨j, hj, hij⟩ := support_eq_true_exists_cell X.core.J i hi
  let k := collarWidth psi + j
  have hcell :
      BirthCheckChainR1Ring.cell ring X.core.J.first j =
        BirthCheckChainR1Ring.cell ring X.env.I.first k := by
    dsimp only [k]
    rw [X.core.first_eq]
    exact cell_cell_add ring X.env.I.first (collarWidth psi) j
  have hk1 : 1 ≤ k := by
    dsimp only [k]
    unfold collarWidth
    omega
  have hk2 : k + 1 < X.env.I.size := by
    dsimp only [k]
    rw [X.core.size_eq] at hj
    have hc : 1 ≤ collarWidth psi := by
      unfold collarWidth
      exact Nat.succ_le_succ (Nat.zero_le psi)
    rw [X.env.size_eq]
    unfold envelopeWidth
    calc
      collarWidth psi + j + 1 <
          collarWidth psi + coreWidth psi + 1 :=
        Nat.add_lt_add_right
          (Nat.add_lt_add_left hj (collarWidth psi)) 1
      _ = coreWidth psi + (collarWidth psi + 1) := by
        rw [Nat.add_comm (collarWidth psi) (coreWidth psi)]
        rw [Nat.add_assoc]
      _ ≤ coreWidth psi +
          (collarWidth psi + collarWidth psi) :=
        Nat.add_le_add_left
          (Nat.add_le_add_left hc (collarWidth psi))
          (coreWidth psi)
      _ = coreWidth psi + 2 * collarWidth psi := by
        rw [Nat.two_mul]
  have hb := hBits k hk1 hk2
  rw [hij, hcell]
  exact hb.symm

/-- Second WP-dependent C4 producer: the fixed `WriterSilent'` witness is
preserved by one internal R1 service, together with all core resident bits. -/
theorem bitSilenceProducer_WPfinal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    B6EntranceLawsCensus.BitSilenceProducer
      (ring := ring)
      (B9Host.r1Host
        (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q)
      (WPfinal (psi := psi) ring) := by
  unfold B6EntranceLawsCensus.BitSilenceProducer
  unfold B6EntranceV2.HostCoreBitSilence
  intro X C e hWriter hC hInt
  dsimp only
  intro hD
  change B6WriterSilentGuarded.WriterSilent' ring X.env.I C at hWriter
  change BirthShortDoneTerminalFirstHit.Leaderless C at hC
  change BirthShortDoneTerminalFirstHit.Leaderless
    (B9Host.hostStep
      (B9Host.r1Host
        (kappa := psi) (tau := 16 * psi) hpsi h2)
      ring C e) at hD
  rw [B9Host.hostStep_r1_eq_step1 hpsi h2 ring C e] at hD
  have hs := B6WriterSilentGuarded.writerSilent'_internal_step
    hpsi h2 ring X.env.I C hWriter hC e hInt hD
  refine ⟨?_, ?_⟩
  · change B6WriterSilentGuarded.WriterSilent' ring X.env.I
      (B9Host.hostStep
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring C e)
    rw [B9Host.hostStep_r1_eq_step1 hpsi h2 ring C e]
    exact hs.1
  · rw [B9Host.hostStep_r1_eq_step1 hpsi h2 ring C e]
    exact protectedBitsAgree_coreBitsAgree X C
      (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e) hs.2

end B6EntranceLawsWiring2
