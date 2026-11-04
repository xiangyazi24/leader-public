import Leader.Wu.Entrance.PermitRowK2Observation
import Leader.Wu.Entrance.WriterSilentGuarded

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6EntranceV2K2R1Law

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneCuts
  BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair BirthStationaryWrite
open B6EntranceV2 B6EntranceV2K2 B6EntranceV2K2R1
  B6LocalReverseFill

variable {n psi : Nat}

/-- No production `WriterProtected` value is fixed by the B6/B7 entrance API.
Use the weakest existing R1 writer predicate that already has a complete
internal-service preservation theorem. -/
def r1WriterProtected (ring : DirectedRing n) :
    WriterProtected ring psi (Phys psi psi (16 * psi)) :=
  fun X C => B6WriterSilentGuarded.WriterSilent' ring X.env.I C

/-- The writer component really does have the requested one-service frame.
The proof is only the existing full-R1 writer-silence theorem plus the exact
host-step identification. -/
theorem r1WriterProtected_writer_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    R1WriterAtSingleServiceFrame hpsi h2 ring
      (r1WriterProtected ring) := by
  unfold R1WriterAtSingleServiceFrame
  intro X C e hLL hExpiry hInt
  dsimp only
  intro hD
  have hW := hExpiry.1.1
  change B6WriterSilentGuarded.WriterSilent' ring X.env.I C at hW
  change BirthShortDoneTerminalFirstHit.Leaderless C at hLL
  change BirthShortDoneTerminalFirstHit.Leaderless
    (B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      ring C e) at hD
  rw [B9Host.hostStep_r1_eq_step1 hpsi h2 ring C e] at hD
  have hw := B6WriterSilentGuarded.writerSilent'_internal_step
    hpsi h2 ring X.env.I C hW hLL e hInt hD
  change B6WriterSilentGuarded.WriterSilent' ring X.env.I
    (B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      ring C e)
  rw [B9Host.hostStep_r1_eq_step1 hpsi h2 ring C e]
  exact hw.1

namespace Regression

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring45 : DirectedRing 45 := ⟨by decide⟩

private def envI : Interval ring45 where
  first := 0
  size := 44
  nonempty := by decide
  fits := by decide

private def env : Envelope ring45 3 where
  I := envI
  size_eq := by decide
  proper := by decide

private def coreI : Interval ring45 where
  first := BirthCheckChainR1Ring.cell ring45 envI.first 4
  size := 36
  nonempty := by decide
  fits := by decide


private theorem support_iff_cell45
    (I : Interval ring45) (i : Fin 45) :
    support I i = true ↔
      ∃ k : Nat, k < I.size ∧
        i = BirthCheckChainR1Ring.cell ring45 I.first k := by
  constructor
  · intro h
    change (List.range I.size).any
      (fun k => decide
        (i = BirthCheckChainR1Ring.cell ring45 I.first k)) = true at h
    obtain ⟨k, hk, he⟩ := List.any_eq_true.mp h
    exact ⟨k, List.mem_range.mp hk, of_decide_eq_true he⟩
  · rintro ⟨k, hk, rfl⟩
    exact B6LocalReverseFill.support_cell I hk

private theorem mod_add_mod_left45 (a b : Nat) :
    (a % 45 + b) % 45 = (a + b) % 45 := by
  rw [Nat.add_mod (a % 45) b 45, Nat.mod_mod]
  exact (Nat.add_mod a b 45).symm

private theorem cell_cell_add45 (s : Fin 45) (a b : Nat) :
    BirthCheckChainR1Ring.cell ring45
        (BirthCheckChainR1Ring.cell ring45 s a) b =
      BirthCheckChainR1Ring.cell ring45 s (a + b) := by
  apply Fin.ext
  simp only [BirthCheckChainR1Ring.cell]
  rw [mod_add_mod_left45]
  rw [Nat.add_assoc]

private theorem coreI_cell_shift (k : Nat) :
    BirthCheckChainR1Ring.cell ring45 coreI.first k =
      BirthCheckChainR1Ring.cell ring45 envI.first (4 + k) := by
  simpa only [coreI] using cell_cell_add45 envI.first 4 k

private def core : Core ring45 3 env where
  J := coreI
  first_eq := rfl
  size_eq := by decide
  subset := by
    change ∀ i, support coreI i = true → support envI i = true
    intro i hi
    obtain ⟨k, hk, hik⟩ := (support_iff_cell45 coreI i).mp hi
    have hk44 : 4 + k < envI.size := by
      change k < 36 at hk
      change 4 + k < 44
      omega
    rw [hik, coreI_cell_shift k]
    exact B6LocalReverseFill.support_cell envI hk44



private def X : Workspace ring45 3 := ⟨env, core⟩
private theorem env_guard_shape :
    B6WriterSilentGuarded.GuardShape ring45 X.env.I := by
  change 2 ≤ 44 ∧ 44 < 45
  omega


private def ingress : Fin 45 :=
  BirthCheckChainR1Ring.cell ring45 envI.first 3

private def coreFirst : Fin 45 :=
  BirthCheckChainR1Ring.cell ring45 envI.first 4


private theorem ingress_right :
    ring45.rightNeighbor ingress = coreFirst := by
  change ring45.rightNeighbor
      (BirthCheckChainR1Ring.cell ring45 envI.first 3) =
    BirthCheckChainR1Ring.cell ring45 envI.first (3 + 1)
  exact BirthCheckChainR1Ring.right_cell ring45 envI.first 3


private theorem ingress_ne :
    ring45.rightNeighbor ingress ≠ ingress := by
  rw [ingress_right]
  change BirthCheckChainR1Ring.cell ring45 envI.first 4 ≠
    BirthCheckChainR1Ring.cell ring45 envI.first 3
  exact BirthCheckChainR1Ring.cell_ne ring45 envI.first
    (by decide : 4 < 45) (by decide : 3 < 45) (by decide : 4 ≠ 3)


private theorem ingress_internal : internal X.env.I ingress := by
  change internal envI ingress
  apply (B6LocalReverseFill.internal_iff envI ingress).2
  constructor
  · change support envI
      (BirthCheckChainR1Ring.cell ring45 envI.first 3) = true
    exact B6LocalReverseFill.support_cell envI (by decide)
  · rw [ingress_right]
    change support envI
      (BirthCheckChainR1Ring.cell ring45 envI.first 4) = true
    exact B6LocalReverseFill.support_cell envI (by decide)


private theorem coreFirst_mem : support X.core.J coreFirst = true := by
  change support coreI coreFirst = true
  apply (support_iff_cell45 coreI coreFirst).2
  refine ⟨0, ?_, ?_⟩
  · change 0 < 36
    omega
  · apply Fin.ext
    rfl

private theorem ingress_not_core : support X.core.J ingress = false := by
  change support coreI ingress = false
  cases hs : support coreI ingress with
  | false => rfl
  | true =>
      obtain ⟨k, hk, hik⟩ := (support_iff_cell45 coreI ingress).mp hs
      change k < 36 at hk
      have hk45 : 4 + k < 45 := by omega
      have heq :
          BirthCheckChainR1Ring.cell ring45 envI.first 3 =
            BirthCheckChainR1Ring.cell ring45 envI.first (4 + k) := by
        calc
          BirthCheckChainR1Ring.cell ring45 envI.first 3 = ingress := rfl
          _ = BirthCheckChainR1Ring.cell ring45 coreI.first k := hik
          _ = BirthCheckChainR1Ring.cell ring45 envI.first (4 + k) :=
            coreI_cell_shift k
      have hne := BirthCheckChainR1Ring.cell_ne ring45 envI.first
        (by decide : 3 < 45) hk45 (by omega : 3 ≠ 4 + k)
      exact (hne heq).elim




private def r1Host3 : B9Host.HostRow (Phys 3 3 48) :=
  B9Host.r1Host (kappa := 3) (tau := 48) h3 h23

/-- Clean bounded carrier used by both regressions.  Stall one prevents a
same-row static expiry from erasing a newly produced comparison state. -/
private def mkCell (i : Fin 45) (w resetCmd : Bool) : Phys 3 3 48 :=
  let b : BoundedAgentState 3 3 := {
    leader := false
    probe := false
    phase := false
    bit := false
    wait := w
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := ⟨i.val % 3, Nat.mod_lt _ h3⟩
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := resetCmd
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false
  }
  ⟨⟨b, false⟩, 1⟩

private theorem mkCell_follower (i : Fin 45) (w rc : Bool) :
    (mkCell i w rc).core.core.leader = false := by rfl

private theorem mkCell_empty (i : Fin 45) (w rc : Bool) :
    B6WriterSilence.EmptyWriter (B6Sanitation.rawCell (mkCell i w rc)) := by
  rfl

private theorem mkCell_reset_clear (i : Fin 45) (w : Bool) :
    ResetEchoClearCell (mkCell i w false) := by
  unfold ResetEchoClearCell B6Sanitation.rawCell mkCell
  exact ⟨rfl, rfl⟩

private theorem mkCell_comparison_clean (i : Fin 45) (w rc : Bool) :
    ComparisonCleanCell (mkCell i w rc) := by
  unfold ComparisonCleanCell B6Sanitation.rawCell mkCell
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Only the left-collar label-zero endpoint has a released WAIT token. -/
private def comparisonSeed : PConfig 45 (Phys 3 3 48) := fun i =>
  if i = ingress then mkCell i false false else mkCell i true false

private def comparisonAfter : PConfig 45 (Phys 3 3 48) :=
  B9Host.hostStep r1Host3 ring45 comparisonSeed ingress

private theorem comparisonSeed_follower (i : Fin 45) :
    (comparisonSeed i).core.core.leader = false := by
  by_cases h : i = ingress
  · rw [comparisonSeed, if_pos h]
    exact mkCell_follower i false false
  · rw [comparisonSeed, if_neg h]
    exact mkCell_follower i true false

private theorem comparisonSeed_empty (i : Fin 45) :
    B6WriterSilence.EmptyWriter
      (B6Sanitation.rawCell (comparisonSeed i)) := by
  by_cases h : i = ingress
  · rw [comparisonSeed, if_pos h]
    exact mkCell_empty i false false
  · rw [comparisonSeed, if_neg h]
    exact mkCell_empty i true false

private theorem comparisonSeed_reset_clear (i : Fin 45) :
    ResetEchoClearCell (comparisonSeed i) := by
  by_cases h : i = ingress
  · rw [comparisonSeed, if_pos h]
    exact mkCell_reset_clear i false
  · rw [comparisonSeed, if_neg h]
    exact mkCell_reset_clear i true

private theorem comparisonSeed_comparison_clean (i : Fin 45) :
    ComparisonCleanCell (comparisonSeed i) := by
  by_cases h : i = ingress
  · rw [comparisonSeed, if_pos h]
    exact mkCell_comparison_clean i false false
  · rw [comparisonSeed, if_neg h]
    exact mkCell_comparison_clean i true false

private theorem comparisonSeed_prefix :
    B6WriterSilentGuarded.PrefixEmpty ring45 X.env.I comparisonSeed := by
  intro k hk
  exact comparisonSeed_empty _

private theorem comparisonSeed_leaderless :
    HostLeaderless (fun q : Phys 3 3 48 => q) comparisonSeed := by
  change ∀ i, (comparisonSeed i).core.core.leader = false
  exact comparisonSeed_follower

private theorem comparisonSeed_expiry :
    ExpiryAt (fun q : Phys 3 3 48 => q)
      (r1WriterProtected ring45) X comparisonSeed := by
  constructor
  · constructor
    · change B6WriterSilentGuarded.WriterSilent'
        ring45 X.env.I comparisonSeed
      exact B6WriterSilentGuarded.writerSilent'_of_prefixEmpty
        ring45 X.env.I comparisonSeed env_guard_shape comparisonSeed_prefix
    · intro i hi
      exact comparisonSeed_reset_clear i
  · intro i hi
    exact comparisonSeed_comparison_clean i


/- Field-level kernel certificate for the WAIT/GEN hazard.  Both outputs are
followers, but the core responder has been re-armed to `.produce`. -/
theorem comparisonPair_snapshot :
    let q := r1Host3.row
      (comparisonSeed ingress) (comparisonSeed coreFirst)
    q.1.core.core.leader = false ∧
      q.2.core.core.leader = false ∧
      (B6Sanitation.rawCell q.2).state = .produce := by
  decide +kernel

private theorem comparisonAfter_leaderless :
    HostLeaderless (fun q : Phys 3 3 48 => q) comparisonAfter := by
  change ∀ i, (comparisonAfter i).core.core.leader = false
  intro i
  unfold comparisonAfter
  by_cases hL : i = ingress
  · subst i
    rw [B9Host.hostStep_left, ingress_right]
    exact comparisonPair_snapshot.1
  · by_cases hR : i = coreFirst
    · subst i
      rw [← ingress_right]
      rw [B9Host.hostStep_right r1Host3 ring45 comparisonSeed ingress ingress_ne]
      simpa only [ingress_right] using comparisonPair_snapshot.2.1
    · have hR' : i ≠ ring45.rightNeighbor ingress := by
        rw [ingress_right]
        exact hR
      rw [B9Host.hostStep_other
        r1Host3 ring45 comparisonSeed ingress i hL hR']
      exact comparisonSeed_follower i


private theorem comparisonAfter_core_state :
    (B6Sanitation.rawCell (comparisonAfter coreFirst)).state = .produce := by
  unfold comparisonAfter
  rw [← ingress_right]
  rw [B9Host.hostStep_right r1Host3 ring45 comparisonSeed ingress ingress_ne]
  simpa only [ingress_right] using comparisonPair_snapshot.2.2


private theorem comparisonSeed_ingress_wait :
    (B6Sanitation.rawCell (comparisonSeed ingress)).wait = false := by
  rw [comparisonSeed, if_pos rfl]
  rfl


/-- `ComparisonCleanCell` is not an R1 one-service invariant, even after fixing
the natural writer-silence predicate.  The source is fully `ExpiryAt`; only a
WAIT release outside the sanitation coordinates is used. -/
theorem r1WriterProtected_comparison_frame_false :
    ¬ R1ComparisonCleanSingleServiceFrame h3 h23 ring45
      (r1WriterProtected ring45) := by
  intro h
  have hcore := h X comparisonSeed ingress
    comparisonSeed_leaderless comparisonSeed_expiry ingress_internal
    comparisonAfter_leaderless
  change CoreAll (fun q : Phys 3 3 48 => q) X
    ComparisonCleanCell comparisonAfter at hcore
  have hc := hcore coreFirst coreFirst_mem
  unfold ComparisonCleanCell at hc
  dsimp only at hc
  have hnone := hc.1
  have hbad : MainState.produce = MainState.none :=
    comparisonAfter_core_state.symm.trans hnone
  exact (by decide : MainState.produce ≠ MainState.none) hbad

/-- The only reset token is at envelope offset 3, immediately to the left of
the protected core.  Thus the source core itself is reset/echo clear. -/
private def resetSeed : PConfig 45 (Phys 3 3 48) := fun i =>
  if i = ingress then mkCell i true true else mkCell i true false

private def resetAfter : PConfig 45 (Phys 3 3 48) :=
  B9Host.hostStep r1Host3 ring45 resetSeed ingress

private theorem resetSeed_follower (i : Fin 45) :
    (resetSeed i).core.core.leader = false := by
  by_cases h : i = ingress
  · rw [resetSeed, if_pos h]
    exact mkCell_follower i true true
  · rw [resetSeed, if_neg h]
    exact mkCell_follower i true false

private theorem resetSeed_empty (i : Fin 45) :
    B6WriterSilence.EmptyWriter (B6Sanitation.rawCell (resetSeed i)) := by
  by_cases h : i = ingress
  · rw [resetSeed, if_pos h]
    exact mkCell_empty i true true
  · rw [resetSeed, if_neg h]
    exact mkCell_empty i true false

private theorem resetSeed_comparison_clean (i : Fin 45) :
    ComparisonCleanCell (resetSeed i) := by
  by_cases h : i = ingress
  · rw [resetSeed, if_pos h]
    exact mkCell_comparison_clean i true true
  · rw [resetSeed, if_neg h]
    exact mkCell_comparison_clean i true false

private theorem resetSeed_reset_clear_of_ne
    (i : Fin 45) (h : i ≠ ingress) :
    ResetEchoClearCell (resetSeed i) := by
  rw [resetSeed, if_neg h]
  exact mkCell_reset_clear i true

private theorem resetSeed_prefix :
    B6WriterSilentGuarded.PrefixEmpty ring45 X.env.I resetSeed := by
  intro k hk
  exact resetSeed_empty _

private theorem resetSeed_leaderless :
    HostLeaderless (fun q : Phys 3 3 48 => q) resetSeed := by
  change ∀ i, (resetSeed i).core.core.leader = false
  exact resetSeed_follower

private theorem resetSeed_expiry :
    ExpiryAt (fun q : Phys 3 3 48 => q)
      (r1WriterProtected ring45) X resetSeed := by
  constructor
  · constructor
    · change B6WriterSilentGuarded.WriterSilent' ring45 X.env.I resetSeed
      exact B6WriterSilentGuarded.writerSilent'_of_prefixEmpty
        ring45 X.env.I resetSeed env_guard_shape resetSeed_prefix
    · intro i hi
      by_cases h : i = ingress
      · subst i
        rw [ingress_not_core] at hi
        cases hi
      · exact resetSeed_reset_clear_of_ne i h
  · intro i hi
    exact resetSeed_comparison_clean i


/- Field-level kernel certificate for the boundary scar.  Algorithm-14 moves
the left reset right; the responder reset survives the complete R1 row. -/
theorem resetPair_snapshot :
    let q := r1Host3.row (resetSeed ingress) (resetSeed coreFirst)
    q.1.core.core.leader = false ∧
      q.2.core.core.leader = false ∧
      (B6Sanitation.rawCell q.2).reset_cmd = true := by
  decide +kernel

private theorem resetAfter_leaderless :
    HostLeaderless (fun q : Phys 3 3 48 => q) resetAfter := by
  change ∀ i, (resetAfter i).core.core.leader = false
  intro i
  unfold resetAfter
  by_cases hL : i = ingress
  · subst i
    rw [B9Host.hostStep_left, ingress_right]
    exact resetPair_snapshot.1
  · by_cases hR : i = coreFirst
    · subst i
      rw [← ingress_right]
      rw [B9Host.hostStep_right r1Host3 ring45 resetSeed ingress ingress_ne]
      simpa only [ingress_right] using resetPair_snapshot.2.1
    · have hR' : i ≠ ring45.rightNeighbor ingress := by
        rw [ingress_right]
        exact hR
      rw [B9Host.hostStep_other r1Host3 ring45 resetSeed ingress i hL hR']
      exact resetSeed_follower i


private theorem resetAfter_core_reset :
    (B6Sanitation.rawCell (resetAfter coreFirst)).reset_cmd = true := by
  unfold resetAfter
  rw [← ingress_right]
  rw [B9Host.hostStep_right r1Host3 ring45 resetSeed ingress ingress_ne]
  simpa only [ingress_right] using resetPair_snapshot.2.2


/-- `ResetEchoClearCell` is likewise not closed: `ExpiryAt` only asks for it on
the core, while an internal envelope edge can import a reset from its collar. -/
theorem r1WriterProtected_resetEcho_frame_false :
    ¬ R1ResetEchoSingleServiceFrame h3 h23 ring45
      (r1WriterProtected ring45) := by
  intro h
  have hcore := h X resetSeed ingress
    resetSeed_leaderless resetSeed_expiry ingress_internal
    resetAfter_leaderless
  change CoreAll (fun q : Phys 3 3 48 => q) X
    ResetEchoClearCell resetAfter at hcore
  have hc := hcore coreFirst coreFirst_mem
  unfold ResetEchoClearCell at hc
  dsimp only at hc
  have hfalse := hc.1
  have hbad : (true : Bool) = false :=
    resetAfter_core_reset.symm.trans hfalse
  exact (by decide : (true : Bool) ≠ false) hbad

/-- Hence the exact `R1K2DrainFrame` premise used by the proposed reverse-sweep
lift is false for the natural R1 writer predicate. -/
theorem r1WriterProtected_drainFrame_false :
    ¬ R1K2DrainFrame h3 h23 ring45 (r1WriterProtected ring45) := by
  intro h
  have hE := h X resetSeed ingress
    resetSeed_leaderless resetSeed_expiry ingress_internal
    resetAfter_leaderless
  have hcore := hE.1.2 coreFirst coreFirst_mem
  unfold ResetEchoClearCell at hcore
  dsimp only at hcore
  have hfalse := hcore.1
  have hbad : (true : Bool) = false :=
    resetAfter_core_reset.symm.trans hfalse
  exact (by decide : (true : Bool) ≠ false) hbad

/-- The row-observation seam remains valid; what fails is the
source-invariant half of the conjunction. -/
theorem r1WriterProtected_proofSeams_false :
    ¬ R1K2ProofSeams h3 h23 ring45 (r1WriterProtected ring45) := by
  intro h
  exact r1WriterProtected_drainFrame_false h.1

end Regression

/-- A current-state envelope predicate strong enough to exclude both concrete
hazards above: sanitation is required on the collars as well as the core, and
WAIT is dormant.  It still says nothing about K2 bullet occupancy. -/
def R1DrainDormantCell (q : Phys psi psi (16 * psi)) : Prop :=
  ResetEchoClearCell q ∧
    ComparisonCleanCell q ∧
    B6WriterSilence.EmptyWriter (B6Sanitation.rawCell q) ∧
    (B6Sanitation.rawCell q).wait = true

def R1DrainEnvelopeClean
    (ring : DirectedRing n) (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) : Prop :=
  ∀ i, support X.env.I i = true → R1DrainDormantCell (C i)

/-- Exact prefix invariant needed by the reverse-envelope K2 induction.
It does not assume the K2 target; it only says that the non-K2 substrate stays
clean/dormant at every prefix of the designated reverse word while the run is
leaderless.  A future physical entrance theorem must derive this (or a more
local equivalent) from executable fields rather than assume it silently. -/
def R1DrainStable
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) : Prop :=
  R1DrainEnvelopeClean ring X C ∧
    ∀ u v : List (Fin n), u ++ v = k2DrainWord ring X →
      let D := runHost
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring u C
      HostLeaderless (fun q : Phys psi psi (16 * psi) => q) D →
        R1DrainEnvelopeClean ring X D

theorem expiry_not_enough_for_R1DrainStable :
    ∃ (C : PConfig 45 (Phys 3 3 48)),
      HostLeaderless (fun q : Phys 3 3 48 => q) C ∧
      ExpiryAt (fun q : Phys 3 3 48 => q)
        (r1WriterProtected Regression.ring45) Regression.X C ∧
      ¬ R1DrainStable Regression.h3 Regression.h23
        Regression.ring45 Regression.X C := by
  refine ⟨Regression.comparisonSeed,
    Regression.comparisonSeed_leaderless,
    Regression.comparisonSeed_expiry, ?_⟩
  intro hs
  have hing :
      support Regression.X.env.I Regression.ingress = true :=
    ((B6LocalReverseFill.internal_iff
      Regression.X.env.I Regression.ingress).mp
        Regression.ingress_internal).1
  have hd := hs.1 Regression.ingress hing
  have hw :
      (B6Sanitation.rawCell
        (Regression.comparisonSeed Regression.ingress)).wait = true :=
    hd.2.2.2
  have hf := Regression.comparisonSeed_ingress_wait
  have hbad : (false : Bool) = true := hf.symm.trans hw
  exact (by decide : (false : Bool) ≠ true) hbad



end B6EntranceV2K2R1Law
