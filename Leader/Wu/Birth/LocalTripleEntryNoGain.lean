import Leader.Wu.Birth.LocalTripleContinuationBridge

namespace BirthB1Local3EventHit

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
open BirthWaitClockMass BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing BirthWaitClockMass.ResetEntry
open BirthShortWaitDomainWitness BirthShortWaitRawRing
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Count
open BirthShortDoneTerminalPassiveLocal3Producer
open BirthShortDoneTerminalPassiveLocal3Rotation

set_option autoImplicit false
set_option pp.structureInstances false
set_option Elab.async false

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide

private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0

private def d0 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def d1 : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def raw4 (i : Fin 4) : AgentState 2 :=
  if i.val = 0 then BirthWaitPassive.cell d0
  else if i.val = 1 then BirthWaitPassive.cell d1
  else if i.val = 2 then BirthWaitPassive.cell d0
  else BirthWaitPassive.cell d1

private theorem raw4_domain (i : Fin 4) :
    (raw4 i).inProtocolDomain 2 := by
  simp [raw4, d0, d1, AgentState.inProtocolDomain,
    BirthWaitPassive.cell]

private def pack4 (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain (raw4 i) (raw4_domain i), false⟩, 0⟩

private def source : BirthPhaseWait2BlockProgress.FC 4 2 2 0 :=
  fun i => pack4 i

@[simp] private theorem raw_source (i : Fin 4) :
    raw (source i) = raw4 i := by
  simp [source, pack4, raw, BoundedAgentState.erase_ofDomain]

private theorem source_line : LocalLine3 hpsi2 hn4 source := by
  refine {
    pass0 := ?_, pass1 := ?_, pass2 := ?_,
    lab0 := ?_, lab1 := ?_, lab2 := ?_ }
  · simp [raw4, p0, d0, Passive, InertWriter, Metadata,
      BirthWaitPassive.registers, BirthWaitPassive.cell]
  · simp [raw4, p1, d1, Passive, InertWriter, Metadata,
      BirthWaitPassive.registers, BirthWaitPassive.cell]
  · simp [raw4, p2, d0, Passive, InertWriter, Metadata,
      BirthWaitPassive.registers, BirthWaitPassive.cell]
  · simp [raw4, p0, d0, BirthWaitPassive.cell]
  · simp [raw4, p1, d1, BirthWaitPassive.cell]
  · simp [raw4, p2, d0, BirthWaitPassive.cell]

private theorem safe0 : SafeLine3Edge hn4 (p0 hn4) := by
  constructor
  · exact Fin.ne_of_val_ne (by simp [p0, p2])
  · exact Fin.ne_of_val_ne (by simp [p0, leftCross]; omega)

private theorem safe1 : SafeLine3Edge hn4 (p1 hn4) := by
  constructor
  · exact Fin.ne_of_val_ne (by simp [p1, p2])
  · exact Fin.ne_of_val_ne (by simp [p1, leftCross]; omega)

private theorem p0_ne_p1 : p0 hn4 ≠ p1 hn4 :=
  Fin.ne_of_val_ne (by simp [p0, p1])

private theorem preFinish_right_label
    (kappa : Nat) (l r : AgentState 2) :
    (preFinishEntry2 hpsi2 h2 kappa l r).2.label = r.label := by
  simp [preFinishEntry2, waitSaturatedPrepare, terminalInactiveClear,
    waitWidthCarry, waitWidthReset]

private theorem p0_preFinish :
    let s := preFinishEntry2 hpsi2 h2 2
      (raw (source (p0 hn4))) (raw (source (p1 hn4)))
    s.2.label = (1 : Fin 2) ∧ s.2.count = 0 := by
  simp only [raw_source]
  decide

private theorem p0_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 source (p0 hn4) := by
  unfold RowPreCap2
  intro hc
  unfold RowCap2 at hc
  dsimp only at hc
  rw [right_p0] at hc
  have hw := p0_preFinish
  dsimp only at hw
  omega

private def c1 := hostStep hpsi2 h2 ring4 source (p0 hn4)
private def c2 := hostStep hpsi2 h2 ring4 c1 (p1 hn4)

private theorem c1_line : LocalLine3 hpsi2 hn4 c1 := by
  have hs := local3_one_step hpsi2 h2 hn4 2 0 ring4
    source (p0 hn4) source_line safe0 (fun _ => p0_preCap)
  exact hs.1

private theorem p1_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 c1 (p1 hn4) := by
  unfold RowPreCap2
  intro hc
  unfold RowCap2 at hc
  dsimp only at hc
  have hkeep := preFinish_right_label 2
    (raw (c1 (p1 hn4)))
    (raw (c1 (ring4.rightNeighbor (p1 hn4))))
  have hterm :
      (raw (c1 (ring4.rightNeighbor (p1 hn4)))).label =
        widthTerminal hpsi2 h2 := hkeep.symm.trans hc.1
  have hp2 : (raw (c1 (p2 hn4))).label.val = 0 := by
    simpa using c1_line.lab2
  have hr0 :
      (raw (c1 (ring4.rightNeighbor (p1 hn4)))).label.val = 0 := by
    rw [right_p1]
    exact hp2
  have hv := congrArg Fin.val hterm
  rw [hr0] at hv
  simp [widthTerminal] at hv

private theorem entry_localWait : LocalWaitEntry2 hpsi2 hn4 c2 := by
  have h := twoCross_success_entry_or_cap
    hpsi2 h2 hn4 2 0 ring4 source source_line
      [p0 hn4, p1 hn4] (by rfl)
  simp only [Local3EntryOrCap] at h
  rcases h with hcap0 | hp0 | hp1 | hout
  · exact (p0_preCap hcap0.2.2.2).elim
  · rcases hp0 with ⟨_, _, _, _, hafter⟩
    simp only [Local3AfterP0] at hafter
    rcases hafter with hcap1 | hentry | hp0again | hout1
    · exact (p1_preCap hcap1.2.2.2).elim
    · rcases hentry with ⟨_, _, _, _, hwait⟩
      simpa [c1, c2] using hwait
    · exact (p0_ne_p1 hp0again.1.symm).elim
    · exact (hout1.2.1 (Or.inr rfl)).elim
  · exact (p0_ne_p1 hp1.1).elim
  · exact (hout.2.1 (Or.inl rfl)).elim

private theorem rotate_zero
    (C : BirthPhaseWait2BlockProgress.FC 4 2 2 0) :
    rotateConfig ring4 anchor4 C = C := by
  funext i
  apply congrArg C
  apply Fin.ext
  change (0 + i.val) % 4 = i.val
  simpa using Nat.mod_eq_of_lt i.isLt

set_option maxRecDepth 32768 in
/-- Actual p0,p1 Local3 entry, but the tracked count did not move. -/
theorem orderedWaitEntry2At_no_strict_gain :
    OrderedWaitEntry2At hn4 ring4 anchor4 c2 ∧
      ¬ BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 source <
        BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 c2 := by
  constructor
  · unfold OrderedWaitEntry2At
    rw [rotate_zero]
    exact entry_localWait.2
  · have heq :
        BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 source =
          BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 c2 := by
      decide
    rw [← heq]
    exact Nat.lt_irrefl _

end BirthB1Local3EventHit

#print axioms BirthB1Local3EventHit.orderedWaitEntry2At_no_strict_gain
