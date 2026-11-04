import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleMass


namespace BirthShortDoneTerminalPassiveLocal3FiniteAudit


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
open BirthShortDoneTerminalPassiveLocal3Mass
open FiniteUniformStoppingTree ControlledSchedulerMass


set_option autoImplicit false
set_option pp.structureInstances false
set_option Elab.async false


private theorem hpsi2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide
private theorem hn5 : 4 <= 5 := by decide


private def ring5 : DirectedRing 5 := ⟨by decide⟩


/-- Explicitly certify that this is the requested nondivisible case. -/
theorem n5_psi2_nondivisible : ¬ 2 ∣ 5 := by decide


/-- Dirty local root: passive, but both reset and carry are deliberately set. -/
private def d0 : Registers 2 where
  label := 0
  h := true
  carry := true
  reset := true
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


/-- Dirty width-two terminal: again both reset and carry are set. -/
private def d1 : Registers 2 where
  label := 1
  h := true
  carry := true
  reset := true
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


/-- Third local-line BirthWaitPassive.cell.  Its required LocalLine3 label is 2 % 2 = 0. -/
private def d2 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


/-- Deliberately non-passive outside BirthWaitPassive.cell. -/
private def dout : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := false
  bit := true
  phase := true
  writer := .none


private def raw5 (i : Fin 5) : AgentState 2 :=
  if i.val = 0 then BirthWaitPassive.cell d0
  else if i.val = 1 then BirthWaitPassive.cell d1
  else if i.val = 2 then BirthWaitPassive.cell d2
  else BirthWaitPassive.cell dout


/-- Every raw record is in the finite value domain for every kappa; all counts
are zero.  This is value-domain membership only, not passivity. -/
private theorem raw5_domain (kappa : Nat) (i : Fin 5) :
    (raw5 i).inProtocolDomain kappa := by
  simp [raw5, d0, d1, d2, dout, AgentState.inProtocolDomain, BirthWaitPassive.cell]


private def pack5 (kappa : Nat) (i : Fin 5) :
    ExpiringAgentState 2 kappa 0 :=
  ⟨⟨BoundedAgentState.ofDomain (raw5 i) (raw5_domain kappa i), false⟩, 0⟩


private def sourceC (kappa : Nat) : FC 5 2 kappa 0 :=
  fun i => pack5 kappa i


@[simp] private theorem raw_sourceC (kappa : Nat) (i : Fin 5) :
    raw (sourceC kappa i) = raw5 i := by
  simp [sourceC, pack5, raw, BoundedAgentState.erase_ofDomain]


/-- The requested dirty local fields are literal source fields. -/
theorem source_dirty (kappa : Nat) :
    (raw (sourceC kappa (p0 hn5))).reset = true /\
    (raw (sourceC kappa (p0 hn5))).carry = true /\
    (raw (sourceC kappa (p1 hn5))).reset = true /\
    (raw (sourceC kappa (p1 hn5))).carry = true := by
  simp [raw5, p0, p1, d0, d1, BirthWaitPassive.cell]


/-- Site 3 is outside the LocalLine3 triple and is genuinely non-passive. -/
theorem source_has_nonpassive_outside (kappa : Nat) :
    ¬ Passive (raw (sourceC kappa (p3 hn5))) := by
  simp only [raw_sourceC]
  intro h
  have hw := h.2.1
  change false = true at hw
  cases hw


/-- The same full source satisfies exactly the accepted local-line premise. -/
theorem source_localLine3 (kappa : Nat) :
    LocalLine3 hpsi2 hn5 (sourceC kappa) := by
  refine {
    pass0 := ?_
    pass1 := ?_
    pass2 := ?_
    lab0 := ?_
    lab1 := ?_
    lab2 := ?_ }
  · simp [raw5, p0, d0, Passive, InertWriter, Metadata, BirthWaitPassive.registers, BirthWaitPassive.cell]
  · simp [raw5, p1, d1, Passive, InertWriter, Metadata, BirthWaitPassive.registers, BirthWaitPassive.cell]
  · simp [raw5, p2, d2, Passive, InertWriter, Metadata, BirthWaitPassive.registers, BirthWaitPassive.cell]
  · simp [raw5, p0, d0, BirthWaitPassive.cell]
  · simp [raw5, p1, d1, BirthWaitPassive.cell]
  · simp [raw5, p2, d2, BirthWaitPassive.cell]


/-- Dirty reset at physical site 0 excludes an already-completed ordered WAIT
entry.  This does not rely on Decidable for the existential State predicate. -/
theorem source_not_ordered (kappa : Nat) :
    ¬ OrderedWaitEntry2 hn5 (sourceC kappa) := by
  intro h
  rcases h with ⟨S, hconf⟩
  have hk := S.agree (0 : Fin 2)
  unfold BirthShortWaitRawRing.KeyAgree at hk
  have hz := congrArg WaitKey.reset hk
  rw [hconf] at hz
  change
    (raw (sourceC kappa (p0 hn5))).reset =
      (S.line.cell (0 : Fin 2)).reset at hz
  have hd : (raw (sourceC kappa (p0 hn5))).reset = true := by
    simp [raw5, p0, d0, BirthWaitPassive.cell]
  have hc : (S.line.cell (0 : Fin 2)).reset = false :=
    S.line.reset_clear (0 : Fin 2)
  have htf : (true : Bool) = false := hd.symm.trans (hz.trans hc)
  simpa using htf


private theorem safe0 : SafeLine3Edge hn5 (p0 hn5) := by
  constructor
  · exact Fin.ne_of_val_ne (by simp [p0, p2])
  · exact Fin.ne_of_val_ne (by simp [p0, leftCross]; omega)


private theorem safe1 : SafeLine3Edge hn5 (p1 hn5) := by
  constructor
  · exact Fin.ne_of_val_ne (by simp [p1, p2])
  · exact Fin.ne_of_val_ne (by simp [p1, leftCross]; omega)


private theorem p0_ne_p1 : p0 hn5 ≠ p1 hn5 :=
  Fin.ne_of_val_ne (by simp [p0, p1])


/-- `preFinishEntry2` never changes the responder label.  This is the cheap
structural fact used to rule out a p1 cap after the real p0 host row. -/
private theorem preFinish_right_label (kappa : Nat) (l r : AgentState 2) :
    (preFinishEntry2 hpsi2 hle2 kappa l r).2.label = r.label := by
  simp [preFinishEntry2, waitSaturatedPrepare, terminalInactiveClear,
    waitWidthCarry, waitWidthReset]


/-! ### Positive-cap-2 entry fixture -/


private def entryC0 : FC 5 2 2 0 := sourceC 2
private def entryC1 : FC 5 2 2 0 :=
  hostStep hpsi2 hle2 ring5 entryC0 (p0 hn5)
private def entryC2 : FC 5 2 2 0 :=
  hostStep hpsi2 hle2 ring5 entryC1 (p1 hn5)


/-- Small closed WAIT check: the first row raises terminal count only to 1,
strictly below kappa=2. -/
private theorem entry_p0_preFinish :
    let s := preFinishEntry2 hpsi2 hle2 2
      (raw (entryC0 (p0 hn5))) (raw (entryC0 (p1 hn5)))
    s.2.label = (1 : Fin 2) /\ s.2.count = 1 := by
  simp only [entryC0, raw_sourceC]
  decide


private theorem entry_p0_preCap :
    RowPreCap2 hpsi2 hle2 2 ring5 entryC0 (p0 hn5) := by
  unfold RowPreCap2
  intro hc
  unfold RowCap2 at hc
  dsimp only at hc
  rw [right_p0] at hc
  have hw := entry_p0_preFinish
  dsimp only at hw
  omega


/-- Public local producer consumes the literal full TerminalHost p0 row. -/
private theorem entry_step0 :
    LocalLine3 hpsi2 hn5 entryC1 /\
      RowProjection2 hpsi2 hle2 2 0 ring5 entryC0 (p0 hn5) := by
  have hs := local3_one_step hpsi2 hle2 hn5 2 0 ring5
    entryC0 (p0 hn5) (source_localLine3 2) safe0
    (fun _ => entry_p0_preCap)
  exact ⟨hs.1, hs.2 (Or.inl rfl)⟩


/-- The second row cannot be a cap row for a structural reason: its responder
is p2, and LocalLine3 preserves p2's label 0, whereas width-two terminal is 1. -/
private theorem entry_p1_preCap :
    RowPreCap2 hpsi2 hle2 2 ring5 entryC1 (p1 hn5) := by
  unfold RowPreCap2
  intro hc
  unfold RowCap2 at hc
  dsimp only at hc
  have hkeep := preFinish_right_label 2
    (raw (entryC1 (p1 hn5)))
    (raw (entryC1 (ring5.rightNeighbor (p1 hn5))))
  have hterm :
      (raw (entryC1 (ring5.rightNeighbor (p1 hn5)))).label =
        widthTerminal (by decide : 0 < 2) hle2 :=
    hkeep.symm.trans hc.1
  have hp2 : (raw (entryC1 (p2 hn5))).label.val = 0 := by
    simpa using entry_step0.1.lab2
  have hr0 :
      (raw (entryC1 (ring5.rightNeighbor (p1 hn5)))).label.val = 0 := by
    rw [right_p1]
    exact hp2
  have hv := congrArg Fin.val hterm
  rw [hr0] at hv
  simp [widthTerminal] at hv


/-- Public local producer consumes the literal full TerminalHost p1 row too. -/
private theorem entry_step1 :
    LocalLine3 hpsi2 hn5 entryC2 /\
      RowProjection2 hpsi2 hle2 2 0 ring5 entryC1 (p1 hn5) := by
  have hs := local3_one_step hpsi2 hle2 hn5 2 0 ring5
    entryC1 (p1 hn5) entry_step0.1 safe1
    (fun _ => entry_p1_preCap)
  exact ⟨hs.1, hs.2 (Or.inr rfl)⟩


/-- The word is on the original Fin 5 scheduler alphabet, not a projected or
conditioned scheduler. -/
theorem entry_word_success :
    runWord (twoCrossStep hn5) (.active false)
      [p0 hn5, p1 hn5] = .success := by
  rfl


/-- Consume the accepted public producer and eliminate the only two cap
possibilities using the actual pre-cap facts above. -/
private theorem entry_localWait : LocalWaitEntry2 hpsi2 hn5 entryC2 := by
  have h := twoCross_success_entry_or_cap
    hpsi2 hle2 hn5 2 0 ring5 entryC0
    (source_localLine3 2) [p0 hn5, p1 hn5] entry_word_success
  simp only [Local3EntryOrCap] at h
  rcases h with hcap0 | hp0 | hp1 | hout
  · exact (entry_p0_preCap hcap0.2.2.2).elim
  · rcases hp0 with ⟨_, _, _, _, hafter⟩
    simp only [Local3AfterP0] at hafter
    rcases hafter with hcap1 | hentry | hp0again | hout1
    · exact (entry_p1_preCap hcap1.2.2.2).elim
    · rcases hentry with ⟨_, _, _, _, hwait⟩
      simpa [entryC1, entryC2] using hwait
    · exact (p0_ne_p1 hp0again.1.symm).elim
    · exact (hout1.2.1 (Or.inr rfl)).elim
  · exact (p0_ne_p1 hp1.1).elim
  · exact (hout.2.1 (Or.inl rfl)).elim


/-- This is the requested real entry-before-cap endpoint. -/
theorem n5_psi2_dirty_entry_before_cap :
    OrderedWaitEntry2 hn5 entryC2 :=
  entry_localWait.2


/-- Both actually executed rows are pre-cap. -/
theorem n5_psi2_dirty_entry_rows_preCap :
    RowPreCap2 hpsi2 hle2 2 ring5 entryC0 (p0 hn5) /\
      RowPreCap2 hpsi2 hle2 2 ring5 entryC1 (p1 hn5) :=
  ⟨entry_p0_preCap, entry_p1_preCap⟩


/-- The accepted mass consumer sees the same original word and literal host. -/
theorem n5_psi2_dirty_entry_public_endpoint :
    Local3PhysicalEndpoint hpsi2 hle2 hn5 2 0 ring5 entryC0
      [p0 hn5, p1 hn5] :=
  twoCross_success_physical_endpoint
    hpsi2 hle2 hn5 2 0 ring5 entryC0
    (source_localLine3 2) [p0 hn5, p1 hn5] entry_word_success


/-- Stronger specialization: for this fixture we know the public endpoint is
specifically its executed-prefix entry branch. -/
theorem n5_psi2_dirty_entry_exact_branch :
    Local3PhysicalEndpoint hpsi2 hle2 hn5 2 0 ring5 entryC0
      [p0 hn5, p1 hn5] := by
  refine Or.inl ⟨[p0 hn5, p1 hn5], [], by simp, ?_⟩
  simpa [entryC0, entryC1, entryC2] using n5_psi2_dirty_entry_before_cap


/-! ### Separate genuine positive cap fixture -/


private def capC : FC 5 2 1 0 := sourceC 1


/-- The terminal is not preloaded at cap. -/
theorem cap_source_count_zero :
    (raw (capC (p1 hn5))).count = 0 := by
  simp [capC, raw5, p1, d1, BirthWaitPassive.cell]


/-- Closed check of the real p0 WAIT prefix: this row raises terminal count
from 0 to 1. -/
private theorem cap_p0_preFinish :
    let s := preFinishEntry2 hpsi2 hle2 1
      (raw (capC (p0 hn5))) (raw (capC (p1 hn5)))
    s.2.label = (1 : Fin 2) /\ s.2.count = 1 := by
  simp only [capC, raw_sourceC]
  decide


/-- Hence the current p0 row is a genuine RowCap2 at positive kappa=1. -/
theorem n5_psi2_positive_cap_row :
    RowCap2 hpsi2 hle2 1 ring5 capC (p0 hn5) := by
  unfold RowCap2
  dsimp only
  rw [right_p0]
  have h := cap_p0_preFinish
  dsimp only at h
  simpa [widthTerminal] using h


private theorem cap_now :
    Local3CapNow hpsi2 hle2 hn5 1 0 ring5 capC (p0 hn5) :=
  ⟨source_localLine3 1, safe0, Or.inl rfl, n5_psi2_positive_cap_row⟩


private theorem cap_event :
    Local3EntryOrCap hpsi2 hle2 hn5 1 0 ring5 capC [p0 hn5] := by
  change Local3CapNow hpsi2 hle2 hn5 1 0 ring5 capC (p0 hn5) \/ _
  exact Or.inl cap_now


/-- Public physical consumer: the cap is tested before executing p0. -/
theorem n5_psi2_positive_cap_public_endpoint :
    Local3PhysicalEndpoint hpsi2 hle2 hn5 1 0 ring5 capC [p0 hn5] :=
  Local3EntryOrCap_physical_endpoint
    hpsi2 hle2 hn5 1 0 ring5 capC [p0 hn5] cap_event


/-- Explicitly expose the cap branch, with empty executed prefix. -/
theorem n5_psi2_positive_cap_exact_branch :
    Local3PhysicalEndpoint hpsi2 hle2 hn5 1 0 ring5 capC [p0 hn5] := by
  exact Or.inr
    ⟨[], p0 hn5, [], rfl, safe0, Or.inl rfl,
      by simpa using n5_psi2_positive_cap_row⟩


/-- The cap fixture also retains the requested dirty/not-entry/outside checks. -/
theorem n5_psi2_positive_cap_source_audit :
    (raw (capC (p0 hn5))).reset = true /\
    (raw (capC (p0 hn5))).carry = true /\
    ¬ OrderedWaitEntry2 hn5 capC /\
    ¬ Passive (raw (capC (p3 hn5))) := by
  exact ⟨(source_dirty 1).1, (source_dirty 1).2.1,
    source_not_ordered 1, source_has_nonpassive_outside 1⟩


#print axioms BirthShortDoneTerminalPassiveLocal3FiniteAudit.n5_psi2_dirty_entry_before_cap
#print axioms BirthShortDoneTerminalPassiveLocal3FiniteAudit.n5_psi2_dirty_entry_public_endpoint
#print axioms BirthShortDoneTerminalPassiveLocal3FiniteAudit.n5_psi2_positive_cap_row
#print axioms BirthShortDoneTerminalPassiveLocal3FiniteAudit.n5_psi2_positive_cap_public_endpoint


end BirthShortDoneTerminalPassiveLocal3FiniteAudit
