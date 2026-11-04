import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleRotation

namespace BirthShortDoneTerminalPassiveLocal3RotationAudit

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Count
open BirthShortDoneTerminalPassiveLocal3Producer
open BirthShortDoneTerminalPassiveLocal3Mass
open BirthShortDoneTerminalPassiveLocal3Rotation
open FiniteUniformStoppingTree ControlledSchedulerMass

set_option autoImplicit false
set_option pp.structureInstances false
set_option Elab.async false

private theorem hpsi2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide
private theorem hn5 : 4 <= 5 := by decide

/-- The audit is genuinely anchored at the last physical site, not at zero. -/
def auditRing5 : DirectedRing 5 := ⟨by decide⟩
def auditAnchor4 : Fin 5 := ⟨4, by decide⟩

theorem anchor4_nonzero : auditAnchor4 ≠ (0 : Fin 5) := by
  decide

/-- Literal physical wraparound: the scheduler edge named 4 is 4 -> 0. -/
theorem anchor4_wrap :
    auditRing5.rightNeighbor auditAnchor4 = (0 : Fin 5) := by
  decide

/-- The fixed proof's excluded incoming boundary rotates to physical 3 -> 4.
In particular, physical 4 -> 0 is not that excluded boundary. -/
theorem rotated_leftCross_is_three :
    rotateIndex auditRing5 auditAnchor4 (leftCross hn5) = (3 : Fin 5) := by
  decide

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

/-- Deliberately nonpassive outside record.  Its label is also chosen so that
outside edge 2 -> 3 violates the global psi=2 successor-label equation. -/
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

/-- The physical Local3 triple is 4,0,1.  Sites 2 and 3 are deliberately
outside and nonpassive. -/
def auditRaw (i : Fin 5) : AgentState 2 :=
  if i.val = 4 then BirthWaitPassive.cell d0
  else if i.val = 0 then BirthWaitPassive.cell d1
  else if i.val = 1 then BirthWaitPassive.cell d2
  else BirthWaitPassive.cell dout

private theorem auditRaw_domain (i : Fin 5) :
    (auditRaw i).inProtocolDomain 1 := by
  simp [auditRaw, d0, d1, d2, dout,
    AgentState.inProtocolDomain, BirthWaitPassive.cell]

private def auditPack (i : Fin 5) : ExpiringAgentState 2 1 0 :=
  ⟨⟨BoundedAgentState.ofDomain (auditRaw i) (auditRaw_domain i), false⟩, 0⟩

def auditSource : FC 5 2 1 0 :=
  fun i => auditPack i

@[simp] private theorem raw_auditSource (i : Fin 5) :
    raw (auditSource i) = auditRaw i := by
  simp [auditSource, auditPack, raw, BoundedAgentState.erase_ofDomain]

/-- Exactly the arbitrary physical premise at anchor 4: the passive labelled
line is physical 4,0,1, hence it crosses n-1 -> 0. -/
theorem source_localLine3At :
    LocalLine3At hpsi2 hn5 auditRing5 auditAnchor4 auditSource := by
  refine {
    pass0 := ?_
    pass1 := ?_
    pass2 := ?_
    lab0 := ?_
    lab1 := ?_
    lab2 := ?_ }
  all_goals first | rfl | exact ⟨rfl, rfl, Or.inl rfl⟩

/-- A concrete full-record outside witness; no global passivity is present. -/
theorem source_has_nonpassive_outside :
    ¬ Passive (raw (auditSource (2 : Fin 5))) := by
  simp only [raw_auditSource]
  intro h
  have hw := h.2.1
  change false = true at hw
  cases hw

/-- This source does not already satisfy the fixed canonical LocalLine3 at
physical sites 0,1,2: site 0 has label 1 rather than 0. -/
theorem source_not_canonical_localLine3 :
    ¬ LocalLine3 hpsi2 hn5 auditSource := by
  intro h
  have hv := h.lab0
  simp [auditRaw, p0, d1, BirthWaitPassive.cell] at hv

/-- There is no hidden globally-cyclic-label premise either: outside edge
2 -> 3 carries 1 -> 1, whereas the psi=2 successor of 1 is 0. -/
theorem source_not_globally_cyclic_labels :
    ¬ (forall i : Fin 5,
      (raw (auditSource (auditRing5.rightNeighbor i))).label.val =
        ((raw (auditSource i)).label.val + 1) % 2) := by
  intro h
  have h23 := h (2 : Fin 5)
  change (1 : Nat) = 0 at h23
  cases h23

/-- Forward geometry on the literal scheduler alphabet: canonical [p0,p1]
is the physical word [4,0], in that order. -/
theorem physical_twoCross_word_forward :
    rotateWord auditRing5 auditAnchor4 [p0 hn5, p1 hn5] =
      [auditAnchor4, (0 : Fin 5)] := by
  simp [rotateWord, anchor4_wrap]

/-- The inverse used by the fixed-site matcher has the corresponding direction:
the original physical word [4,0] pulls back to canonical [p0,p1]. -/
theorem physical_twoCross_word_unrotates :
    unrotateWord auditRing5 auditAnchor4
        [auditAnchor4, (0 : Fin 5)] =
      [p0 hn5, p1 hn5] := by
  calc
    unrotateWord auditRing5 auditAnchor4
        [auditAnchor4, (0 : Fin 5)] =
      unrotateWord auditRing5 auditAnchor4
        (rotateWord auditRing5 auditAnchor4 [p0 hn5, p1 hn5]) := by
          rw [physical_twoCross_word_forward]
    _ = [p0 hn5, p1 hn5] :=
      unrotateWord_rotateWord auditRing5 auditAnchor4 [p0 hn5, p1 hn5]

theorem physical_twoCross_word_success :
    runWord (twoCrossStep hn5) (.active false)
      (unrotateWord auditRing5 auditAnchor4
        [auditAnchor4, (0 : Fin 5)]) = .success := by
  rw [physical_twoCross_word_unrotates]
  rfl

/-- Physical wrap edge 4 -> 0 is the rotated internal p0 edge, so it is both
safe and internal.  The excluded rotated incoming boundary is 3 -> 4. -/
private theorem safe_anchor4 :
    SafeLine3EdgeAt hn5 auditRing5 auditAnchor4 auditAnchor4 := by
  unfold SafeLine3EdgeAt SafeLine3Edge
  decide

private theorem internal_anchor4 :
    InternalLine3EdgeAt hn5 auditRing5 auditAnchor4 auditAnchor4 := by
  unfold InternalLine3EdgeAt InternalLine3Edge
  decide

/-- The physical responder at 0 starts strictly below the positive cap. -/
theorem cap_responder_count_zero :
    (raw (auditSource
      (auditRing5.rightNeighbor auditAnchor4))).count = 0 := by
  rw [anchor4_wrap]
  simp [auditRaw, d1, BirthWaitPassive.cell]

/-- Direct closed calculation on the actual physical 4 -> 0 pair: the repaired
pre-finish row raises the responder count from 0 to 1. -/
private theorem cap_wrap_preFinish :
    let s := preFinishEntry2 hpsi2 hle2 1
      (raw (auditSource auditAnchor4))
      (raw (auditSource
        (auditRing5.rightNeighbor auditAnchor4)))
    s.2.label = (1 : Fin 2) /\ s.2.count = 1 := by
  simp only [anchor4_wrap, raw_auditSource]
  decide

/-- Genuine positive current-row cap on the actual physical wrap edge 4 -> 0. -/
theorem positive_cap_on_physical_wrap :
    RowCap2 hpsi2 hle2 1 auditRing5 auditSource auditAnchor4 := by
  unfold RowCap2
  dsimp only
  rw [anchor4_wrap]
  have h := cap_wrap_preFinish
  dsimp only at h
  simpa [widthTerminal, anchor4_wrap] using h

/-- Independent target audit, not obtained by transporting an event target.
On literal physical word [4,0], pre=[] and current e=4, so RowCap2 is checked
on auditSource itself and the cap row has not been executed. -/
theorem physical_cap_exact_empty_prefix :
    Local3PhysicalEndpointAt hpsi2 hle2 hn5 1 0
      auditRing5 auditAnchor4 auditSource
      [auditAnchor4, (0 : Fin 5)] := by
  exact Or.inr
    ⟨[], auditAnchor4, [(0 : Fin 5)], rfl,
      safe_anchor4, internal_anchor4, positive_cap_on_physical_wrap⟩

/-- The public rotation consumer reaches that same literal physical target on
that same physical word.  Together with physical_cap_exact_empty_prefix this
cross-checks transport against an independently constructed target witness. -/
theorem public_matcher_endpoint_same_physical_word :
    Local3PhysicalEndpointAt hpsi2 hle2 hn5 1 0
      auditRing5 auditAnchor4 auditSource
      [auditAnchor4, (0 : Fin 5)] :=
  twoCross_success_physical_endpoint_at
    hpsi2 hle2 hn5 1 0 auditRing5 auditAnchor4 auditSource
    source_localLine3At [auditAnchor4, (0 : Fin 5)]
    physical_twoCross_word_success

/-- Concrete arbitrary-anchor mass specialization.  Its only Local3 premise is
the physical LocalLine3At witness above; this same source is noncanonical,
has a nonpassive outside record, and violates global cyclic labels outside. -/
theorem n5_psi2_anchor4_sixteenth :
    5^(4*5) <= 16 *
      actualEventCountAt hle2 hn5 1 0
        auditRing5 auditAnchor4 auditSource (4*5) :=
  local3_entry_or_cap_sixteenth_at
    hle2 hn5 1 0 auditRing5 auditAnchor4 auditSource
    source_localLine3At

#print axioms BirthShortDoneTerminalPassiveLocal3RotationAudit.physical_twoCross_word_unrotates
#print axioms BirthShortDoneTerminalPassiveLocal3RotationAudit.positive_cap_on_physical_wrap
#print axioms BirthShortDoneTerminalPassiveLocal3RotationAudit.physical_cap_exact_empty_prefix
#print axioms BirthShortDoneTerminalPassiveLocal3RotationAudit.public_matcher_endpoint_same_physical_word
#print axioms BirthShortDoneTerminalPassiveLocal3RotationAudit.n5_psi2_anchor4_sixteenth

end BirthShortDoneTerminalPassiveLocal3RotationAudit
