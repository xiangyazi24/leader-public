import Leader.Wu.Splice.GarbageDrainTable

set_option autoImplicit false

/-! # V10e: V10d with every controller stutter replaced by a physical hold

Diagnosis behind LDR-BIRTH-B9-V10D-HANDOFF-DEADLOCK and the V9 fence orbit: a controller
HOLD placed ahead of the physical ordinary-host row blocks the physical protocol on that edge
forever.  V10e keeps rowV10d wherever it changes something and otherwise performs the physical
ordinary row with every controller field (role, repairPending, acquireTicket) kept, fencing a
relabelled neutral right follower exactly as ordinaryHostWriteV7 does. -/

namespace B9SpliceTableV10e

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness B9SpliceBlockDrainMass B9OrphanToFence B9SpliceTableV10d

variable {n psi width kappa tau : Nat}

/-- Physical step with the controller fields of both endpoints kept. -/
def physicalHoldV6 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := ordinaryRow hpsi hwidth hle l.carrier r.carrier
  let l' : R1AgentStateV6 psi kappa tau := ⟨q.1, l.acquireTicket⟩
  let r' : R1AgentStateV6 psi kappa tau := ⟨q.2, r.acquireTicket⟩
  if rightFollowerRelabelledV7 r.carrier q.2 then (l', setTicketV6 r' true) else (l', r')

/-- A left cell that certifies nothing: a non-pending victim or front, or a malformed pending
mark. -/
def LeftScrubGuardV10e (l : R1AgentStateV6 psi kappa tau) : Prop :=
  VictimLeftScrubGuardV6 l ∨ (role l.carrier = .front ∧ l.carrier.repairPending = false) ∨
    MalformedLeftPendingGuardV6 l

instance instDecLeftScrubGuardV10e (l : R1AgentStateV6 psi kappa tau) :
    Decidable (LeftScrubGuardV10e l) := by
  unfold LeftScrubGuardV10e; infer_instance

/-- Scrub rows of V6 that the fence and reservation HOLDs preempt: a non-pending victim or
front on the right, a malformed pending mark on the right.  Any predecessor on the right keeps
the V8-style stale HOLD: relabelling a predecessor from its incoming edge can strip the
protection of its outgoing repair edge (triple census); it drains at its own outgoing edge. -/
def rowV10e (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := rowV10d hpsi hwidth hle l r
  if q = (l, r) then
    if VictimRightScrubGuardV6 r then (l, clearControlV6 r)
    else if FrontRightScrubGuardV6 r then (l, clearControlV6 r)
    else if MalformedRightPendingGuardV6 r then (l, clearControlV6 r)
    else if role r.carrier = .predecessorArmed then
      if r.carrier.repairPending then
        -- a pending predecessor is legitimate only behind a settled predecessor (MoveCommit) or
        -- a neutral cell (V10d row 4); behind a reserved front it is cleared (the front certifies
        -- the edge), behind a certificate-free cell that cell is cleared first
        if ReservedFrontHoldGuard l.carrier then (l, clearControlV6 r)
        else if LeftScrubGuardV10e l then (clearControlV6 l, r)
        else (l, r)
      else
        -- settled predecessor on the right: physical step, then the relabelled predecessor
        -- becomes a host fence (its outgoing edge stays protected; a partner front is orphaned
        -- and fenced by the orphan row later)
        let q := physicalHoldV6 hpsi hwidth hle l r
        (q.1, fenceV6 q.2)
    else physicalHoldV6 hpsi hwidth hle l r
  else q

def stepV10e (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C else
    let q := rowV10e hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i

theorem physicalHold_role_left (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (physicalHoldV6 hpsi hwidth hle l r).1.carrier = role l.carrier := by
  simp only [physicalHoldV6]; split <;> rfl

theorem physicalHold_role_right (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (physicalHoldV6 hpsi hwidth hle l r).2.carrier = role r.carrier := by
  simp only [physicalHoldV6]; split <;> rfl


/-! ## Step shape and relative whole-step safety -/

/-- The physical hold as a configuration writer. -/
def physicalHoldAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let q := physicalHoldV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then q.1 else if i = ring.rightNeighbor e then q.2 else C i

section StepShape

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
  (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)

theorem stepV10e_self (hne : ring.rightNeighbor e = e) :
    stepV10e hpsi hwidth hle ring C e = C := by
  simp [stepV10e, hne]

theorem stepV10e_of_change (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ≠ (C e, C (ring.rightNeighbor e))) :
    stepV10e hpsi hwidth hle ring C e = stepV10d hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV10e, stepV10d, rowV10e, hne, if_false, h]

theorem stepV10e_of_victimScrub (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))) :
    stepV10e hpsi hwidth hle ring C e = orphanVictimClearAt ring C e := by
  funext i
  simp only [stepV10e, rowV10e, orphanVictimClearAt, hne, if_false, h, h1, if_true]
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · simp [hi]

theorem stepV10e_of_frontScrub (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))) :
    stepV10e hpsi hwidth hle ring C e = orphanVictimClearAt ring C e := by
  funext i
  simp only [stepV10e, rowV10e, orphanVictimClearAt, hne, if_false, h, h1, h2, if_true]
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · simp [hi]

theorem stepV10e_of_malformedScrub (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : ¬ FrontRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))) :
    stepV10e hpsi hwidth hle ring C e = orphanVictimClearAt ring C e := by
  funext i
  simp only [stepV10e, rowV10e, orphanVictimClearAt, hne, if_false, h, h1, h2, h3, if_true]
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · simp [hi]

theorem stepV10e_of_frontOwnedPredClear (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : ¬ FrontRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h3 : ¬ MalformedRightPendingGuardV6 (C (ring.rightNeighbor e)))
    (h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true)
    (h6 : ReservedFrontHoldGuard (C e).carrier) :
    stepV10e hpsi hwidth hle ring C e = orphanVictimClearAt ring C e := by
  funext i
  simp only [stepV10e, rowV10e, orphanVictimClearAt, hne, if_false, h, h1, h2, h3, h4, h5, h6, if_true]
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · simp [hi]

/-- The left scrub as a configuration writer. -/
def clearLeftAtV10e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then clearControlV6 (C e) else C i

theorem stepV10e_of_leftScrub (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : ¬ FrontRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h3 : ¬ MalformedRightPendingGuardV6 (C (ring.rightNeighbor e)))
    (h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true)
    (h6 : ¬ ReservedFrontHoldGuard (C e).carrier)
    (h7 : LeftScrubGuardV10e (C e)) :
    stepV10e hpsi hwidth hle ring C e = clearLeftAtV10e ring C e := by
  funext i
  simp only [stepV10e, rowV10e, clearLeftAtV10e, hne, if_false, h, h1, h2, h3, h4, h5, h6, h7, if_true]
  by_cases hi : i = e
  · subst hi; simp
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

theorem stepV10e_of_pendingPredHold (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : ¬ FrontRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h3 : ¬ MalformedRightPendingGuardV6 (C (ring.rightNeighbor e)))
    (h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true)
    (h6 : ¬ ReservedFrontHoldGuard (C e).carrier)
    (h7 : ¬ LeftScrubGuardV10e (C e)) :
    stepV10e hpsi hwidth hle ring C e = C := by
  funext i
  simp only [stepV10e, rowV10e, hne, if_false, h, h1, h2, h3, h4, h5, h6, h7, if_true]
  by_cases hi : i = e
  · subst hi; simp
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

/-- Physical hold followed by fencing the relabelled settled predecessor. -/
def physicalFenceAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let q := physicalHoldV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then q.1 else if i = ring.rightNeighbor e then fenceV6 q.2 else C i

theorem stepV10e_of_settledPredFence (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : ¬ FrontRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h3 : ¬ MalformedRightPendingGuardV6 (C (ring.rightNeighbor e)))
    (h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (h5 : (C (ring.rightNeighbor e)).carrier.repairPending = false) :
    stepV10e hpsi hwidth hle ring C e = physicalFenceAt hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV10e, rowV10e, physicalFenceAt, hne, if_false, h, h1, h2, h3, h4, h5, if_true,
    Bool.false_eq_true]

theorem stepV10e_of_physical (hne : ring.rightNeighbor e ≠ e)
    (h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)))
    (h1 : ¬ VictimRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h2 : ¬ FrontRightScrubGuardV6 (C (ring.rightNeighbor e)))
    (h3 : ¬ MalformedRightPendingGuardV6 (C (ring.rightNeighbor e)))
    (h4 : ¬ role (C (ring.rightNeighbor e)).carrier = .predecessorArmed) :
    stepV10e hpsi hwidth hle ring C e = physicalHoldAt hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV10e, rowV10e, physicalHoldAt, hne, if_false, h, h1, h2, h3, h4, if_true]

/-- Whole-step safety of V10e relative to (a) V10c whole-step safety and (b) safety of the
physical hold on a pair where V10d stutters and no scrub or stale hold applies. -/
theorem stepV10e_preserves_spliceSafeV7
    (hV10c : ∀ (D : R1ConfigV6 n psi kappa tau) (f : Fin n), SpliceSafeV7 hpsi ring D →
      SpliceSafeV7 hpsi ring (stepV10c hpsi hwidth hle ring D f))
    (hphys : ∀ (D : R1ConfigV6 n psi kappa tau) (f : Fin n), SpliceSafeV7 hpsi ring D →
      ring.rightNeighbor f ≠ f →
      rowV10d hpsi hwidth hle (D f) (D (ring.rightNeighbor f)) = (D f, D (ring.rightNeighbor f)) →
      ¬ VictimRightScrubGuardV6 (D (ring.rightNeighbor f)) →
      ¬ FrontRightScrubGuardV6 (D (ring.rightNeighbor f)) →
      ¬ MalformedRightPendingGuardV6 (D (ring.rightNeighbor f)) →
      ¬ role (D (ring.rightNeighbor f)).carrier = .predecessorArmed →
      SpliceSafeV7 hpsi ring (physicalHoldAt hpsi hwidth hle ring D f))
    (hfrontPred : ∀ (D : R1ConfigV6 n psi kappa tau) (f : Fin n), SpliceSafeV7 hpsi ring D →
      ReservedFrontHoldGuard (D f).carrier →
      role (D (ring.rightNeighbor f)).carrier = .predecessorArmed →
      (D (ring.rightNeighbor f)).carrier.repairPending = true →
      SpliceSafeV7 hpsi ring (orphanVictimClearAt ring D f))
    (hleftScrub : ∀ (D : R1ConfigV6 n psi kappa tau) (f : Fin n), SpliceSafeV7 hpsi ring D →
      LeftScrubGuardV10e (D f) → SpliceSafeV7 hpsi ring (clearLeftAtV10e ring D f))
    (hfence : ∀ (D : R1ConfigV6 n psi kappa tau) (f : Fin n), SpliceSafeV7 hpsi ring D →
      ring.rightNeighbor f ≠ f →
      rowV10d hpsi hwidth hle (D f) (D (ring.rightNeighbor f)) = (D f, D (ring.rightNeighbor f)) →
      role (D (ring.rightNeighbor f)).carrier = .predecessorArmed →
      (D (ring.rightNeighbor f)).carrier.repairPending = false →
      SpliceSafeV7 hpsi ring (physicalFenceAt hpsi hwidth hle ring D f))
    (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10e hpsi hwidth hle ring C e) := by
  by_cases hne : ring.rightNeighbor e = e
  · rw [stepV10e_self hpsi hwidth hle ring C e hne]; exact hS
  by_cases h : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))
  · by_cases h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_victimScrub hpsi hwidth hle ring C e hne h h1]
      refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
      · intro hf; exact absurd hf.1 (by rw [h1.1]; decide)
      · rw [h1.1]; decide
      · intro hv; exact absurd hv.2 (by rw [h1.2]; decide)
      · intro hf; exact absurd hf.1 (by rw [h1.1]; decide)
    by_cases h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_frontScrub hpsi hwidth hle ring C e hne h h1 h2]
      refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
      · intro hf; exact absurd hf.2 (by rw [h2.2]; decide)
      · rw [h2.1]; decide
      · intro hv; exact absurd hv.1 (by rw [h2.1]; decide)
      · intro hf; exact absurd hf.1 (by rw [h2.1]; decide)
    by_cases h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_malformedScrub hpsi hwidth hle ring C e hne h h1 h2 h3]
      refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
      · intro hf; exact h3.2.2.1 hf.1
      · exact h3.2.1
      · intro hv; exact h3.2.2.2 hv.1
      · intro hf; exact absurd hf.2.1 (by rw [h3.1]; decide)
    by_cases h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed
    · by_cases h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true
      · by_cases h6 : ReservedFrontHoldGuard (C e).carrier
        · rw [stepV10e_of_frontOwnedPredClear hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6]
          exact hfrontPred C e hS h6 h4 h5
        by_cases h7 : LeftScrubGuardV10e (C e)
        · rw [stepV10e_of_leftScrub hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
          exact hleftScrub C e hS h7
        · rw [stepV10e_of_pendingPredHold hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]; exact hS
      · have h5' : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
          cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
          · rfl
          · exact absurd hp h5
        rw [stepV10e_of_settledPredFence hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5']
        exact hfence C e hS hne h h4 h5'
    · rw [stepV10e_of_physical hpsi hwidth hle ring C e hne h h1 h2 h3 h4]
      exact hphys C e hS hne h h1 h2 h3 h4
  · rw [stepV10e_of_change hpsi hwidth hle ring C e hne h]
    exact stepV10d_preserves_spliceSafeV7 hpsi hwidth hle ring C e hV10c hS

end StepShape


/-! ## Frame facts for the physical hold -/

section HoldFrame

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
  (l r : R1AgentStateV6 psi kappa tau)

theorem physicalHold_left_carrier :
    (physicalHoldV6 hpsi hwidth hle l r).1.carrier =
      (ordinaryRow hpsi hwidth hle l.carrier r.carrier).1 := by
  simp only [physicalHoldV6]; split <;> rfl

theorem physicalHold_right_carrier :
    (physicalHoldV6 hpsi hwidth hle l r).2.carrier =
      (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 := by
  simp only [physicalHoldV6]; split <;> rfl

theorem physicalHold_left_ticket :
    (physicalHoldV6 hpsi hwidth hle l r).1.acquireTicket = l.acquireTicket := by
  simp only [physicalHoldV6]; split <;> rfl

theorem physicalHold_pending_left :
    (physicalHoldV6 hpsi hwidth hle l r).1.carrier.repairPending = l.carrier.repairPending := by
  rw [physicalHold_left_carrier]; rfl

theorem physicalHold_pending_right :
    (physicalHoldV6 hpsi hwidth hle l r).2.carrier.repairPending = r.carrier.repairPending := by
  rw [physicalHold_right_carrier]; rfl

theorem physicalHold_base_left :
    (physicalHoldV6 hpsi hwidth hle l r).1.carrier.splice.base =
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base).1 := by
  rw [physicalHold_left_carrier]; rfl

theorem physicalHold_base_right :
    (physicalHoldV6 hpsi hwidth hle l r).2.carrier.splice.base =
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base).2 := by
  rw [physicalHold_right_carrier]; rfl

/-- The physical hold and the V7 ordinary host agree on both carriers. -/
theorem physicalHold_carriers_eq_ordinaryHost :
    (physicalHoldV6 hpsi hwidth hle l r).1.carrier =
        (ordinaryHostWriteV7 hpsi hwidth hle l r).1.carrier ∧
      (physicalHoldV6 hpsi hwidth hle l r).2.carrier =
        (ordinaryHostWriteV7 hpsi hwidth hle l r).2.carrier := by
  simp only [physicalHoldV6, ordinaryHostWriteV7]
  split <;> exact ⟨rfl, rfl⟩

end HoldFrame

end B9SpliceTableV10e
