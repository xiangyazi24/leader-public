import Leader.Wu.Splice.HostTable
import Leader.Wu.Splice.AllPendingFixed
import Leader.Wu.Splice.HostQuiescence
import Init.Data.List.OfFn

/-!
# Host-parametric B9 controller garbage recovery

This module implements the controller-only recovery.
It does not alter any physical host row. `rowScrubH` removes malformed tickets
and unsupported pending predecessors. `rowRecoverH` additionally installs the
DELETE-shaped ownership pair on an uncovered prepared danger, without executing
the host or changing either physical base.

The old `SpliceSafeV7g` domain is observationally unchanged: none of the new
guards can fire there. The clear-only row is also inactive on every pair of
neutral controller cells, so the existing host-quiescence lift transfers to
`stepScrub` on the same scheduler word.

The global 6n descent/counting theorem remains a named PLAN target below; only
its short pair-local decrease facts are activated here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B9ControllerRecovery

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
open B9OrphanToFence B9SpliceTableV10g
open B9SpliceV10hControllerRowsSafe
open B9Host B9SpliceTableHost
open B9AllPendingFixed

variable {n psi kappa tau : Nat}

/-- The exact pending-predecessor cell whose outgoing backing is constrained
by `ProvenanceSafeV7`. -/
def Pending (u : Cell psi kappa tau) : Prop :=
  role u.carrier = .predecessorArmed ∧
  u.carrier.repairPending = true

/-- A true ticket is malformed exactly when it has neither of the two V7
meanings: reserved front or neutral host fence. -/
def BadTicket (u : Cell psi kappa tau) : Prop :=
  u.acquireTicket = true ∧
    ¬ (ReservedFrontHoldGuard u.carrier ∨ HostFenceShapeV7 u)

/-- The pending predecessor is missing the exact provenance backing required
by `ProvenanceSafeV7`: a reserved, unticketed right neighbour. -/
def BadBacking (l r : Cell psi kappa tau) : Prop :=
  Pending l ∧
    ¬ (ReservedFrontHoldGuard r.carrier ∧ r.acquireTicket = false)

/-- Pair-local form of `PreparedDangerAt`. -/
def LocalDanger (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Prop :=
  (preparedR1 hpsi l.carrier).core.leader = false ∧
    LocalPreparedBarrier hpsi l.carrier r.carrier

/-- Pair-local expansion of `ProtectedSpliceEdgeV7g`. -/
def PairCovered (l r : Cell psi kappa tau) : Prop :=
  ((ReservedFrontHoldGuard l.carrier ∨
      Pending r ∨
      (role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false ∧
        (ReservedFrontHoldGuard r.carrier ∨
          (role r.carrier = .victimArmed ∧
            r.carrier.repairPending = true) ∨
          Pending r))) ∨
    HostFenceShapeV7 l) ∨
  PendingOwnerHoldShapeV7 l r

/-- The geometric garbage class not repaired by ticket/backing scrubs alone. -/
def Hole (hpsi : 0 < psi) (l r : Cell psi kappa tau) : Prop :=
  LocalDanger hpsi l r ∧ ¬ PairCovered l r

/-- Garbage seen by the clear-only wrapper. -/
def ScrubGarbage (l r : Cell psi kappa tau) : Prop :=
  BadTicket l ∨ BadTicket r ∨ BadBacking l r

/-- Garbage seen by the complete recovery wrapper. -/
def Garbage (hpsi : 0 < psi) (l r : Cell psi kappa tau) : Prop :=
  ScrubGarbage l r ∨ Hole hpsi l r

/-- The recovery ownership installation. Both physical bases are retained.
`setControlV6` also clears both acquisition tickets. -/
def coverWrite (l r : Cell psi kappa tau) :
    Cell psi kappa tau × Cell psi kappa tau :=
  (setControlV6 l .predecessorArmed true,
    setControlV6 r .front true)

/-- Clear-only garbage recovery. -/
noncomputable def rowScrubH (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (l r : Cell psi kappa tau) :
    Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact if BadTicket l then (clearControlV6 l, r)
    else if BadTicket r then (l, clearControlV6 r)
    else if BadBacking l r then (clearControlV6 l, r)
    else rowB9 host hpsi l r

/-- Complete recovery: scrubs first, then installs local ownership on an
uncovered physical danger. -/
noncomputable def rowRecoverH (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (l r : Cell psi kappa tau) :
    Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact if BadTicket l then (clearControlV6 l, r)
    else if BadTicket r then (l, clearControlV6 r)
    else if BadBacking l r then (clearControlV6 l, r)
    else if Hole hpsi l r then coverWrite l r
    else rowB9 host hpsi l r

/-- Self edges cannot install two different roles in one physical cell. On a
malformed singleton we therefore use the clear-only endpoint action. -/
noncomputable def stepScrub (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) : Config n psi kappa tau := by
  classical
  exact if ring.rightNeighbor e = e then
    if ScrubGarbage (C e) (C e) then
      writeAt ring C e (clearControlV6 (C e), C e)
    else C
  else
    writeAt ring C e
      (rowScrubH host hpsi (C e) (C (ring.rightNeighbor e)))

/-- The complete recovery step. Safe self edges retain the old B9 hold. -/
noncomputable def stepRecover (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) : Config n psi kappa tau := by
  classical
  exact if ring.rightNeighbor e = e then
    if Garbage hpsi (C e) (C e) then
      writeAt ring C e (clearControlV6 (C e), C e)
    else C
  else
    writeAt ring C e
      (rowRecoverH host hpsi (C e) (C (ring.rightNeighbor e)))

/-- Existing quiescence-neutral controller state. -/
abbrev Neutral (u : Cell psi kappa tau) : Prop :=
  B9SpliceHostQuiescence.Neutral u

@[simp] theorem clearControl_neutral (u : Cell psi kappa tau) :
    Neutral (clearControlV6 u) := ⟨rfl, rfl, rfl⟩

@[simp] theorem clearControl_base (u : Cell psi kappa tau) :
    base (clearControlV6 u) = base u := rfl

@[simp] theorem coverWrite_bases (l r : Cell psi kappa tau) :
    base (coverWrite l r).1 = base l ∧
    base (coverWrite l r).2 = base r := ⟨rfl, rfl⟩

@[simp] theorem coverWrite_fields (l r : Cell psi kappa tau) :
    Pending (coverWrite l r).1 ∧
    ReservedFrontHoldGuard (coverWrite l r).2.carrier ∧
    (coverWrite l r).1.acquireTicket = false ∧
    (coverWrite l r).2.acquireTicket = false :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem localDanger_iff_at (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    LocalDanger hpsi (C e) (C (ring.rightNeighbor e)) ↔
      PreparedDangerAt hpsi ring (projectV6 C) e := by
  rfl

private theorem pairCovered_iff_at (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) :
    PairCovered (C e) (C (ring.rightNeighbor e)) ↔
      ProtectedSpliceEdgeV7g ring C e := by
  rfl

/-- The new guards are impossible on the existing safe domain. -/
theorem no_garbage_of_safe (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C)
    (e : Fin n) :
    ¬ Garbage hpsi (C e) (C (ring.rightNeighbor e)) := by
  intro hg
  rcases hg with (hL | hR | hB) | hH
  · exact hL.2 (hS.2.1 e hL.1)
  · exact hR.2 (hS.2.1 (ring.rightNeighbor e) hR.1)
  · exact hB.2 (hS.2.2 e hB.1.1 hB.1.2)
  · have hd : PreparedDangerAt hpsi ring (projectV6 C) e :=
      (localDanger_iff_at hpsi ring C e).mp hH.1
    have hc : PairCovered (C e) (C (ring.rightNeighbor e)) :=
      (pairCovered_iff_at ring C e).mpr (hS.1 e hd)
    exact hH.2 hc

/-- Pair-level safe-domain equality. -/
theorem rowRecoverH_eq_safe (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C)
    (e : Fin n) :
    rowRecoverH host hpsi (C e) (C (ring.rightNeighbor e)) =
      rowB9 host hpsi (C e) (C (ring.rightNeighbor e)) := by
  classical
  have hg := no_garbage_of_safe hpsi ring C hS e
  have hL : ¬ BadTicket (C e) := by
    intro h; exact hg (Or.inl (Or.inl h))
  have hR : ¬ BadTicket (C (ring.rightNeighbor e)) := by
    intro h; exact hg (Or.inl (Or.inr (Or.inl h)))
  have hB : ¬ BadBacking (C e) (C (ring.rightNeighbor e)) := by
    intro h; exact hg (Or.inl (Or.inr (Or.inr h)))
  have hH : ¬ Hole hpsi (C e) (C (ring.rightNeighbor e)) := by
    intro h; exact hg (Or.inr h)
  simp only [rowRecoverH, if_neg hL, if_neg hR, if_neg hB, if_neg hH]

/-- Whole-step equality on every old safe state. -/
theorem stepRecover_eq_stepB9_of_safe
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau)
    (hS : SpliceSafeV7g hpsi ring C) (e : Fin n) :
    stepRecover host hpsi ring C e = stepB9 host hpsi ring C e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hg : ¬ Garbage hpsi (C e) (C e) := by
      simpa only [hs] using no_garbage_of_safe hpsi ring C hS e
    simp only [stepRecover, stepB9, if_pos hs, if_neg hg]
  · have hr := rowRecoverH_eq_safe host hpsi ring C hS e
    simp only [stepRecover, stepB9, if_neg hs, hr]

private theorem neutral_not_badTicket (u : Cell psi kappa tau)
    (hN : Neutral u) : ¬ BadTicket u := by
  intro h
  have hb : false = true := hN.2.2.symm.trans h.1
  cases hb

private theorem neutral_not_badBacking
    (l r : Cell psi kappa tau) (hL : Neutral l) :
    ¬ BadBacking l r := by
  intro h
  have hr : SpliceRole.none = .predecessorArmed := hL.1.symm.trans h.1.1
  cases hr

/-- The clear-only wrapper is literally inactive on a neutral pair. -/
theorem rowScrubH_eq_neutral (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hL : Neutral l) (hR : Neutral r) :
    rowScrubH host hpsi l r = rowB9 host hpsi l r := by
  classical
  simp only [rowScrubH,
    if_neg (neutral_not_badTicket l hL),
    if_neg (neutral_not_badTicket r hR),
    if_neg (neutral_not_badBacking l r hL)]

/-- Configuration-level neutral equality, including the self-edge case. -/
theorem stepScrub_eq_stepB9_of_neutral
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau)
    (hN : ∀ i, Neutral (C i)) (e : Fin n) :
    stepScrub host hpsi ring C e = stepB9 host hpsi ring C e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hL := neutral_not_badTicket (C e) (hN e)
    have hB := neutral_not_badBacking (C e) (C e) (hN e)
    have hg : ¬ ScrubGarbage (C e) (C e) := by
      intro h
      rcases h with h | h | h
      · exact hL h
      · exact hL h
      · exact hB h
    simp only [stepScrub, stepB9, if_pos hs, if_neg hg]
  · have hr := rowScrubH_eq_neutral host hpsi
      (C e) (C (ring.rightNeighbor e)) (hN e) (hN _)
    simp only [stepScrub, stepB9, if_neg hs, hr]

/-- One quiet lifted host step is unchanged by the clear-only wrapper. -/
theorem stepScrub_lift (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 2 ≤ n)
    (B : PhysConfig n psi kappa tau) (e : Fin n)
    (hq : B9SpliceHostQuiescence.QuietAt host ring B e) :
    stepScrub host hpsi ring (B9SpliceHostQuiescence.lift B) e =
      B9SpliceHostQuiescence.lift (hostStep host ring B e) := by
  rw [stepScrub_eq_stepB9_of_neutral host hpsi ring _
    (fun i => B9SpliceHostQuiescence.lift_neutral B i) e]
  exact B9SpliceHostQuiescence.step_lift host hpsi ring hn B e hq

/-- Same original scheduler word as the existing quiescence theorem. -/
theorem runScrub_lift (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 2 ≤ n) :
    ∀ (w : List (Fin n)) (B : PhysConfig n psi kappa tau),
      B9SpliceHostQuiescence.QuietAlong host ring B w →
      w.foldl (stepScrub host hpsi ring)
          (B9SpliceHostQuiescence.lift B) =
        B9SpliceHostQuiescence.lift
          (w.foldl (hostStep host ring) B)
  | [], _, _ => rfl
  | e :: es, B, h => by
      change es.foldl (stepScrub host hpsi ring)
          (stepScrub host hpsi ring
            (B9SpliceHostQuiescence.lift B) e) =
        B9SpliceHostQuiescence.lift
          (es.foldl (hostStep host ring) (hostStep host ring B e))
      rw [stepScrub_lift host hpsi ring hn B e h.1]
      exact runScrub_lift host hpsi ring hn es _ h.2

/-! ## Fixed-family regression -/

private theorem pending_not_badTicket (x : Phys psi kappa tau) :
    ¬ BadTicket (pendingCell x) := by
  intro h
  have hb : (false : Bool) = true := h.1
  cases hb

private theorem pending_badBacking (l r : Phys psi kappa tau) :
    BadBacking (pendingCell l) (pendingCell r) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rintro ⟨hRF, _⟩
  exact pendingCell_not_reserved r hRF

private theorem cleared_not_badTicket (u : Cell psi kappa tau) :
    ¬ BadTicket (clearControlV6 u) := by
  intro h
  have hb : (false : Bool) = true := h.1
  cases hb

private theorem cleared_not_reserved (u : Cell psi kappa tau) :
    ¬ ReservedFrontHoldGuard (clearControlV6 u).carrier := by
  intro h
  have hr : SpliceRole.none = .front := h.1
  cases hr

/-- The recovery pair now actually consumes the all-pending garbage. -/
theorem rowRecover_pending_pending
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Phys psi kappa tau) :
    rowRecoverH host hpsi (pendingCell l) (pendingCell r) =
      (clearControlV6 (pendingCell l), pendingCell r) := by
  classical
  rw [rowRecoverH,
    if_neg (pending_not_badTicket l),
    if_neg (pending_not_badTicket r),
    if_pos (pending_badBacking l r)]

/-- A pending cell followed by a cell already cleared by recovery is consumed
on the next oppositely oriented service. -/
theorem rowRecover_pending_cleared
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Phys psi kappa tau) :
    rowRecoverH host hpsi (pendingCell l) (clearControlV6 (pendingCell r)) =
      (clearControlV6 (pendingCell l), clearControlV6 (pendingCell r)) := by
  classical
  have hB : BadBacking (pendingCell l) (clearControlV6 (pendingCell r)) := by
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    rintro ⟨hRF, _⟩
    exact cleared_not_reserved (pendingCell r) hRF
  rw [rowRecoverH,
    if_neg (pending_not_badTicket l),
    if_neg (cleared_not_badTicket (pendingCell r)),
    if_pos hB]

theorem allPending_not_fixed_recover
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (e : Fin n) (hself : ring.rightNeighbor e ≠ e) :
    stepRecover host hpsi ring (allPending X) e ≠ allPending X := by
  intro heq
  have hrow := rowRecover_pending_pending host hpsi
    (X e) (X (ring.rightNeighbor e))
  have hleft := congrArg (fun D : Config n psi kappa tau =>
    role (D e).carrier) heq
  unfold stepRecover at hleft
  rw [if_neg hself] at hleft
  rw [show (allPending X) e = pendingCell (X e) from rfl,
      show (allPending X) (ring.rightNeighbor e) =
        pendingCell (X (ring.rightNeighbor e)) from rfl,
      hrow, writeAt_e] at hleft
  change SpliceRole.none = SpliceRole.predecessorArmed at hleft
  cases hleft


/-- Concrete two-cell physical fixture; recovery never invokes this host on the
Q,Q regression, but fixing it to identity makes the whole regression closed. -/
def ring2 : DirectedRing 2 := ⟨by decide⟩

def idHost2 : HostRow (Phys 3 3 1) := ⟨fun l r => (l, r)⟩

def phys2 : Phys 3 3 1 := B9AllPendingFixed.cleanPhys3 (0 : Fin 3)

def x2 : PhysConfig 2 3 3 1 := fun _ => phys2

def qq2 : Config 2 3 3 1 := allPending x2

private theorem ring2_r0 : ring2.rightNeighbor (0 : Fin 2) = 1 := by decide
private theorem ring2_r1 : ring2.rightNeighbor (1 : Fin 2) = 0 := by decide

noncomputable def qq2After0 : Config 2 3 3 1 :=
  stepRecover idHost2 (by decide : 0 < 3) ring2 qq2 0


noncomputable def qq2After01 : Config 2 3 3 1 :=
  stepRecover idHost2 (by decide : 0 < 3) ring2 qq2After0 1


private theorem qq2After0_eq :
    qq2After0 =
      writeAt ring2 qq2 (0 : Fin 2)
        (clearControlV6 (pendingCell phys2), pendingCell phys2) := by
  change stepRecover idHost2 (by decide : 0 < 3) ring2 qq2
      (0 : Fin 2) = _
  unfold stepRecover
  have hs : ring2.rightNeighbor (0 : Fin 2) ≠ 0 := by decide
  rw [if_neg hs]
  rw [show qq2 (0 : Fin 2) = pendingCell phys2 from rfl,
      show qq2 (ring2.rightNeighbor (0 : Fin 2)) =
        pendingCell phys2 from rfl,
      rowRecover_pending_pending idHost2 (by decide : 0 < 3) phys2 phys2]

private theorem qq2After0_points :
    qq2After0 0 = clearControlV6 (pendingCell phys2) ∧
    qq2After0 1 = pendingCell phys2 := by
  rw [qq2After0_eq]
  constructor
  · exact writeAt_e ring2 qq2 (0 : Fin 2)
      (clearControlV6 (pendingCell phys2), pendingCell phys2)
  · have hs : ring2.rightNeighbor (0 : Fin 2) ≠ 0 := by decide
    have hj := writeAt_j ring2 qq2 (0 : Fin 2)
      (clearControlV6 (pendingCell phys2), pendingCell phys2) hs
    rw [ring2_r0] at hj
    exact hj


private theorem qq2After01_eq :
    qq2After01 =
      writeAt ring2 qq2After0 (1 : Fin 2)
        (clearControlV6 (pendingCell phys2),
          clearControlV6 (pendingCell phys2)) := by
  change stepRecover idHost2 (by decide : 0 < 3) ring2 qq2After0
      (1 : Fin 2) = _
  unfold stepRecover
  have hs : ring2.rightNeighbor (1 : Fin 2) ≠ 1 := by decide
  rw [if_neg hs]
  rw [ring2_r1, qq2After0_points.2, qq2After0_points.1,
      rowRecover_pending_cleared idHost2 (by decide : 0 < 3) phys2 phys2]

/-- The closed n=2 Q,Q regression: [0,1] clears both cells. -/
theorem qq2_after_01_neutral :
    Neutral (qq2After01 0) ∧ Neutral (qq2After01 1) := by
  rw [qq2After01_eq]
  have hs : ring2.rightNeighbor (1 : Fin 2) ≠ 1 := by decide
  constructor
  · have hj := writeAt_j ring2 qq2After0 (1 : Fin 2)
      (clearControlV6 (pendingCell phys2),
        clearControlV6 (pendingCell phys2)) hs
    rw [ring2_r1] at hj
    rw [hj]
    exact clearControl_neutral _
  · rw [writeAt_e]
    exact clearControl_neutral _


/-! ## Pair-local recovery rank -/

noncomputable def ind (P : Prop) : Nat := by
  classical
  exact if P then 1 else 0

/-- This is the local contribution used by the global `3*T + 2*B + U`
potential. It deliberately ignores faults on the two neighbouring edges. -/
noncomputable def pairRank (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Nat :=
  3 * ind (BadTicket l) +
  3 * ind (BadTicket r) +
  2 * ind (BadBacking l r) +
  ind (Hole hpsi l r)

private theorem clear_not_pending (u : Cell psi kappa tau) :
    ¬ Pending (clearControlV6 u) := by
  intro h
  have hr : SpliceRole.none = .predecessorArmed := h.1
  cases hr

private theorem clear_left_not_badBacking
    (l r : Cell psi kappa tau) :
    ¬ BadBacking (clearControlV6 l) r := by
  intro h
  exact clear_not_pending l h.1

private theorem badBacking_clearRight_implies_old
    (l r : Cell psi kappa tau) (hR : BadTicket r) :
    BadBacking l (clearControlV6 r) → BadBacking l r := by
  intro h
  refine ⟨h.1, ?_⟩
  rintro ⟨_, ht⟩
  have bad : true = false := hR.1.symm.trans ht
  cases bad

private theorem cover_not_badTicket_left (l r : Cell psi kappa tau) :
    ¬ BadTicket (coverWrite l r).1 := by
  intro h
  have bad : (false : Bool) = true := h.1
  cases bad

private theorem cover_not_badTicket_right (l r : Cell psi kappa tau) :
    ¬ BadTicket (coverWrite l r).2 := by
  intro h
  have bad : (false : Bool) = true := h.1
  cases bad

private theorem cover_not_badBacking (l r : Cell psi kappa tau) :
    ¬ BadBacking (coverWrite l r).1 (coverWrite l r).2 := by
  intro h
  apply h.2
  exact ⟨⟨rfl, rfl⟩, rfl⟩

private theorem cover_pairCovered (l r : Cell psi kappa tau) :
    PairCovered (coverWrite l r).1 (coverWrite l r).2 := by
  right
  exact ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem cover_not_hole (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) :
    ¬ Hole hpsi (coverWrite l r).1 (coverWrite l r).2 := by
  intro h
  exact h.2 (cover_pairCovered l r)

/-- First priority branch: clearing a malformed left ticket strictly lowers
this pair's weighted rank, regardless of the old/new hole bits. -/
theorem pairRank_clear_badTicket_left
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hL : BadTicket l) :
    pairRank hpsi (clearControlV6 l) r < pairRank hpsi l r := by
  classical
  have hcL := cleared_not_badTicket l
  have hcB := clear_left_not_badBacking l r
  by_cases hR : BadTicket r <;>
    by_cases hB : BadBacking l r <;>
    by_cases hI : Hole hpsi l r <;>
    by_cases hO : Hole hpsi (clearControlV6 l) r <;>
    simp [pairRank, ind, hL, hcL, hcB, hR, hB, hI, hO] <;> omega

/-- Second priority branch. A new backing fault after clearing the right cell
was already a backing fault before the clear because a bad ticket is true. -/
theorem pairRank_clear_badTicket_right
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hL : ¬ BadTicket l) (hR : BadTicket r) :
    pairRank hpsi l (clearControlV6 r) < pairRank hpsi l r := by
  classical
  have hcR := cleared_not_badTicket r
  by_cases hBO : BadBacking l (clearControlV6 r)
  · have hBI := badBacking_clearRight_implies_old l r hR hBO
    by_cases hI : Hole hpsi l r <;>
      by_cases hO : Hole hpsi l (clearControlV6 r) <;>
      simp [pairRank, ind, hL, hR, hcR, hBI, hBO, hI, hO] <;> omega
  · by_cases hBI : BadBacking l r <;>
      by_cases hI : Hole hpsi l r <;>
      by_cases hO : Hole hpsi l (clearControlV6 r) <;>
      simp [pairRank, ind, hL, hR, hcR, hBI, hBO, hI, hO] <;> omega

/-- Third priority branch. Weight two pays for at most one newly exposed served
hole after the unsupported pending predecessor is cleared. -/
theorem pairRank_clear_badBacking
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hL : ¬ BadTicket l) (hR : ¬ BadTicket r)
    (hB : BadBacking l r) :
    pairRank hpsi (clearControlV6 l) r < pairRank hpsi l r := by
  classical
  have hcL := cleared_not_badTicket l
  have hcB := clear_left_not_badBacking l r
  by_cases hI : Hole hpsi l r <;>
    by_cases hO : Hole hpsi (clearControlV6 l) r <;>
    simp [pairRank, ind, hL, hR, hB, hcL, hcB, hI, hO] <;> omega

/-- Fourth priority branch installs a complete local ownership certificate and
removes the sole remaining local unit of rank. -/
theorem pairRank_cover_hole
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hL : ¬ BadTicket l) (hR : ¬ BadTicket r)
    (hB : ¬ BadBacking l r) (hH : Hole hpsi l r) :
    pairRank hpsi (coverWrite l r).1 (coverWrite l r).2 <
      pairRank hpsi l r := by
  classical
  have hoL := cover_not_badTicket_left l r
  have hoR := cover_not_badTicket_right l r
  have hoB := cover_not_badBacking l r
  have hoH := cover_not_hole hpsi l r
  simp [pairRank, ind, hL, hR, hB, hH, hoL, hoR, hoB, hoH]

/-- Every actual recovery branch, before the old B9 fallback, strictly lowers
its served-pair rank. -/
theorem rowRecover_pairRank_lt
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (hg : Garbage hpsi l r) :
    pairRank hpsi (rowRecoverH host hpsi l r).1
        (rowRecoverH host hpsi l r).2 < pairRank hpsi l r := by
  classical
  by_cases hL : BadTicket l
  · rw [rowRecoverH, if_pos hL]
    exact pairRank_clear_badTicket_left hpsi l r hL
  · rw [rowRecoverH, if_neg hL]
    by_cases hR : BadTicket r
    · rw [if_pos hR]
      exact pairRank_clear_badTicket_right hpsi l r hL hR
    · rw [if_neg hR]
      by_cases hB : BadBacking l r
      · rw [if_pos hB]
        exact pairRank_clear_badBacking hpsi l r hL hR hB
      · rw [if_neg hB]
        have hH : Hole hpsi l r := by
          rcases hg with (a | a | a) | a
          · exact (hL a).elim
          · exact (hR a).elim
          · exact (hB a).elim
          · exact a
        rw [if_pos hH]
        exact pairRank_cover_hole hpsi l r hL hR hB hH

/-! ## Global potential vocabulary

The active definitions below are finite and executable. The global descent and
first-hit mass statements are intentionally left in PLAN comments until the
three-edge overlap bookkeeping is kernel-checked. -/

noncomputable def faultCount (P : Fin n → Prop) : Nat := by
  classical
  exact (List.ofFn (fun i : Fin n => if P i then 1 else 0)).foldl
    (fun a b : Nat => a + b) 0

noncomputable def ticketFaults (C : Config n psi kappa tau) : Nat :=
  faultCount (fun i => BadTicket (C i))

noncomputable def backingFaults (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Nat :=
  faultCount (fun i => BadBacking (C i) (C (ring.rightNeighbor i)))

noncomputable def holes (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Nat :=
  faultCount (fun i => Hole hpsi (C i) (C (ring.rightNeighbor i)))

/-- Weighted global candidate: `3*T + 2*B + U`. -/
noncomputable def recoveryPotential (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Nat :=
  3 * ticketFaults C + 2 * backingFaults ring C + holes hpsi ring C

/-- The requested first-hit target. -/
def RecoveryTarget (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Prop :=
  SpliceSafeV7g hpsi ring C ∨ ∀ i, Neutral (C i)

/-
PLAN -- exact global theorem targets; not declarations and not assumptions.

The local theorem `rowRecover_pairRank_lt` is insufficient by itself because
one service can alter fault status on the predecessor and successor edges. The
remaining proof is the three-edge census:

* clearing a BadTicket removes weight 3 and creates at most two holes;
* clearing BadBacking removes weight 2 and creates at most one hole;
* coverWrite creates no ticket/backing fault and removes at least its served
  hole, while its incoming/served/outgoing edges are protected.

For n = 2 the two exterior edges coincide and must be counted once.

The intended active theorem signatures are:

theorem recoveryPotential_le_six_mul
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    recoveryPotential hpsi ring C ≤ 6 * n

theorem recovery_descent
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau)
    (hnot : ¬ RecoveryTarget hpsi ring C) :
    ∃ e : Fin n,
      recoveryPotential hpsi ring (stepRecover host hpsi ring C e) <
        recoveryPotential hpsi ring C

theorem recovery_word
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) :
    ∃ w : List (Fin n), w.length ≤ 6 * n ∧
      RecoveryTarget hpsi ring
        (w.foldl (stepRecover host hpsi ring) C)

Using `BirthTwoStageEscape.avoidCount`, the coarse reciprocal-mass statement is
exactly (Q = n^(6*n), H = 6*n):

theorem recovery_first_hit_mass
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) :
    let H := 6 * n
    let Q := n ^ H
    Q * BirthTwoStageEscape.avoidCount
      (stepRecover host hpsi ring)
      (fun _ : Config n psi kappa tau => True)
      (RecoveryTarget hpsi ring) C H ≤
      (Q - 1) * n ^ H

A proof of `recovery_word` gives one successful word of length m ≤ H. Padding
that word gives n^(H-m) successful H-letter scheduler words, so the displayed
Q is conservative. No fairness or filtered-subword argument is needed.
-/

end B9ControllerRecovery
