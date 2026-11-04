import Leader.Wu.Birth.LocalTripleContinuationBridge

namespace BirthB1NoUndoLaw

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthB1ReacquireReentryMass

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- Change only the already-bounded count coordinate. -/
def putCount
    (u : ExpiringAgentState psi kappa tau) (c : Fin (kappa + 1)) :
    ExpiringAgentState psi kappa tau :=
  { u with core := { u.core with core := { u.core.core with count := c } } }

@[simp] theorem putCount_self
    (u : ExpiringAgentState psi kappa tau) :
    putCount u u.core.core.count = u := by
  cases u with
  | mk a s =>
      cases a with
      | mk b p =>
          cases b
          rfl

@[simp] theorem putCount_putCount
    (u : ExpiringAgentState psi kappa tau)
    (a b : Fin (kappa + 1)) :
    putCount (putCount u a) b = putCount u b := by
  cases u with
  | mk c s =>
      cases c with
      | mk d p =>
          cases d
          rfl

/-- Constant-state guard: a row may raise/frame count, but never lower it. -/
def protectCount
    (old out : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau :=
  if out.core.core.count.val < old.core.core.count.val then
    putCount out old.core.core.count
  else out

theorem protectCount_nondec
    (old out : ExpiringAgentState psi kappa tau) :
    old.core.core.count.val <= (protectCount old out).core.core.count.val := by
  unfold protectCount
  split <;> rename_i h
  · simp [putCount]
  · exact Nat.le_of_not_gt h

/-- All non-count output state is exactly the current row output. -/
theorem protectCount_only_count
    (old out : ExpiringAgentState psi kappa tau) :
    putCount (protectCount old out) out.core.core.count = out := by
  unfold protectCount
  split
  · rw [putCount_putCount, putCount_self]
  · exact putCount_self out

/-- Proposed terminal-consumer row.  No carrier field is added. -/
def rowGuarded
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2 l r
  (protectCount l q.1, protectCount r q.2)

theorem rowGuarded_only_counts
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2 l r
    let g := rowGuarded hpsi h2 l r
    putCount g.1 q.1.core.core.count = q.1 /\
      putCount g.2 q.2.core.core.count = q.2 := by
  dsimp [rowGuarded]
  exact ⟨protectCount_only_count _ _, protectCount_only_count _ _⟩

/-- Ring lift of the guarded local row. -/
def stepGuarded
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) : FC n psi kappa tau :=
  let j := ring.rightNeighbor e
  let q := rowGuarded hpsi h2 (C e) (C j)
  fun i => if i = e then q.1 else if i = j then q.2 else C i

/-- Local core: no scheduler edge can lower the tracked count. -/
theorem stepGuarded_shortCount_nondec
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (anchor e : Fin n) (C : FC n psi kappa tau) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (stepGuarded hpsi h2 ring C e) := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  by_cases hL : ring.rightNeighbor anchor = e
  · have h := protectCount_nondec
      (C e)
      (BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1
    simpa [stepGuarded, rowGuarded, hL] using h
  · by_cases hR : ring.rightNeighbor anchor = ring.rightNeighbor e
    · by_cases hself : ring.rightNeighbor e = e
      · by_cases hn : 1 < n
        · have hne := rightNeighbor_ne_self_of_one_lt ring hn e
          exact False.elim (hne hself)
        · exact False.elim (hL (hR.trans hself))
      · have h := protectCount_nondec
          (C (ring.rightNeighbor e))
          (BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).2
        simpa [stepGuarded, rowGuarded, hL, hR, hself] using h
    · simp [stepGuarded, hL, hR]

/-- The requested controlled/target-free formulation; the guard is stronger
than the premise, so `Controlled` can be any consumer invariant. -/
def ControlledTargetFreeStep
    (Controlled : FC n psi kappa tau -> Prop)
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  Controlled C /\
    BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C [e] = false

theorem controlled_target_free_step_no_undo
    (Controlled : FC n psi kappa tau -> Prop)
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (anchor e : Fin n) (C : FC n psi kappa tau)
    (_h : ControlledTargetFreeStep
      (kappa := kappa) (tau := tau)
      Controlled hpsi h2 ring C e) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (stepGuarded hpsi h2 ring C e) :=
  stepGuarded_shortCount_nondec hpsi h2 ring anchor e C

/-- Executable prefix endpoint for the guarded consumer. -/
def guardedEndpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) :
    FC n psi kappa tau -> List (Fin n) -> FC n psi kappa tau
  | C, [] => C
  | C, e :: u => guardedEndpoint hpsi h2 ring
      (stepGuarded hpsi h2 ring C e) u

theorem guardedEndpoint_count_nondec
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (anchor : Fin n) (C : FC n psi kappa tau) (u : List (Fin n)) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (guardedEndpoint hpsi h2 ring C u) := by
  induction u generalizing C with
  | nil => exact Nat.le_refl _
  | cons e u ih =>
      exact Nat.le_trans
        (stepGuarded_shortCount_nondec hpsi h2 ring anchor e C)
        (ih (C := stepGuarded hpsi h2 ring C e))

theorem guardedEndpoint_append
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u v : List (Fin n)) :
    guardedEndpoint hpsi h2 ring C (u ++ v) =
      guardedEndpoint hpsi h2 ring
        (guardedEndpoint hpsi h2 ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e u ih =>
      exact ih (C := stepGuarded hpsi h2 ring C e)

/-- Producer-side premise: success already supplies either cap or a strict hit. -/
def PrefixHitBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : BirthPhaseWait2BlockProgress.DirtySuccessRel
      n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C ->
    forall u, u.length = BirthPhaseWait2BlockProgress.L n -> DirtySuccess C u ->
      BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = true \/
      exists hit tail, u = hit ++ tail /\
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (guardedEndpoint hpsi h2 ring C hit)

/-- Minimal consumer statement, now forced by one-step no-undo. -/
def PreservedPrefixProgressBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : BirthPhaseWait2BlockProgress.DirtySuccessRel
      n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C ->
    forall u, u.length = BirthPhaseWait2BlockProgress.L n -> DirtySuccess C u ->
      BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = true \/
      exists hit tail, u = hit ++ tail /\
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (guardedEndpoint hpsi h2 ring C hit) /\
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (guardedEndpoint hpsi h2 ring C hit) <=
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (guardedEndpoint hpsi h2 ring C u)

theorem preservedPrefixProgressBridge_of_hit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    (h : PrefixHitBridge hpsi h2 hn kappa tau ring anchor DirtySuccess) :
    PreservedPrefixProgressBridge hpsi h2 hn kappa tau ring anchor DirtySuccess := by
  intro C hR u hlen hdirty
  rcases h C hR u hlen hdirty with ht | ⟨hit, tail, hw, hgain⟩
  · exact Or.inl ht
  · right
    refine ⟨hit, tail, hw, hgain, ?_⟩
    rw [hw, guardedEndpoint_append]
    exact guardedEndpoint_count_nondec hpsi h2 ring anchor
      (guardedEndpoint hpsi h2 ring C hit) tail

end BirthB1NoUndoLaw

#print axioms BirthB1NoUndoLaw.protectCount_nondec
#print axioms BirthB1NoUndoLaw.protectCount_only_count
#print axioms BirthB1NoUndoLaw.stepGuarded_shortCount_nondec
#print axioms BirthB1NoUndoLaw.controlled_target_free_step_no_undo
#print axioms BirthB1NoUndoLaw.preservedPrefixProgressBridge_of_hit
