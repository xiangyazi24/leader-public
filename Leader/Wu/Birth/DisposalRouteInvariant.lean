import Leader.Wu.Birth.DisposalParametricWait

set_option autoImplicit false

namespace BirthDisposalRouteInvariant

open PPLL PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepPreCheckResetRepair BirthCheckCongestGuardRepair
  BirthSigMoveDisposalRepair

variable {psi kappa tau n : Nat}

/-! The pending-disposal repair is analyzed on its complete finite host.
The physical input predicate below includes either an already attached
deletion state or the original terminal action-three/action-four command.
No future execution property is included in this predicate.

The first contracts cover arbitrary other endpoint fields and all timer
values.  They are then lifted through the real ring scheduling semantics:
an attached carrier stays at its site until an incoming interaction deletes
it, and a contiguous present signal can be removed by backward service. -/

/-- A present component whose physical input already requests disposal. -/
def DisposalDue (hpsi : psi > 0) (u : AuthorizedAgentState psi) : Prop :=
  u.core.path ≠ .bot ∧
    (u.core.state = .eliminate_signal ∨
      pendingTerminalDisposal hpsi u.core = true)

/-- The leader, label, and identifier bit are unchanged by priority deletion. -/
def rulerView (u : AgentState psi) : Bool × Fin psi × Bool :=
  (u.leader, u.label, u.bit)

private theorem prepareDisposal_view (hpsi : psi > 0)
    (u : AuthorizedAgentState psi) :
    rulerView (prepareDisposal hpsi u).core = rulerView u.core := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem normalizeDeletion_view (u : AuthorizedAgentState psi) :
    rulerView (normalizeDeletion u).core = rulerView u.core := by
  unfold normalizeDeletion
  split <;> rfl

private theorem normalizeDeletion_path (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.path = u.core.path := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_due (hpsi : psi > 0)
    (u : AuthorizedAgentState psi) (hu : DisposalDue hpsi u) :
    (prepareDisposal hpsi u).core.state = .eliminate_signal := by
  rcases hu with ⟨hpath, hstate | hpending⟩
  · unfold prepareDisposal
    split
    · cases hp : u.core.path with
      | bot => exact (hpath hp).elim
      | some label bit => simp [markComparisonForDeletion, hp]
    · exact hstate
  · exact (prepareDisposal_pending hpsi u hpending hpath).1

private theorem normalized_prepared_due (hpsi : psi > 0)
    (u : AuthorizedAgentState psi) (hu : DisposalDue hpsi u) :
    normalizeDeletion (prepareDisposal hpsi u) = prepareDisposal hpsi u ∧
      deletionActive (prepareDisposal hpsi u) = true := by
  have hp : (prepareDisposal hpsi u).core.path ≠ .bot := by
    simpa only [prepareDisposal_path] using hu.1
  exact ⟨normalizeDeletion_eq_of_path_present _ hp,
    deletionActive_eq_true _ (prepareDisposal_due hpsi u hu) hp⟩

attribute [local irreducible]
  PPLLWallSweepFinite.wallSweepResetProbeAuthorizedBeforeCheck
  wallSweepLeaderSinkAfterCheckSuffix

/-- An input disposal at the responder selects only the existing deletion
branch.  Its payload is cleared; the predecessor keeps its own payload and
receives deletion unless its physical label is terminal.  Both ruler views
are framed, even when the predecessor contains arbitrary control garbage. -/
theorem due_responder_authorized
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hr : DisposalDue hpsi r) :
    let q := disposalAuthorizedTransition hpsi kappa l r
    q.2.core.path = .bot ∧ q.2.core.state = .none ∧
      q.1.core.path = l.core.path ∧
      rulerView q.1.core = rulerView l.core ∧
      rulerView q.2.core = rulerView r.core ∧
      (l.core.label ≠ ⟨psi - 1, by omega⟩ →
        q.1.core.state = .eliminate_signal) := by
  have hnr := (normalized_prepared_due hpsi r hr).1
  have hactive := (normalized_prepared_due hpsi r hr).2
  have hrs := prepareDisposal_due hpsi r hr
  have hlp := (normalizeDeletion_path (prepareDisposal hpsi l)).trans
    (prepareDisposal_path hpsi l)
  have hlv := (normalizeDeletion_view (prepareDisposal hpsi l)).trans
    (prepareDisposal_view hpsi l)
  have hrv := prepareDisposal_view hpsi r
  have hll : (normalizeDeletion (prepareDisposal hpsi l)).core.label = l.core.label :=
    congrArg (fun x : Bool × Fin psi × Bool => x.2.1) hlv
  unfold disposalAuthorizedTransition guardedAuthorizedTransition
  dsimp only
  rw [hnr]
  simp only [hactive, ↓reduceIte]
  unfold authorizedEliminateSig authorizedReconcile eliminateSig
  simp only [hrs, ↓reduceIte]
  split
  · exact ⟨True.intro, True.intro, hlp, hlv, hrv, fun _ => rfl⟩
  · rename_i hterminal
    exact ⟨True.intro, True.intro, hlp, hlv, hrv,
      fun h => (hterminal (hll ▸ h)).elim⟩

/-- A deleting initiator keeps exactly its own payload with the marker for
every responder state.  A deleting responder may itself be cleared; neither
priority branch transports the initiator's payload into it. -/
theorem due_initiator_authorized
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : DisposalDue hpsi l) :
    let q := disposalAuthorizedTransition hpsi kappa l r
    q.1.core.path = l.core.path ∧ q.1.core.state = .eliminate_signal ∧
      (q.2.core.path = r.core.path ∨ q.2.core.path = .bot) ∧
      rulerView q.1.core = rulerView l.core ∧
      rulerView q.2.core = rulerView r.core := by
  have hnl := (normalized_prepared_due hpsi l hl).1
  have hactive := (normalized_prepared_due hpsi l hl).2
  have hls := prepareDisposal_due hpsi l hl
  have hlp := prepareDisposal_path hpsi l
  have hrp := (normalizeDeletion_path (prepareDisposal hpsi r)).trans
    (prepareDisposal_path hpsi r)
  have hlv := prepareDisposal_view hpsi l
  have hrv := (normalizeDeletion_view (prepareDisposal hpsi r)).trans
    (prepareDisposal_view hpsi r)
  unfold disposalAuthorizedTransition guardedAuthorizedTransition
  dsimp only
  rw [hnl]
  split
  · rename_i hractive
    have hrs : (normalizeDeletion (prepareDisposal hpsi r)).core.state =
        .eliminate_signal := by
      have hh := hractive
      simp only [deletionActive, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact hh.1
    unfold authorizedEliminateSig authorizedReconcile eliminateSig
    simp only [hrs, ↓reduceIte]
    split
    · exact ⟨hlp, rfl, Or.inr True.intro, hlv, hrv⟩
    · exact ⟨hlp, hls, Or.inr True.intro, hlv, hrv⟩
  · exact ⟨hlp, hls, Or.inl hrp, hlv, hrv⟩

private theorem expiry_path_cases (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core.erase.core.path =
        out.core.erase.core.path ∨
      (deletionPriorityExpireOne tau old out).core.erase.core.path = .bot := by
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl

private theorem expiry_view (old out : ExpiringAgentState psi kappa tau) :
    rulerView (deletionPriorityExpireOne tau old out).core.erase.core =
      rulerView out.core.erase.core := by
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

private theorem expiry_state_none (old out : ExpiringAgentState psi kappa tau)
    (h : out.core.erase.core.state = .none) :
    (deletionPriorityExpireOne tau old out).core.erase.core.state = .none := by
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  split
  · exact h
  · split
    · exact h
    · split
      · rfl
      · exact h

private theorem clearLeaderSignal_fields (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.path = u.core.erase.core.path ∧
      (clearExpiringLeaderSignal u).core.erase.core.state = u.core.erase.core.state ∧
      rulerView (clearExpiringLeaderSignal u).core.erase.core =
        rulerView u.core.erase.core := by
  unfold clearExpiringLeaderSignal
  split <;> exact ⟨rfl, rfl, rfl⟩

attribute [local irreducible] guardedBoundedTransition

/-- The complete finite host pins an input disposal at the initiator for an
arbitrary responder, including another deleting component.  No timer value
or valid-ruler assumption is needed.  In particular, the input payload does
not escape through SIGMOVE while its command remains behind. -/
theorem due_initiator_full
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : DisposalDue hpsi l.core.erase) :
    let q := disposalFullTransition hpsi kappa tau l r
    q.1.core.erase.core.path = l.core.erase.core.path ∧
      q.1.core.erase.core.state = .eliminate_signal ∧
      (q.2.core.erase.core.path = r.core.erase.core.path ∨
        q.2.core.erase.core.path = .bot) ∧
      rulerView q.1.core.erase.core = rulerView l.core.erase.core ∧
      rulerView q.2.core.erase.core = rulerView r.core.erase.core := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := guardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have hf := due_initiator_authorized hpsi kappa l.core.erase r.core.erase hl
  rw [← erase_disposal_base hpsi kappa l.core r.core] at hf
  change q.1.erase.core.path = l.core.erase.core.path ∧
    q.1.erase.core.state = .eliminate_signal ∧
    (q.2.erase.core.path = r.core.erase.core.path ∨ q.2.erase.core.path = .bot) ∧
    rulerView q.1.erase.core = rulerView l.core.erase.core ∧
    rulerView q.2.erase.core = rulerView r.core.erase.core at hf
  have hactive := deletionActive_eq_true lOut.core.erase hf.2.1
    (by simpa only [lOut, hf.1] using hl.1)
  have heleft := deletionPriorityExpireOne_of_active tau l0 lOut hactive
  have heright : (deletionPriorityExpireOne tau r0 rOut).core.erase.core.path =
      r.core.erase.core.path ∨
      (deletionPriorityExpireOne tau r0 rOut).core.erase.core.path = .bot := by
    rcases expiry_path_cases r0 rOut with hp | hp
    · exact hf.2.2.1.imp (hp.trans ·) (hp.trans ·)
    · exact Or.inr hp
  have hlview := (expiry_view l0 lOut).trans hf.2.2.2.1
  have hrview := (expiry_view r0 rOut).trans hf.2.2.2.2
  change
    let z := initializeFollowerPairBirthSignals l0 r0
      (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)
    z.1.core.erase.core.path = l.core.erase.core.path ∧
      z.1.core.erase.core.state = .eliminate_signal ∧
      (z.2.core.erase.core.path = r.core.erase.core.path ∨
        z.2.core.erase.core.path = .bot) ∧
      rulerView z.1.core.erase.core = rulerView l.core.erase.core ∧
      rulerView z.2.core.erase.core = rulerView r.core.erase.core
  unfold initializeFollowerPairBirthSignals
  split
  · simp only [(clearLeaderSignal_fields _).1, (clearLeaderSignal_fields _).2.1,
      (clearLeaderSignal_fields _).2.2]
    exact ⟨by rw [heleft]; exact hf.1,
      by rw [heleft]; exact hf.2.1, heright, hlview, hrview⟩
  · exact ⟨by rw [heleft]; exact hf.1,
      by rw [heleft]; exact hf.2.1, heright, hlview, hrview⟩

/-- A responder's input disposal is consumed in one actual full interaction.
If the predecessor carries a nonterminal component, its exact payload receives
the deletion marker and survives expiry.  These are the two physical facts
needed for induction along a complete signal; the other fields are arbitrary. -/
theorem due_responder_full
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : DisposalDue hpsi r.core.erase) :
    let q := disposalFullTransition hpsi kappa tau l r
    q.2.core.erase.core.path = .bot ∧ q.2.core.erase.core.state = .none ∧
      rulerView q.1.core.erase.core = rulerView l.core.erase.core ∧
      rulerView q.2.core.erase.core = rulerView r.core.erase.core ∧
      (l.core.erase.core.path ≠ .bot →
        l.core.erase.core.label ≠ ⟨psi - 1, by omega⟩ →
        q.1.core.erase.core.path = l.core.erase.core.path ∧
          q.1.core.erase.core.state = .eliminate_signal) := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := guardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have hf := due_responder_authorized hpsi kappa l.core.erase r.core.erase hr
  rw [← erase_disposal_base hpsi kappa l.core r.core] at hf
  change q.2.erase.core.path = .bot ∧ q.2.erase.core.state = .none ∧
    q.1.erase.core.path = l.core.erase.core.path ∧
    rulerView q.1.erase.core = rulerView l.core.erase.core ∧
    rulerView q.2.erase.core = rulerView r.core.erase.core ∧
    (l.core.erase.core.label ≠ ⟨psi - 1, by omega⟩ →
      q.1.erase.core.state = .eliminate_signal) at hf
  have hrpath : (deletionPriorityExpireOne tau r0 rOut).core.erase.core.path =
      .bot := by
    rcases expiry_path_cases r0 rOut with hp | hp
    · exact hp.trans hf.1
    · exact hp
  have hrstate := expiry_state_none r0 rOut hf.2.1
  have hlview := (expiry_view l0 lOut).trans hf.2.2.2.1
  have hrview := (expiry_view r0 rOut).trans hf.2.2.2.2.1
  have hprop : l.core.erase.core.path ≠ .bot →
      l.core.erase.core.label ≠ ⟨psi - 1, by omega⟩ →
      (deletionPriorityExpireOne tau l0 lOut).core.erase.core.path =
          l.core.erase.core.path ∧
        (deletionPriorityExpireOne tau l0 lOut).core.erase.core.state =
          .eliminate_signal := by
    intro hlp hln
    have hls := hf.2.2.2.2.2 hln
    have ha := deletionActive_eq_true lOut.core.erase hls
      (by simpa only [lOut, hf.2.2.1] using hlp)
    rw [deletionPriorityExpireOne_of_active tau l0 lOut ha]
    exact ⟨hf.2.2.1, hls⟩
  change
    let z := initializeFollowerPairBirthSignals l0 r0
      (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)
    z.2.core.erase.core.path = .bot ∧ z.2.core.erase.core.state = .none ∧
      rulerView z.1.core.erase.core = rulerView l.core.erase.core ∧
      rulerView z.2.core.erase.core = rulerView r.core.erase.core ∧
      (l.core.erase.core.path ≠ .bot →
        l.core.erase.core.label ≠ ⟨psi - 1, by omega⟩ →
        z.1.core.erase.core.path = l.core.erase.core.path ∧
          z.1.core.erase.core.state = .eliminate_signal)
  unfold initializeFollowerPairBirthSignals
  split
  · simp only [(clearLeaderSignal_fields _).1, (clearLeaderSignal_fields _).2.1,
      (clearLeaderSignal_fields _).2.2]
    exact ⟨hrpath, hrstate, hlview, hrview, hprop⟩
  · exact ⟨hrpath, hrstate, hlview, hrview, hprop⟩

attribute [local irreducible] disposalFullTransition

/-- No actual moved-right event can carry an input disposal out of its site.
This is a contract for the same event used by authorized SIGMOVE, evaluated
on the complete repaired transition. -/
theorem due_has_no_moved_right_event
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : DisposalDue hpsi l.core.erase) :
    let q := disposalFullTransition hpsi kappa tau l r
    pathMovedRight l.core.erase.core r.core.erase.core
      q.1.core.erase.core q.2.core.erase.core = false := by
  have hp := (due_initiator_full hpsi kappa tau l r hl).1
  simp only [pathMovedRight, hp, hl.1, decide_false, Bool.and_false, Bool.false_and]

private theorem due_step_before_incoming
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (i e : Fin n)
    (hi : DisposalDue hpsi (C i).core.erase)
    (he : ring.rightNeighbor e ≠ i) :
    let D := localStep ring (disposalFullTransition hpsi kappa tau) C e
    (D i).core.erase.core.path = (C i).core.erase.core.path ∧
      DisposalDue hpsi (D i).core.erase := by
  by_cases hei : i = e
  · subst e
    have h := due_initiator_full hpsi kappa tau (C i)
      (C (ring.rightNeighbor i)) hi
    simp only [localStep, ↓reduceIte]
    exact ⟨h.1, by simpa only [h.1] using hi.1, Or.inl h.2.1⟩
  · simp only [localStep, hei, Ne.symm he, ↓reduceIte]
    exact ⟨True.intro, hi⟩

/-- Under every finite schedule with no incoming service at the marked site,
the same physical payload remains there and still requests disposal.  Other
edges and endpoint fields are unrestricted.  This proves persistence from
the transition, rather than requiring a future route invariant as an input. -/
theorem disposal_stays_until_incoming
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (i : Fin n)
    (word : DetSchedule n) (hi : DisposalDue hpsi (C i).core.erase)
    (havoid : ∀ e ∈ word, ring.rightNeighbor e ≠ i) :
    let D := runLocalSchedule ring (disposalFullTransition hpsi kappa tau) C word
    (D i).core.erase.core.path = (C i).core.erase.core.path ∧
      DisposalDue hpsi (D i).core.erase := by
  induction word generalizing C with
  | nil => exact ⟨rfl, hi⟩
  | cons e rest ih =>
      have hstep := due_step_before_incoming ring hpsi kappa tau C i e hi
        (havoid e (by simp))
      have hrest := ih _ hstep.2 (fun f hf => havoid f (by simp [hf]))
      exact ⟨hrest.1.trans hstep.1, hrest.2⟩

/-- The first incoming edge after any intervening schedule deletes the
designated payload at its original site.  The schedule prefix carries no
fairness assumption: it merely identifies the actual first incoming service. -/
theorem first_incoming_consumes_disposal
    (ring : DirectedRing n) (hn : 1 < n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (i e : Fin n)
    (word : DetSchedule n) (hi : DisposalDue hpsi (C i).core.erase)
    (havoid : ∀ f ∈ word, ring.rightNeighbor f ≠ i)
    (hnext : ring.rightNeighbor e = i) :
    let D := runLocalSchedule ring (disposalFullTransition hpsi kappa tau) C word
    let E := localStep ring (disposalFullTransition hpsi kappa tau) D e
    (D i).core.erase.core.path = (C i).core.erase.core.path ∧
      (E i).core.erase.core.path = .bot ∧
      (E i).core.erase.core.state = .none := by
  let D := runLocalSchedule ring (disposalFullTransition hpsi kappa tau) C word
  have hd := disposal_stays_until_incoming ring hpsi kappa tau C i word hi havoid
  have hpair := due_responder_full hpsi kappa tau (D e) (D i) hd.2
  have hne : i ≠ e := by
    rw [← hnext]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  exact ⟨hd.1, by simpa only [localStep, hne, hnext, ↓reduceIte] using hpair.1,
    by simpa only [localStep, hne, hnext, ↓reduceIte] using hpair.2.1⟩

private theorem run_away {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Fin n → Q) (word : DetSchedule n) (i : Fin n)
    (havoid : ∀ e ∈ word, i ≠ e ∧ i ≠ ring.rightNeighbor e) :
    runLocalSchedule ring T C word i = C i := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      have he := havoid e (by simp)
      have hr := ih (localStep ring T C e)
        (fun f hf => havoid f (by simp [hf]))
      exact hr.trans (by simp only [localStep, he.1, he.2, ↓reduceIte])

/-- Explicit predecessor service order for sites `nodes 1` through `nodes m`.
The last component is serviced first, and each following edge consumes the
marker just propagated to the preceding component. -/
def deletionWord (nodes : Nat → Fin n) : Nat → DetSchedule n
  | 0 => []
  | m + 1 => nodes m :: deletionWord nodes m

theorem deletionWord_length (nodes : Nat → Fin n) (m : Nat) :
    (deletionWord nodes m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [deletionWord, List.length_cons, ih]

private theorem mem_deletionWord (nodes : Nat → Fin n) (m : Nat) (e : Fin n)
    (he : e ∈ deletionWord nodes m) : ∃ k, k < m ∧ e = nodes k := by
  induction m with
  | zero => simp [deletionWord] at he
  | succ m ih =>
      simp only [deletionWord, List.mem_cons] at he
      rcases he with he | he
      · exact ⟨m, by omega, he⟩
      · rcases ih he with ⟨k, hk, he⟩
        exact ⟨k, by omega, he⟩

/-- Snapshot description of an actual backward deletion prefix.  Sites above
the frontier have been cleared, lower present payloads are unchanged, and the
frontier itself carries the next disposal.  The global ruler view is fixed.
This is a derived output invariant, not a guard or a physical state field. -/
def DisposalFrontier (hpsi : psi > 0)
    (initial current : Fin n → ExpiringAgentState psi kappa tau)
    (nodes : Nat → Fin n) (frontier last : Nat) : Prop :=
  (∀ i, rulerView (current i).core.erase.core =
    rulerView (initial i).core.erase.core) ∧
  (∀ k, 0 < k → k ≤ frontier →
    (current (nodes k)).core.erase.core.path =
      (initial (nodes k)).core.erase.core.path) ∧
  (∀ k, frontier < k → k ≤ last →
    (current (nodes k)).core.erase.core.path = .bot ∧
      (current (nodes k)).core.erase.core.state = .none) ∧
  (0 < frontier → DisposalDue hpsi (current (nodes frontier)).core.erase)

/-- Every prefix of the explicit backward service word has exactly the
claimed physical deletion frontier.  Only the initial contiguous paths,
initial nonterminal interior labels, terminal disposal, and finite corridor
geometry are assumed.  The complete host itself supplies all intermediate
marker persistence, path preservation, and absence of new leaders. -/
theorem deletion_route_invariant
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (nodes : Nat → Fin n) (m : Nat)
    (hinj : ∀ i j, i ≤ m → j ≤ m → nodes i = nodes j → i = j)
    (hadj : ∀ k, k < m → ring.rightNeighbor (nodes k) = nodes (k + 1))
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hpaths : ∀ k, 0 < k → k ≤ m → (C (nodes k)).core.erase.core.path ≠ .bot)
    (hlabels : ∀ k, 0 < k → k < m →
      (C (nodes k)).core.erase.core.label ≠ ⟨psi - 1, by omega⟩)
    (hdue : 0 < m → DisposalDue hpsi (C (nodes m)).core.erase)
    (t : Nat) (ht : t ≤ m) :
    DisposalFrontier hpsi C
      (runLocalSchedule ring (disposalFullTransition hpsi kappa tau)
        C ((deletionWord nodes m).take t)) nodes (m - t) m := by
  induction m generalizing C t with
  | zero =>
      have ht0 : t = 0 := by omega
      subst t
      exact ⟨fun _ => rfl, by omega, by omega, by omega⟩
  | succ m ih =>
      cases t with
      | zero =>
          exact ⟨fun _ => rfl, fun _ _ _ => rfl, by omega, hdue⟩
      | succ t =>
          have ht' : t ≤ m := by omega
          let T := disposalFullTransition hpsi kappa tau
          let D := localStep ring T C (nodes m)
          have hadjm := hadj m (by omega)
          have hne : nodes (m + 1) ≠ nodes m := by
            intro he
            have hi := hinj (m + 1) m (by omega) (by omega) he
            omega
          have hf := due_responder_full hpsi kappa tau (C (nodes m))
            (C (nodes (m + 1))) (hdue (by omega))
          have hcleared : (D (nodes (m + 1))).core.erase.core.path = .bot ∧
              (D (nodes (m + 1))).core.erase.core.state = .none := by
            simpa only [D, localStep, hadjm, hne, ↓reduceIte, T] using
              And.intro hf.1 hf.2.1
          have hview : ∀ i, rulerView (D i).core.erase.core =
              rulerView (C i).core.erase.core := by
            intro i
            by_cases hi : i = nodes m
            · subst i
              simpa only [D, localStep, hadjm, ↓reduceIte, T] using hf.2.2.1
            · by_cases hj : i = nodes (m + 1)
              · subst i
                simpa only [D, localStep, hadjm, hi, ↓reduceIte, T] using
                  hf.2.2.2.1
              · simp only [D, localStep, hadjm, hi, hj, ↓reduceIte]
          have hprop (hm : 0 < m) :
              (D (nodes m)).core.erase.core.path = (C (nodes m)).core.erase.core.path ∧
                (D (nodes m)).core.erase.core.state = .eliminate_signal := by
            simpa only [D, localStep, hadjm, ↓reduceIte, T] using
              hf.2.2.2.2 (hpaths m hm (by omega)) (hlabels m hm (by omega))
          have hpathKeep : ∀ k, 0 < k → k ≤ m →
              (D (nodes k)).core.erase.core.path = (C (nodes k)).core.erase.core.path := by
            intro k hk hkm
            by_cases hkm' : k = m
            · subst k
              exact (hprop hk).1
            · have hkne : nodes k ≠ nodes m := by
                intro he
                exact hkm' (hinj k m (by omega) (by omega) he)
              have hkne' : nodes k ≠ nodes (m + 1) := by
                intro he
                have hh := hinj k (m + 1) (by omega) (by omega) he
                omega
              simp only [D, localStep, hadjm, hkne, hkne', ↓reduceIte]
          have hpathsD : ∀ k, 0 < k → k ≤ m →
              (D (nodes k)).core.erase.core.path ≠ .bot := by
            intro k hk hkm
            rw [hpathKeep k hk hkm]
            exact hpaths k hk (by omega)
          have hlabelsD : ∀ k, 0 < k → k < m →
              (D (nodes k)).core.erase.core.label ≠ ⟨psi - 1, by omega⟩ := by
            intro k hk hkm
            have hv := congrArg (fun x : Bool × Fin psi × Bool => x.2.1)
              (hview (nodes k))
            change (D (nodes k)).core.erase.core.label =
              (C (nodes k)).core.erase.core.label at hv
            rw [hv]
            exact hlabels k hk (by omega)
          have hdueD : 0 < m → DisposalDue hpsi (D (nodes m)).core.erase := by
            intro hm
            exact ⟨hpathsD m hm (by omega), Or.inl (hprop hm).2⟩
          have hi := ih
            (fun i j hi hj he => hinj i j (by omega) (by omega) he)
            (fun k hk => hadj k (by omega)) D hpathsD hlabelsD hdueD t ht'
          let E := runLocalSchedule ring T D ((deletionWord nodes m).take t)
          have hlast : E (nodes (m + 1)) = D (nodes (m + 1)) := by
            apply run_away
            intro e he
            have hemem : e ∈ deletionWord nodes m := List.mem_of_mem_take he
            rcases mem_deletionWord nodes m e hemem with ⟨k, hk, he⟩
            subst e
            constructor
            · intro he
              have hh := hinj (m + 1) k (by omega) (by omega) he
              omega
            · rw [hadj k (by omega)]
              intro he
              have hh := hinj (m + 1) (k + 1) (by omega) (by omega) he
              omega
          rw [show m + 1 - (t + 1) = m - t by omega]
          change DisposalFrontier hpsi C E nodes (m - t) (m + 1)
          refine ⟨fun i => (hi.1 i).trans (hview i), ?_, ?_, hi.2.2.2⟩
          · intro k hk hkt
            exact (hi.2.1 k hk hkt).trans (hpathKeep k hk (by omega))
          · intro k hkt hkm
            by_cases hlastk : k = m + 1
            · subst k
              rw [hlast]
              exact hcleared
            · exact hi.2.2.1 k hkt (by omega)

/-- A complete `psi`-component signal with pending terminal disposal is
physically removed in exactly `psi` interactions.  Every prefix preserves
all leader bits, ruler labels, and identifier bits.  This is the explicit
service consequence of the general route invariant, for arbitrary timers. -/
theorem complete_signal_disposal_service
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (nodes : Nat → Fin n)
    (hinj : ∀ i j, i ≤ psi → j ≤ psi → nodes i = nodes j → i = j)
    (hadj : ∀ k, k < psi → ring.rightNeighbor (nodes k) = nodes (k + 1))
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hpaths : ∀ k, 0 < k → k ≤ psi →
      (C (nodes k)).core.erase.core.path ≠ .bot)
    (hlabels : ∀ k, 0 < k → k < psi →
      (C (nodes k)).core.erase.core.label ≠ ⟨psi - 1, by omega⟩)
    (hdue : DisposalDue hpsi (C (nodes psi)).core.erase) :
    (deletionWord nodes psi).length = psi ∧
      (∀ t, t ≤ psi → ∀ i,
        rulerView (runLocalSchedule ring (disposalFullTransition hpsi kappa tau)
          C ((deletionWord nodes psi).take t) i).core.erase.core =
          rulerView (C i).core.erase.core) ∧
      (∀ k, 0 < k → k ≤ psi →
        let D := runLocalSchedule ring (disposalFullTransition hpsi kappa tau)
          C (deletionWord nodes psi)
        (D (nodes k)).core.erase.core.path = .bot ∧
          (D (nodes k)).core.erase.core.state = .none) := by
  refine ⟨deletionWord_length nodes psi, ?_, ?_⟩
  · intro t ht
    exact (deletion_route_invariant ring hpsi kappa tau nodes psi hinj hadj C
      hpaths hlabels (fun _ => hdue) t ht).1
  · intro k hk hkp
    have h := (deletion_route_invariant ring hpsi kappa tau nodes psi hinj hadj C
      hpaths hlabels (fun _ => hdue) psi (by omega)).2.2.1 k (by omega) hkp
    have htake : (deletionWord nodes psi).take psi = deletionWord nodes psi := by
      calc
        (deletionWord nodes psi).take psi =
            (deletionWord nodes psi).take (deletionWord nodes psi).length :=
          congrArg (fun k => (deletionWord nodes psi).take k)
            (deletionWord_length nodes psi).symm
        _ = _ := List.take_length
    simpa only [htake] using h

/-! The actual complete-signal mismatch discovered by the independent audit
enters the general theorem above.  This witness checks only the present route
entry; all deletion-prefix conclusions are supplied by the generic proof. -/

open BirthFullHostRulerCounterexample BirthFullHostWaitedRulerCounterexample

/-- The two-cell target group in the actual eighteen-step mismatch trace,
with its preceding terminal as site zero. -/
def mismatchNodes (k : Nat) : Fin 8 := ⟨(k + 1) % 8, by omega⟩

private theorem get_ofFn {Q : Type} (C : Fin 8 → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {Q : Type} (T : Q → Q → Q × Q) :
    DetSchedule 8 → Vector Q 8 → Vector Q 8
  | [], C => C
  | e :: rest, C => cachedRun T rest (Vector.ofFn (localStep ringEight T C.get e))

private theorem cachedRun_correct {Q : Type} (T : Q → Q → Q × Q)
    (C : Fin 8 → Q) (word : DetSchedule 8) :
    (cachedRun T word (Vector.ofFn C)).get = runLocalSchedule ringEight T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

attribute [local semireducible] disposalFullTransition guardedBoundedTransition
  PPLLWallSweepFinite.wallSweepResetProbeAuthorizedBeforeCheck
  wallSweepLeaderSinkAfterCheckSuffix

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- After the real full host performs WAIT, one complete GEN, transport, and
the unequal CHECK, both original components are still together at sites two
and three and the terminal carries the actual pending disposal command. -/
theorem actual_mismatch_enters_disposal_route :
    (disposalRegressionPrefix 13 2).core.erase.core.path = .some 0 0 ∧
      (disposalRegressionPrefix 13 3).core.erase.core.path = .some 1 0 ∧
      (disposalRegressionPrefix 13 2).core.erase.core.label = 0 ∧
      pendingTerminalDisposal (by omega)
        (disposalRegressionPrefix 13 3).core.erase.core = true := by
  unfold disposalRegressionPrefix
  simp only [← cachedRun_correct]
  decide

attribute [local irreducible] disposalFullTransition

/-- The checked real mismatch is consumed by the general route invariant.
The two-edge word is `[2, 1]`; every prefix preserves the whole ruler view
and clears exactly the serviced suffix of the complete signal. -/
theorem actual_mismatch_has_general_deletion_route (t : Nat) (ht : t ≤ 2) :
    DisposalFrontier (by omega) (disposalRegressionPrefix 13)
      (runLocalSchedule ringEight (disposalFullTransition (by omega) 2 16)
        (disposalRegressionPrefix 13) ((deletionWord mismatchNodes 2).take t))
      mismatchNodes (2 - t) 2 := by
  have hw := actual_mismatch_enters_disposal_route
  apply deletion_route_invariant
  · intro i j hi hj he
    have hv := congrArg Fin.val he
    change (i + 1) % 8 = (j + 1) % 8 at hv
    omega
  · intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> decide
  · intro k hk hle
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · change (disposalRegressionPrefix 13 2).core.erase.core.path ≠ .bot
      rw [hw.1]
      intro h
      cases h
    · change (disposalRegressionPrefix 13 3).core.erase.core.path ≠ .bot
      rw [hw.2.1]
      intro h
      cases h
  · intro k hk hlt
    have hk' : k = 1 := by omega
    subst k
    change (disposalRegressionPrefix 13 2).core.erase.core.label ≠ _
    rw [hw.2.2.1]
    intro he
    have hv := congrArg Fin.val he
    change (0 : Nat) = 1 at hv
    omega
  · intro _
    refine ⟨?_, Or.inr hw.2.2.2⟩
    change (disposalRegressionPrefix 13 3).core.erase.core.path ≠ .bot
    rw [hw.2.1]
    intro h
    cases h
  · exact ht

end BirthDisposalRouteInvariant

#print axioms BirthDisposalRouteInvariant.due_initiator_full
#print axioms BirthDisposalRouteInvariant.due_responder_full
#print axioms BirthDisposalRouteInvariant.due_has_no_moved_right_event
#print axioms BirthDisposalRouteInvariant.disposal_stays_until_incoming
#print axioms BirthDisposalRouteInvariant.first_incoming_consumes_disposal
#print axioms BirthDisposalRouteInvariant.deletion_route_invariant
#print axioms BirthDisposalRouteInvariant.complete_signal_disposal_service
#print axioms BirthDisposalRouteInvariant.actual_mismatch_enters_disposal_route
#print axioms BirthDisposalRouteInvariant.actual_mismatch_has_general_deletion_route
