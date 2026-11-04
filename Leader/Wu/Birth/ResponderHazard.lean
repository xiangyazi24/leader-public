import Leader.Wu.Birth.MismatchDisposalProducer

/-!
# Actual responder expiry and priority service in the action-one host

These are physical timer and deletion statements for the named old host.
A changed progress view is reported as a refresh, not as generation loss.
The separate stage audit must explain such a refresh before any generation
hazard conclusion can use it. No fixed-neighbor assumption occurs below.
-/

set_option autoImplicit false

namespace BirthResponderHazard

open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepPreCheckResetRepair PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoProtocol BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer

variable {n psi kappa tau : Nat}

def basePair (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := actionOneGuardedBoundedTransition hpsi kappa l0.core r0.core
  (⟨q.1, l0.stall⟩, ⟨q.2, r0.stall⟩)

/-- Exact fields retained by the final signal-B-only wrapper. -/
structure ExpiryFrame (before after : ExpiringAgentState psi kappa tau) : Prop where
  progress : PathProgressView.ofState after.core = PathProgressView.ofState before.core
  path : after.core.erase.core.path = before.core.erase.core.path
  path2 : after.core.erase.core.path2 = before.core.erase.core.path2
  permit : after.core.path0Crossed = before.core.path0Crossed
  state : after.core.erase.core.state = before.core.erase.core.state
  stall : after.stall = before.stall
  active : deletionActive after.core.erase = deletionActive before.core.erase

theorem initialize_right_frame (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau) :
    ExpiryFrame q.2 (initializeFollowerPairBirthSignals l r q).2 := by
  unfold initializeFollowerPairBirthSignals
  split
  · change ExpiryFrame q.2 (clearExpiringLeaderSignal q.2)
    unfold clearExpiringLeaderSignal
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem full_right_expiry_frame (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiryFrame
      (deletionPriorityExpireOne tau (prepareExpiringDisposal hpsi r)
        (basePair hpsi kappa tau l r).2)
      (actionOneFullTransition hpsi kappa tau l r).2 := by
  exact initialize_right_frame (prepareExpiringDisposal hpsi l)
    (prepareExpiringDisposal hpsi r)
    (deletionPriorityExpireOne tau (prepareExpiringDisposal hpsi l)
        (basePair hpsi kappa tau l r).1,
      deletionPriorityExpireOne tau (prepareExpiringDisposal hpsi r)
        (basePair hpsi kappa tau l r).2)

theorem active_due (hpsi : 0 < psi) (u : AuthorizedAgentState psi)
    (ha : deletionActive u = true) : DisposalDue hpsi u := by
  cases hp : u.core.path with
  | bot => simp [deletionActive, pathPresent, hp] at ha
  | some j b =>
      have hs : u.core.state = .eliminate_signal := by
        simpa [deletionActive, pathPresent, hp] using ha
      exact ⟨by simp [hp], Or.inl hs⟩

/-- Any then-current predecessor consumes a due responder in this host. -/
theorem due_right (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (hr : DisposalDue hpsi r.core.erase) :
    (actionOneFullTransition hpsi kappa tau l r).2.core.erase.core.path = .bot ∧
      (actionOneFullTransition hpsi kappa tau l r).2.core.erase.core.state = .none := by
  rw [actionOneFull_eq_disposalFull_of_due hpsi kappa tau l r (Or.inr hr)]
  have hh := due_responder_full hpsi kappa tau l r hr
  exact ⟨hh.1, hh.2.1⟩

theorem due_left (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (hl : DisposalDue hpsi l.core.erase) :
    (actionOneFullTransition hpsi kappa tau l r).1.core.erase.core.path = l.core.erase.core.path ∧
      DisposalDue hpsi (actionOneFullTransition hpsi kappa tau l r).1.core.erase := by
  rw [actionOneFull_eq_disposalFull_of_due hpsi kappa tau l r (Or.inl hl)]
  have hh := due_initiator_full hpsi kappa tau l r hl
  exact ⟨hh.1, by simpa only [hh.1] using hl.1, Or.inl hh.2.1⟩

/-- Active pre-expiry disposal is refreshed, remains physically due after
the final wrapper, and is consumed at the next incoming hit for arbitrary left. -/
theorem priority_output (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (ha : deletionActive (basePair hpsi kappa tau l r).2.core.erase = true) :
    let out := (actionOneFullTransition hpsi kappa tau l r).2
    DisposalDue hpsi out.core.erase ∧ out.stall = freshStall tau ∧
      ∀ a : ExpiringAgentState psi kappa tau,
        (actionOneFullTransition hpsi kappa tau a out).2.core.erase.core.path = .bot ∧
          (actionOneFullTransition hpsi kappa tau a out).2.core.erase.core.state = .none := by
  let out := (actionOneFullTransition hpsi kappa tau l r).2
  have hf := full_right_expiry_frame hpsi kappa tau l r
  have he := deletionPriorityExpireOne_of_active tau (prepareExpiringDisposal hpsi r)
    (basePair hpsi kappa tau l r).2 ha
  rw [he] at hf
  have hd : DisposalDue hpsi out.core.erase := active_due hpsi _ (hf.active.trans ha)
  exact ⟨hd, hf.stall, fun a => due_right hpsi kappa tau a out hd⟩

/-- A changed physical path/permission view is exactly a nonpriority
refresh. This theorem deliberately does not label the change generation loss. -/
theorem progress_refresh (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (ha : deletionActive (basePair hpsi kappa tau l r).2.core.erase = false)
    (hp : PathProgressView.ofState (basePair hpsi kappa tau l r).2.core ≠
      PathProgressView.ofState (prepareExpiringDisposal hpsi r).core) :
    let out := (actionOneFullTransition hpsi kappa tau l r).2
    PathProgressView.ofState out.core = PathProgressView.ofState (basePair hpsi kappa tau l r).2.core ∧
      out.stall = freshStall tau := by
  have hf := full_right_expiry_frame hpsi kappa tau l r
  have he : deletionPriorityExpireOne tau (prepareExpiringDisposal hpsi r)
      (basePair hpsi kappa tau l r).2 =
        ⟨(basePair hpsi kappa tau l r).2.core, freshStall tau⟩ := by
    rw [deletionPriorityExpireOne, if_neg (by simp [ha])]
    exact pathExpireOne_of_progress tau _ _ hp
  rw [he] at hf
  exact ⟨hf.progress, hf.stall⟩

/-- The true unchanged-view branch has only expiry or one exact decrement,
even while state and path2 change. The old timer is physically unchanged by prepare. -/
theorem static_expiry_or_age (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (ha : deletionActive (basePair hpsi kappa tau l r).2.core.erase = false)
    (hp : PathProgressView.ofState (basePair hpsi kappa tau l r).2.core =
      PathProgressView.ofState (prepareExpiringDisposal hpsi r).core) :
    let out := (actionOneFullTransition hpsi kappa tau l r).2
    (r.stall.val = 0 ∧ out.core.erase.core.path = .bot ∧
      out.core.erase.core.path2 = none ∧ out.core.path0Crossed = false) ∨
    (∃ hpos : 0 < r.stall.val,
      PathProgressView.ofState out.core = PathProgressView.ofState (prepareExpiringDisposal hpsi r).core ∧
        out.stall = decStall r.stall hpos) := by
  have hf := full_right_expiry_frame hpsi kappa tau l r
  have he : deletionPriorityExpireOne tau (prepareExpiringDisposal hpsi r)
      (basePair hpsi kappa tau l r).2 =
        pathExpireOne tau (prepareExpiringDisposal hpsi r) (basePair hpsi kappa tau l r).2 := by
    simp only [deletionPriorityExpireOne, ha, Bool.false_eq_true, if_false]
  rw [he] at hf
  by_cases hz : r.stall.val = 0
  · have hh := pathExpireOne_zero_clears tau (prepareExpiringDisposal hpsi r)
      (basePair hpsi kappa tau l r).2 hp hz
    have hpath : (pathExpireOne tau (prepareExpiringDisposal hpsi r)
        (basePair hpsi kappa tau l r).2).core.erase.core.path = .bot := by
      simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase, hh.1]
      rfl
    have hpath2 : (pathExpireOne tau (prepareExpiringDisposal hpsi r)
        (basePair hpsi kappa tau l r).2).core.erase.core.path2 = none := by
      simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase, hh.2.1]
      rfl
    exact Or.inl ⟨hz, hf.path.trans hpath, hf.path2.trans hpath2, hf.permit.trans hh.2.2⟩
  · have hpos : 0 < r.stall.val := Nat.pos_of_ne_zero hz
    have hh := pathExpireOne_succ_of_static tau (prepareExpiringDisposal hpsi r)
      (basePair hpsi kappa tau l r).2 hp hpos
    rw [hh] at hf
    exact Or.inr ⟨hpos, hf.progress.trans hp, hf.stall⟩

private theorem due_step_before_incoming (ring : DirectedRing n) (hpsi : 0 < psi)
    (kappa tau : Nat) (C : Fin n → ExpiringAgentState psi kappa tau) (i e : Fin n)
    (hi : DisposalDue hpsi (C i).core.erase) (he : ring.rightNeighbor e ≠ i) :
    let D := localStep ring (actionOneFullTransition hpsi kappa tau) C e
    (D i).core.erase.core.path = (C i).core.erase.core.path ∧ DisposalDue hpsi (D i).core.erase := by
  by_cases hei : i = e
  · subst e
    have hh := due_left hpsi kappa tau (C i) (C (ring.rightNeighbor i)) hi
    simpa only [localStep, if_true] using hh
  · simp only [localStep, hei, Ne.symm he, if_false]
    exact ⟨True.intro, hi⟩

/-- All intervening edges may change the predecessor arbitrarily. Only
the absence of an incoming edge identifies the pending residence interval. -/
theorem due_stays_until_incoming (ring : DirectedRing n) (hpsi : 0 < psi)
    (kappa tau : Nat) (C : Fin n → ExpiringAgentState psi kappa tau) (i : Fin n)
    (word : DetSchedule n) (hi : DisposalDue hpsi (C i).core.erase)
    (havoid : ∀ e ∈ word, ring.rightNeighbor e ≠ i) :
    let D := runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) C word
    (D i).core.erase.core.path = (C i).core.erase.core.path ∧ DisposalDue hpsi (D i).core.erase := by
  induction word generalizing C with
  | nil => exact ⟨rfl, hi⟩
  | cons e es ih =>
      have hh := due_step_before_incoming ring hpsi kappa tau C i e hi (havoid e (by simp))
      have ht := ih _ hh.2 (fun f hf => havoid f (by simp [hf]))
      exact ⟨ht.1.trans hh.1, ht.2⟩

theorem first_incoming_consumes (ring : DirectedRing n) (hn : 1 < n) (hpsi : 0 < psi)
    (kappa tau : Nat) (C : Fin n → ExpiringAgentState psi kappa tau) (i e : Fin n)
    (word : DetSchedule n) (hi : DisposalDue hpsi (C i).core.erase)
    (havoid : ∀ f ∈ word, ring.rightNeighbor f ≠ i) (hnext : ring.rightNeighbor e = i) :
    let D := runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) C word
    let E := localStep ring (actionOneFullTransition hpsi kappa tau) D e
    (D i).core.erase.core.path = (C i).core.erase.core.path ∧
      (E i).core.erase.core.path = .bot ∧ (E i).core.erase.core.state = .none := by
  let D := runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) C word
  have hd := due_stays_until_incoming ring hpsi kappa tau C i word hi havoid
  have hh := due_right hpsi kappa tau (D e) (D i) hd.2
  have he : i ≠ e := by
    rw [← hnext]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  exact ⟨hd.1, by simpa only [localStep, he, hnext, if_false, if_true] using hh.1,
    by simpa only [localStep, he, hnext, if_false, if_true] using hh.2⟩

end BirthResponderHazard

#print axioms BirthResponderHazard.full_right_expiry_frame
#print axioms BirthResponderHazard.priority_output
#print axioms BirthResponderHazard.progress_refresh
#print axioms BirthResponderHazard.static_expiry_or_age
#print axioms BirthResponderHazard.due_stays_until_incoming
#print axioms BirthResponderHazard.first_incoming_consumes
