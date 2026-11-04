import Leader.Wu.Birth.RulerBarrier
import Leader.Wu.Birth.ArrivalCaptureRepair

/-!
# The inspected-prefix barrier at named complete host boundaries

The producers below consume the actual prepared pre-CHECK computation of
`actionOneFullTransition`. The prefix certificate supplies past inspections;
none of the fields asserting the new mismatch, action four, or Due are inputs.
The arrival host is used only for its already proved identical Due branches.
-/

set_option autoImplicit false

namespace BirthRulerBarrier

open PPLL PPLLWriteSeqRulerBridge PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
  BirthCheckCongestGuardRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthArrivalCaptureRepair

variable {n psi kappa tau : Nat}

attribute [local irreducible] actualCheckInput actualCheckOutput preparedInput
  actionOneFullTransition arrivalFullTransition actionOneAfterCheckSuffix

/-- The exact first-bit assignment in the complete action-one host's CHECK
call, evaluated on its prepared and sanitized physical input. -/
def actualLeftInspection (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AgentState psi :=
  checkSigCheckL hpsi (checkSigSetReady (actualCheckInput hpsi kappa l r).1.core)

/-- The exact successor-bit assignment in that same physical CHECK call. -/
def actualRightInspection (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AgentState psi :=
  checkSigCheckR hpsi (actualLeftInspection hpsi kappa l r)
    (checkSigSetReady (actualCheckInput hpsi kappa l r).2.core)

private theorem ready_fixed (u : AgentState psi) (hs : u.state = .CHECK_ready) :
    checkSigSetReady u = u := by
  have hu : { u with state := MainState.CHECK_ready } = u := by
    cases u
    cases hs
    rfl
  unfold checkSigSetReady
  split
  · split
    · exact hu
    · rfl
  · rfl

/-- The recorded successor result is literally the complete CHECK's right
input to result/leader assignment, whenever the current congestion guard allows
that CHECK call. This statement does not skip the actual host prefix. -/
theorem actual_right_inspection_cut (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : (actualCheckInput hpsi kappa l r).1.core.state ≠ .congest)
    (hr : (actualCheckInput hpsi kappa l r).2.core.state ≠ .congest) :
    (actualCheckOutput hpsi kappa l r).2.core =
      checkSigSetLeader hpsi (checkSigSetResult (actualRightInspection hpsi kappa l r)) := by
  unfold actualCheckOutput
  rw [congestGuardCheck_of_clear hpsi _ _ hl hr]
  rfl

theorem actual_left_inspection_cut (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : (actualCheckInput hpsi kappa l r).1.core.state ≠ .congest)
    (hr : (actualCheckInput hpsi kappa l r).2.core.state ≠ .congest) :
    (actualCheckOutput hpsi kappa l r).1.core =
      checkSigSetResult (actualLeftInspection hpsi kappa l r) := by
  unfold actualCheckOutput
  rw [congestGuardCheck_of_clear hpsi _ _ hl hr]
  rfl

/-- Direct no-new-CHECK-leader consumer on a physically larger group. Its
complete prefix record is the exact present inspection computed by this named
host, and its word values are the physical `groupID`s of the ruler snapshot. -/
theorem actual_larger_group_check_no_birth
    (hpsi : psi > 0) (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (sourceStart targetStart : Fin n)
    (hlt : groupID ring.hn C sourceStart < groupID ring.hn C targetStart)
    (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hrecord : InspectedPrefix hpsi
      (fun k => (C (groupOffset ring sourceStart k)).bit)
      (fun k => (C (groupOffset ring targetStart k)).bit)
      (psi - 1) (actualRightInspection hpsi kappa l r))
    (hl : (actualCheckInput hpsi kappa l r).1.core.state ≠ .congest)
    (hr : (actualCheckInput hpsi kappa l r).2.core.state ≠ .congest) :
    (actualCheckOutput hpsi kappa l r).2.core.leader =
      (actualCheckInput hpsi kappa l r).2.core.leader := by
  have hv := hlt
  rw [groupID_eq_msbBitValue ring C sourceStart,
    groupID_eq_msbBitValue ring C targetStart] at hv
  have h := larger_group_inspection_no_birth hpsi _ _ hrecord hv
  rw [actual_right_inspection_cut hpsi kappa l r hl hr, h.2]
  have hf : ∀ u : AgentState psi, (checkSigSetResult u).leader = u.leader := by
    intro u
    cases hs : u.state <;> simp [checkSigSetResult, hs]
  rw [hf]
  unfold actualRightInspection checkSigCheckR checkSigSetReady
  repeat (first | rfl | split)

/-- A current aligned ready component at label zero supplies the first
inspection record by executing CHECK, without asserting an equal state. -/
theorem record_actual_first (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (source target : Nat → Bool)
    (hl : (actualCheckInput hpsi kappa l r).1.core.label.val = 0)
    (hp : (actualCheckInput hpsi kappa l r).1.core.path = .some 0 (boolBitValue (source 0)))
    (hs : (actualCheckInput hpsi kappa l r).1.core.state = .CHECK_ready)
    (hb : (actualCheckInput hpsi kappa l r).1.core.bit = target 0) :
    InspectedPrefix hpsi source target 0 (actualLeftInspection hpsi kappa l r) := by
  rw [actualLeftInspection, ready_fixed _ hs]
  exact InspectedPrefix.first _ hl hp hs hb

/-- The label-zero first-mismatch case also produces action four in the
actual CHECK call. Subsequent forward command transport is a separate full-host
obligation; this theorem does not silently turn this left output into Due. -/
theorem actual_zero_larger_command (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : (actualCheckInput hpsi kappa l r).1.core.label.val = 0)
    (hp : (actualCheckInput hpsi kappa l r).1.core.path = .some 0 0)
    (hs : (actualCheckInput hpsi kappa l r).1.core.state = .CHECK_ready)
    (hb : (actualCheckInput hpsi kappa l r).1.core.bit = true)
    (hr : (actualCheckInput hpsi kappa l r).2.core.state ≠ .congest) :
    (actualCheckOutput hpsi kappa l r).1.core.state = .larger ∧
      (actualCheckOutput hpsi kappa l r).1.core.path2 = some ⟨0, 0, 0, 4⟩ := by
  have hrec := record_actual_first hpsi kappa l r (fun _ => false) (fun _ => true)
    hl hp hs hb
  have h := inspected_first_larger hpsi (fun _ => false) (fun _ => true) hrec
    (by intro i hi; omega) rfl rfl
  have hc : (actualCheckInput hpsi kappa l r).1.core.state ≠ .congest := by
    rw [hs]
    decide
  rw [actual_left_inspection_cut hpsi kappa l r hc hr]
  exact ⟨by simp [checkSigSetResult, h.1], h.2⟩

/-- Extend a previously inspected physical prefix using this call's actual
aligned ready responder. Prefix retention is explicit in `prior`; the new
equality/inequality result is computed by the real row. -/
theorem record_actual_next (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (source target : Nat → Bool) (j : Nat)
    (prior : InspectedPrefix hpsi source target j (actualLeftInspection hpsi kappa l r))
    (hl : (actualCheckInput hpsi kappa l r).2.core.label.val = j + 1)
    (hp : (actualCheckInput hpsi kappa l r).2.core.path =
      .some (j + 1) (boolBitValue (source (j + 1))))
    (hs : (actualCheckInput hpsi kappa l r).2.core.state = .CHECK_ready)
    (hb : (actualCheckInput hpsi kappa l r).2.core.bit = target (j + 1)) :
    InspectedPrefix hpsi source target (j + 1) (actualRightInspection hpsi kappa l r) := by
  rw [actualRightInspection, ready_fixed _ hs]
  exact InspectedPrefix.next prior _ hl hp hs hb

/-- General first-larger-bit producer at the real action-one CHECK boundary.
All prefix equality, left-label bounds, payload-zero and resident-one fields
required by the previously checked physical producer are derived internally. -/
theorem actual_inspected_larger_full_or_lost
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (source target : Nat → Bool) (j : Nat)
    (hprefix : InspectedPrefix hpsi source target j
      (actualLeftInspection hpsi kappa l.core.erase r.core.erase))
    (hbits : ∀ a, a ≤ j → source a = target a)
    (hsource : source (j + 1) = false) (htarget : target (j + 1) = true)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hlclear : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.state ≠ .congest)
    (hrlabel : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.val = j + 1)
    (hrpath : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path =
      .some (j + 1) (boolBitValue (source (j + 1))))
    (hrstate : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.state = .CHECK_ready)
    (hrbit : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.bit = target (j + 1))
    (hlleader : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hlreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false) :
    let q := actionOneFullTransition hpsi kappa tau l r
    (q.2.core.erase.core.path = .some (j + 1) 0 ∧
      q.2.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.2.core.erase.core.label.val = j + 1) ∨ q.2.core.erase.core.path = .bot := by
  have he := (inspected_equal_iff hpsi source target hprefix).mpr hbits
  have hlabel := inspected_label hpsi source target hprefix
  have hanchor : (actualLeftInspection hpsi kappa l.core.erase r.core.erase).label =
      (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.label := by
    unfold actualLeftInspection checkSigCheckL checkSigSetReady
    repeat (first | rfl | split)
  rw [hanchor] at hlabel
  have hbound : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.label.val < psi - 1 := by
    have := (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.isLt
    omega
  have hp : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path =
      .some (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.val 0 := by
    simpa [hrlabel, hsource, boolBitValue] using hrpath
  have hb : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.bit = true :=
    hrbit.trans htarget
  have h := actual_ready_larger_full_or_lost hpsi kappa tau l r hlinactive hrinactive
    hlclear he hbound hrstate hp hb hlleader hlreset hrreset
  rcases h with h | h
  · exact Or.inl ⟨h.1.trans (by simpa [hsource, boolBitValue] using hrpath), h.2.1,
      (congrArg Fin.val h.2.2).trans hrlabel⟩
  · exact Or.inr h

/-- A terminal first mismatch in an inspected cohort enters actual Due.
The same current-row assumptions as above remain visible; positive timer is
needed only to retain the component through that interaction's expiry. -/
theorem actual_inspected_terminal_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (source target : Nat → Bool) (j : Nat) (hj : j + 1 = psi - 1)
    (hprefix : InspectedPrefix hpsi source target j
      (actualLeftInspection hpsi kappa l.core.erase r.core.erase))
    (hbits : ∀ a, a ≤ j → source a = target a)
    (hsource : source (j + 1) = false) (htarget : target (j + 1) = true)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hlclear : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.state ≠ .congest)
    (hrlabel : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.val = j + 1)
    (hrpath : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path =
      .some (j + 1) (boolBitValue (source (j + 1))))
    (hrstate : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.state = .CHECK_ready)
    (hrbit : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.bit = target (j + 1))
    (hlleader : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hlreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false)
    (hpositive : 0 < r.stall.val) :
    DisposalDue hpsi (actionOneFullTransition hpsi kappa tau l r).2.core.erase := by
  have he := (inspected_equal_iff hpsi source target hprefix).mpr hbits
  have hlabel := inspected_label hpsi source target hprefix
  have hanchor : (actualLeftInspection hpsi kappa l.core.erase r.core.erase).label =
      (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.label := by
    unfold actualLeftInspection checkSigCheckL checkSigSetReady
    repeat (first | rfl | split)
  rw [hanchor] at hlabel
  have hbound : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.label.val < psi - 1 := by
    omega
  have hp : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path =
      .some (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.val 0 := by
    simpa [hrlabel, hsource, boolBitValue] using hrpath
  have hb : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.bit = true :=
    hrbit.trans htarget
  have hterminal : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label =
      ⟨psi - 1, by omega⟩ := Fin.ext (hrlabel.trans hj)
  exact actual_ready_terminal_larger_produces_disposal hpsi kappa tau l r hlinactive hrinactive
    hlclear he hbound hrstate hp hb hlleader hlreset hrreset hterminal hpositive

/-- Due consumes the actual action-one outgoing branch, for any neighbor and
any timer. The cohort cannot use that interaction to escape to the right. -/
theorem actionOne_due_pinned (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (hl : DisposalDue hpsi l.core.erase) :
    let q := actionOneFullTransition hpsi kappa tau l r
    q.1.core.erase.core.path = l.core.erase.core.path ∧
      q.1.core.erase.core.state = .eliminate_signal ∧
      (q.2.core.erase.core.path = r.core.erase.core.path ∨ q.2.core.erase.core.path = .bot) := by
  rw [actionOneFull_eq_disposalFull_of_due hpsi kappa tau l r (Or.inl hl)]
  have h := due_initiator_full hpsi kappa tau l r hl
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The published arrival host shares the same exact outgoing Due branch. -/
theorem arrival_due_pinned (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (hl : DisposalDue hpsi l.core.erase) :
    let q := arrivalFullTransition hpsi kappa tau l r
    q.1.core.erase.core.path = l.core.erase.core.path ∧
      q.1.core.erase.core.state = .eliminate_signal ∧
      (q.2.core.erase.core.path = r.core.erase.core.path ∨ q.2.core.erase.core.path = .bot) := by
  rw [arrivalFull_eq_actionOneFull_of_due hpsi kappa tau l r (Or.inl hl)]
  exact actionOne_due_pinned hpsi kappa tau l r hl

/-- Actual incoming service deletes the Due component and propagates its
deletion to a present nonterminal predecessor. No schedule promise is needed. -/
theorem actionOne_due_deleted (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (hr : DisposalDue hpsi r.core.erase) :
    let q := actionOneFullTransition hpsi kappa tau l r
    q.2.core.erase.core.path = .bot ∧ q.2.core.erase.core.state = .none ∧
      (l.core.erase.core.path ≠ .bot →
        l.core.erase.core.label ≠ ⟨psi - 1, by omega⟩ →
        q.1.core.erase.core.path = l.core.erase.core.path ∧
          q.1.core.erase.core.state = .eliminate_signal) := by
  rw [actionOneFull_eq_disposalFull_of_due hpsi kappa tau l r (Or.inr hr)]
  have h := due_responder_full hpsi kappa tau l r hr
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

theorem arrival_due_deleted (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (hr : DisposalDue hpsi r.core.erase) :
    let q := arrivalFullTransition hpsi kappa tau l r
    q.2.core.erase.core.path = .bot ∧ q.2.core.erase.core.state = .none ∧
      (l.core.erase.core.path ≠ .bot →
        l.core.erase.core.label ≠ ⟨psi - 1, by omega⟩ →
        q.1.core.erase.core.path = l.core.erase.core.path ∧
          q.1.core.erase.core.state = .eliminate_signal) := by
  rw [arrivalFull_eq_actionOneFull_of_due hpsi kappa tau l r (Or.inr hr)]
  exact actionOne_due_deleted hpsi kappa tau l r hr

end BirthRulerBarrier
