import Leader.Wu.Birth.ResponderHazard
import Leader.Wu.Birth.ResponderHazardTrace

/-!
# Actual full-host responder trichotomy

This leaf targets `actionOneFullTransition`. A residence-ending stage event
means an actual GEN assignment or an actual intermediate empty path. It does
not assert that every copy descended from a common generation has vanished.
-/

set_option autoImplicit false

namespace BirthResponderHazardFull

open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer
  BirthResponderHazard BirthResponderHazardTrace

variable {psi kappa tau : Nat}

/-- The priority responder branch itself is a real ELIMINATE. Otherwise,
only the executed ordinary branch contributes its concrete stage events. -/
def HostEvent (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop :=
  let l0 := preparedInput hpsi l
  let r0 := preparedInput hpsi r
  deletionActive r0 = true ∨
    (deletionActive r0 = false ∧ deletionActive l0 = false ∧
      StageEvent (ordinaryTrace hpsi kappa l0 r0))

instance hostEventDecidable (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Decidable (HostEvent hpsi kappa l r) := by
  unfold HostEvent
  infer_instance

theorem prepare_false_permit (hpsi : 0 < psi) (r : AuthorizedAgentState psi)
    (hp : r.path0Crossed = false) : (prepareDisposal hpsi r).path0Crossed = false := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split
    · exact hp
    · rfl
  · exact hp

theorem prepared_present (hpsi : 0 < psi) (r : AuthorizedAgentState psi)
    (hp : r.core.path ≠ .bot) : preparedInput hpsi r = prepareDisposal hpsi r := by
  exact normalizeDeletion_eq_of_path_present _ (by simpa only [prepareDisposal_path] using hp)

/-- The early priority guard has a literal empty-path output in the bounded
base. This is stronger than a changed observer value. -/
theorem right_priority_base_clear (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (preparedInput hpsi r) = true) :
    (actionOneDisposalAuthorizedTransition hpsi kappa l r).2.core.path = .bot := by
  have hs : (preparedInput hpsi r).core.state = .eliminate_signal := by
    cases hp : (preparedInput hpsi r).core.path with
    | bot => simp [deletionActive, pathPresent, hp] at hr
    | some j b => simpa [deletionActive, pathPresent, hp] using hr
  unfold actionOneDisposalAuthorizedTransition actionOneGuardedAuthorizedTransition
  change ((if deletionActive (preparedInput hpsi r) then _ else _) : APair psi).2.core.path = .bot
  simp only [hr, if_true]
  change (eliminateSig hpsi (preparedInput hpsi l).core (preparedInput hpsi r).core).2.path = .bot
  simp [eliminateSig, hs]

attribute [local irreducible] PPLLWallSweepPreCheckResetRepair.wallSweepResetProbePreCheckResetBeforeCheck
  actionOneAfterCheckSuffix ordinaryTrace prepareDisposal

/-- With no real stage event, the actual authorized host retains a nonzero
right payload and false movement permission for every current left state. -/
theorem no_host_event_nonzero (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (j bit : Nat)
    (hp : r.core.path = .some j bit) (hj : j ≠ 0) (ha : r.path0Crossed = false)
    (he : ¬ HostEvent hpsi kappa l r) :
    (actionOneDisposalAuthorizedTransition hpsi kappa l r).2.core.path = r.core.path ∧
      (actionOneDisposalAuthorizedTransition hpsi kappa l r).2.path0Crossed = false := by
  let l0 := preparedInput hpsi l
  let r0 := preparedInput hpsi r
  have hr : deletionActive r0 = false := by
    cases hh : deletionActive r0
    · rfl
    · exact (he (Or.inl hh)).elim
  have hpr : r0.core.path = r.core.path := by
    rw [show r0 = prepareDisposal hpsi r from prepared_present hpsi r (by simp [hp])]
    exact prepareDisposal_path hpsi r
  have har : r0.path0Crossed = false := by
    rw [show r0 = prepareDisposal hpsi r from prepared_present hpsi r (by simp [hp])]
    exact prepare_false_permit hpsi r ha
  unfold actionOneDisposalAuthorizedTransition actionOneGuardedAuthorizedTransition
  change ((if deletionActive r0 then _ else if deletionActive l0 then _ else _) : APair psi).2.core.path = r.core.path ∧
    ((if deletionActive r0 then _ else if deletionActive l0 then _ else _) : APair psi).2.path0Crossed = false
  simp only [hr, Bool.false_eq_true, if_false]
  cases hl : deletionActive l0
  · simp only [Bool.false_eq_true, if_false]
    have hs : ¬ StageEvent (ordinaryTrace hpsi kappa l0 r0) :=
      fun hs => he (Or.inr ⟨hr, hl, hs⟩)
    have hout := no_stage_event_nonzero hpsi kappa l0 r0 j bit (hpr.trans hp) hj hs
    rw [ordinary_output_eq] at hout
    exact ⟨hout.1.trans hp.symm, hout.2⟩
  · simp only [if_true]
    exact ⟨hpr, har⟩

/-- Reification is exact at the same pre-expiry physical pair. -/
theorem base_erase_eq (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    (basePair hpsi kappa tau l r).2.core.erase =
      (actionOneDisposalAuthorizedTransition hpsi kappa l.core.erase r.core.erase).2 :=
  congrArg Prod.snd (erase_actionOne_disposal_base hpsi kappa l.core r.core)

/-- Path-only injectivity of bounded erasure; no other state field is assumed
unchanged merely to establish the timer projection. -/
theorem bounded_path_eq_of_erase (s t : AuthorizedBoundedAgentState psi kappa)
    (hp : s.erase.core.path = t.erase.core.path) : s.core.path = t.core.path := by
  cases hs : s.core.path with
  | bot =>
      cases ht : t.core.path with
      | bot => rfl
      | some j b =>
          have hh : PathInfo.bot = .some j.val b.val := by
            simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase, hs, ht] at hp
            exact hp
          cases hh
  | some i a =>
      cases ht : t.core.path with
      | bot =>
          have hh : PathInfo.some i.val a.val = .bot := by
            simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase, hs, ht] at hp
            exact hp
          cases hh
      | some j b =>
          have hh : PathInfo.some i.val a.val = .some j.val b.val := by
            simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase, hs, ht] at hp
            exact hp
          have hij : i = j := Fin.ext (PathInfo.some.inj hh).1
          have hab : a = b := Fin.ext (PathInfo.some.inj hh).2
          cases hij
          cases hab
          rfl

theorem view_eq_of_erase_path_permit (s t : AuthorizedBoundedAgentState psi kappa)
    (hp : s.erase.core.path = t.erase.core.path) (ha : s.path0Crossed = t.path0Crossed) :
    PathProgressView.ofState s = PathProgressView.ofState t := by
  have hb := bounded_path_eq_of_erase s t hp
  simp only [PathProgressView.ofState, hb, ha]

/-- No final-view fallback is used: path and permission equality follow from
actual stage effects, including the otherwise dangerous GEN/clear-refill rows. -/
theorem no_host_event_static (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (j bit : Nat)
    (hp : r.core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : r.core.path0Crossed = false)
    (he : ¬ HostEvent hpsi kappa l.core.erase r.core.erase) :
    PathProgressView.ofState (basePair hpsi kappa tau l r).2.core =
      PathProgressView.ofState (prepareExpiringDisposal hpsi r).core := by
  have hout := no_host_event_nonzero hpsi kappa l.core.erase r.core.erase j bit hp hj ha he
  have hb := base_erase_eq hpsi kappa tau l r
  have hprep : (prepareExpiringDisposal hpsi r).core.erase = prepareDisposal hpsi r.core.erase :=
    erase_prepareBoundedDisposal hpsi r.core
  apply view_eq_of_erase_path_permit
  · exact (congrArg (fun u => u.core.path) hb).trans
      (hout.1.trans ((congrArg (fun u => u.core.path) hprep).trans
        (prepareDisposal_path hpsi r.core.erase)).symm)
  · have hr := prepare_false_permit hpsi r.core.erase ha
    exact (congrArg AuthorizedAgentState.path0Crossed hb).trans
      (hout.2.trans ((congrArg AuthorizedAgentState.path0Crossed hprep).trans hr).symm)

/-- Exhaustive physical alternatives at one incoming hit, with an arbitrary
current predecessor. Birth is not silently excluded or treated as loss. -/
theorem responder_trichotomy (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (j bit : Nat)
    (hp : r.core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : r.core.path0Crossed = false) :
    let out := (actionOneFullTransition hpsi kappa tau l r).2
    (HostEvent hpsi kappa l.core.erase r.core.erase ∨
      (r.stall.val = 0 ∧ out.core.erase.core.path = .bot ∧
        out.core.erase.core.path2 = none ∧ out.core.path0Crossed = false)) ∨
    (DisposalDue hpsi out.core.erase ∧ out.stall = freshStall tau ∧
      ∀ a : ExpiringAgentState psi kappa tau,
        (actionOneFullTransition hpsi kappa tau a out).2.core.erase.core.path = .bot ∧
        (actionOneFullTransition hpsi kappa tau a out).2.core.erase.core.state = .none) ∨
    (∃ hpos : 0 < r.stall.val,
      PathProgressView.ofState out.core = PathProgressView.ofState (prepareExpiringDisposal hpsi r).core ∧
      out.stall = decStall r.stall hpos) := by
  by_cases he : HostEvent hpsi kappa l.core.erase r.core.erase
  · exact Or.inl (Or.inl he)
  · have hs := no_host_event_static hpsi kappa tau l r j bit hp hj ha he
    cases hb : deletionActive (basePair hpsi kappa tau l r).2.core.erase
    · rcases static_expiry_or_age hpsi kappa tau l r hb hs with hz | hage
      · exact Or.inl (Or.inr hz)
      · exact Or.inr (Or.inr hage)
    · exact Or.inr (Or.inl (priority_output hpsi kappa tau l r hb))

end BirthResponderHazardFull

#print axioms BirthResponderHazardFull.right_priority_base_clear
#print axioms BirthResponderHazardFull.no_host_event_nonzero
#print axioms BirthResponderHazardFull.base_erase_eq
#print axioms BirthResponderHazardFull.no_host_event_static
#print axioms BirthResponderHazardFull.responder_trichotomy
