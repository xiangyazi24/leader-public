import Leader.Wu.Birth.ResponderHazardFull

/-! A deterministic bound on consecutive incoming services with arbitrary
then-current predecessor states. No scheduler probability or global generation
extinction is built into the observer. -/

set_option autoImplicit false

namespace BirthResponderHazardResidence

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthResponderHazard BirthResponderHazardFull

variable {psi kappa tau : Nat}

theorem prepare_progress_eq (hpsi : 0 < psi) (r : ExpiringAgentState psi kappa tau)
    (ha : r.core.path0Crossed = false) :
    PathProgressView.ofState (prepareExpiringDisposal hpsi r).core =
      PathProgressView.ofState r.core := by
  have he : (prepareExpiringDisposal hpsi r).core.erase = prepareDisposal hpsi r.core.erase :=
    erase_prepareBoundedDisposal hpsi r.core
  apply view_eq_of_erase_path_permit
  · exact (congrArg (fun u => u.core.path) he).trans (prepareDisposal_path hpsi r.core.erase)
  · exact (congrArg AuthorizedAgentState.path0Crossed he).trans
      ((prepare_false_permit hpsi r.core.erase ha).trans ha.symm)

/-- A surviving, nonpriority, non-event incoming interaction really spends
one unit of the original finite timer. All predecessor fields are arbitrary. -/
theorem incoming_step (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (j bit : Nat)
    (hp : r.core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : r.core.path0Crossed = false) :
    let out := (actionOneFullTransition hpsi kappa tau l r).2
    HostEvent hpsi kappa l.core.erase r.core.erase ∨
    out.core.erase.core.path = .bot ∨ DisposalDue hpsi out.core.erase ∨
    (out.core.erase.core.path = .some j bit ∧ out.core.path0Crossed = false ∧
      out.stall.val + 1 = r.stall.val) := by
  rcases responder_trichotomy hpsi kappa tau l r j bit hp hj ha with he | hd | hage
  · rcases he with he | hz
    · exact Or.inl he
    · exact Or.inr (Or.inl hz.2.1)
  · exact Or.inr (Or.inr (Or.inl hd.1))
  · obtain ⟨hpos, hv, ht⟩ := hage
    have hv' := hv.trans (prepare_progress_eq hpsi r ha)
    have hb := congrArg PathProgressView.path hv'
    have hab := congrArg PathProgressView.path0Crossed hv'
    change (actionOneFullTransition hpsi kappa tau l r).2.core.core.path = r.core.core.path at hb
    have herase : (actionOneFullTransition hpsi kappa tau l r).2.core.erase.core.path = r.core.erase.core.path := by
      simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase, hb]
    have hcount := congrArg Fin.val ht
    change (actionOneFullTransition hpsi kappa tau l r).2.stall.val = r.stall.val - 1 at hcount
    exact Or.inr (Or.inr (Or.inr ⟨herase.trans hp, hab.trans ha, by omega⟩))

/-- Each list entry is the actual predecessor state at that service. The
list may change arbitrarily; the right endpoint is always the previous output. -/
def incomingRun (hpsi : 0 < psi) (kappa tau : Nat) :
    ExpiringAgentState psi kappa tau → List (ExpiringAgentState psi kappa tau) →
      ExpiringAgentState psi kappa tau
  | r, [] => r
  | r, l :: ls => incomingRun hpsi kappa tau
      (actionOneFullTransition hpsi kappa tau l r).2 ls

/-- Sticky observation along that same actual sequence of responder calls.
The event alternative only uses the literal stage audit; the other alternative
is a physically absent path at an interaction boundary. -/
def ResidenceBreak (hpsi : 0 < psi) (kappa tau : Nat) :
    ExpiringAgentState psi kappa tau → List (ExpiringAgentState psi kappa tau) → Prop
  | r, [] => r.core.erase.core.path = .bot
  | r, l :: ls => r.core.erase.core.path = .bot ∨
      HostEvent hpsi kappa l.core.erase r.core.erase ∨
      ResidenceBreak hpsi kappa tau (actionOneFullTransition hpsi kappa tau l r).2 ls

theorem break_of_empty (hpsi : 0 < psi) (kappa tau : Nat)
    (r : ExpiringAgentState psi kappa tau) (ls : List (ExpiringAgentState psi kappa tau))
    (hp : r.core.erase.core.path = .bot) : ResidenceBreak hpsi kappa tau r ls := by
  cases ls
  · exact hp
  · exact Or.inl hp

/-- At most `old.stall + 2` incoming services force a concrete stage event
or an actual empty path. The extra service consumes the deletion-priority
branch even when that branch refreshes the timer. -/
theorem incoming_services_force_break (hpsi : 0 < psi) (kappa tau : Nat)
    (r : ExpiringAgentState psi kappa tau) (ls : List (ExpiringAgentState psi kappa tau))
    (j bit : Nat) (hp : r.core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : r.core.path0Crossed = false) (hlen : r.stall.val + 2 ≤ ls.length) :
    ResidenceBreak hpsi kappa tau r ls := by
  induction ls generalizing r with
  | nil => simp at hlen
  | cons l ls ih =>
      let out := (actionOneFullTransition hpsi kappa tau l r).2
      rcases incoming_step hpsi kappa tau l r j bit hp hj ha with he | hc | hd | hage
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (break_of_empty hpsi kappa tau out ls hc))
      · cases ls with
        | nil => simp at hlen
        | cons l' ls' =>
            have hc := (due_right hpsi kappa tau l' out hd).1
            exact Or.inr (Or.inr (Or.inr (Or.inr
              (break_of_empty hpsi kappa tau _ ls' hc))))
      · have hlen' : out.stall.val + 2 ≤ ls.length := by
          have ht : out.stall.val + 1 = r.stall.val := hage.2.2
          simp only [List.length_cons] at hlen
          omega
        exact Or.inr (Or.inr (ih out hage.1 hage.2.1 hlen'))

/-- Uniformity in the finite timer cap, still without a probabilistic field. -/
theorem tau_add_two_services (hpsi : 0 < psi) (kappa tau : Nat)
    (r : ExpiringAgentState psi kappa tau) (ls : List (ExpiringAgentState psi kappa tau))
    (j bit : Nat) (hp : r.core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : r.core.path0Crossed = false) (hlen : tau + 2 ≤ ls.length) :
    ResidenceBreak hpsi kappa tau r ls := by
  apply incoming_services_force_break hpsi kappa tau r ls j bit hp hj ha
  have ht := r.stall.isLt
  omega

end BirthResponderHazardResidence

#print axioms BirthResponderHazardResidence.incoming_step
#print axioms BirthResponderHazardResidence.incoming_services_force_break
#print axioms BirthResponderHazardResidence.tau_add_two_services
