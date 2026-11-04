import Leader.Wu.Birth.DoneLineageLeaseActiveGuard
import Leader.Wu.Splice.CheckFreezeLifetime
import Leader.Wu.Scheduler.FixedSpanRenewalPayload
import Leader.Wu.Epoch.VoterSumTools
import Leader.Core.UniformBlockRenewal




set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false




namespace B9LeaseLifetime




open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory PPLLWallSweepHistory
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions
open BirthDoneLineageLeaseHostStep
open BirthDoneLineageLeaseActiveReservation
open BirthDoneLineageLeaseActiveGuard
open B9CheckFreezeLifetime
open FiniteUniformStoppingTree




variable {n psi : Nat}




/-- Strong meaning of a pending DONE handoff: the scheduled cut is live and
already carries its valid lease certificate. -/
def PendingDoneHandoff
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  BirthDoneLineageLeaseActiveReservation.CertifiedCommitAt
    hpsi ring S e




/-- Broader writer-level pending token.  The stale-permit fixture below inhabits this predicate but is
not a certified pending DONE handoff. -/
def PendingLeaseToken
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  S.role e = .predecessorPermit




/-- Commit and safe abandon both consume the predecessor-permit role. -/
def LeaseResolved
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  S.role e ≠ .predecessorPermit




/-! ## Local decidability used by the predictive fallback -/




private instance instDecidableLeaseCutInvariantLife
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi)
    (lr rr : LineageRole) :
    Decidable (LeaseCutInvariant hpsi l r lr rr) := by
  unfold LeaseCutInvariant DoneRoleReady RoleLineageSound
  infer_instance




private instance instDecidableLeaseCutAtLife
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (i : Fin n) :
    Decidable (LeaseCutAt hpsi ring S i) := by
  unfold LeaseCutAt
  dsimp only
  infer_instance




private instance instDecidableLeaseSafeLife
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) :
    Decidable (LeaseSafe hpsi ring M role) := by
  unfold LeaseSafe
  dsimp only
  infer_instance




private instance instDecidableActiveClosureLife
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (i : Fin n) :
    Decidable (ActiveIncidentClosureGuard hpsi ring S i) := by
  unfold ActiveIncidentClosureGuard ActiveReverseCutGuard
  infer_instance




/-- On guard failure, abandon the permit endpoint and leave its predecessor
untouched.  This adds no role/state value and cannot unmask a token by deleting
the predecessor blocker. -/
def abandonPendingEndpoint
    (S : LeaseHostConfig n psi) (e : Fin n) : LeaseHostConfig n psi :=
  { marked := fun i =>
      if i = e then markedClearComparisonSignal (S.marked i) else S.marked i
    role := fun i => if i = e then .none else S.role i }




/-- The active predecessor row is admitted only when its own incident cuts are
safe and, if it leaves the tracked permit pending, the already-existing guarded
commit step on that permit is predicted to consume it.  This is a guard only:
there is no new state and no new lease role. -/
def ActiveTwoStepClosureGuard
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (p : Fin n) : Prop :=
  ActiveIncidentClosureGuard hpsi ring S p ∧
    let T := activePredecessorHostStep ring S p
    let e := ring.rightNeighbor p
    T.role e = .predecessorPermit ->
      LeaseResolved
        (BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
          hpsi ring T e) e




private instance instDecidableActiveTwoStepClosureLife
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (p : Fin n) :
    Decidable (ActiveTwoStepClosureGuard hpsi ring S p) := by
  unfold ActiveTwoStepClosureGuard LeaseResolved
  infer_instance




/-- Constant-state predecessor row.  On a failed two-step guard, scrub the
pending endpoint, not the predecessor blocker. -/
def activeOrAbandonPredecessorStep
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (p : Fin n) : LeaseHostConfig n psi :=
  if ActiveTwoStepClosureGuard hpsi ring S p then
    activePredecessorHostStep ring S p
  else
    let e := ring.rightNeighbor p
    if S.role e = .predecessorPermit then abandonPendingEndpoint S e else S




/-- Transaction projection of one raw scheduler letter.  Once this tracked
lease is resolved, later letters are absorbing for this transaction.  The
commit edge keeps the existing guarded host; the predecessor edge uses the
constant-state two-step fallback above. -/
def leaseSchedulerStep
    (hpsi : 0 < psi) (ring : DirectedRing n) (commit : Fin n)
    (S : LeaseHostConfig n psi) (a : Fin n) : LeaseHostConfig n psi :=
  if S.role commit = .predecessorPermit then
    if a = commit then
      BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
        hpsi ring S a
    else if a = ring.leftNeighbor commit then
      activeOrAbandonPredecessorStep hpsi ring S a
    else
      BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
        hpsi ring S a
  else
    S




/-- Exact endpoint after a finite raw scheduler word. -/
def leaseEndpoint
    (hpsi : 0 < psi) (ring : DirectedRing n) (commit : Fin n)
    (S : LeaseHostConfig n psi) (u : List (Fin n)) :
    LeaseHostConfig n psi :=
  u.foldl (leaseSchedulerStep hpsi ring commit) S




/-- Finite-word first-resolution time.  If the lease is still pending after the
whole supplied word, return `u.length + 1`; thus `leaseLife ... u <= u.length`
means that this word really resolved the lease. -/
def leaseLife
    (hpsi : 0 < psi) (ring : DirectedRing n) (commit : Fin n) :
    LeaseHostConfig n psi -> List (Fin n) -> Nat
  | S, [] =>
      if S.role commit = .predecessorPermit then 1 else 0
  | S, a :: u =>
      if S.role commit = .predecessorPermit then
        1 + leaseLife hpsi ring commit
          (leaseSchedulerStep hpsi ring commit S a) u
      else 0




/-- The advertised predecessor/commit block has resolved the tracked lease. -/
def LeaseTwoStepReady
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) : Prop :=
  LeaseResolved
    (leaseEndpoint hpsi ring e S [ring.leftNeighbor e, e]) e




/-- Exact semantic statement requested by the freeze-lifetime repair. -/
def LeaseSafeTwoStepClosureStatement : Prop :=
  forall (n psi : Nat) (hpsi : 0 < psi) (ring : DirectedRing n)
      (S : LeaseHostConfig n psi) (e : Fin n),
    LeaseSafe hpsi ring S.marked S.role ->
    PendingDoneHandoff hpsi ring S e ->
    LeaseTwoStepReady hpsi ring S e




/-! ## Ring geometry and certified-role consequences -/




private theorem rightNeighbor_leftNeighbor_local
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]




private theorem rightNeighbor_ne_self_of_one_lt
    (ring : DirectedRing n) (hn : 1 < n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self] at hv
    omega




private theorem leftNeighbor_ne_self_of_one_lt
    (ring : DirectedRing n) (hn : 1 < n) (i : Fin n) :
    ring.leftNeighbor i ≠ i := by
  intro h
  have hr : ring.rightNeighbor i = i := by
    calc
      ring.rightNeighbor i =
          ring.rightNeighbor (ring.leftNeighbor i) :=
        congrArg ring.rightNeighbor h.symm
      _ = i := rightNeighbor_leftNeighbor_local ring i
  exact (rightNeighbor_ne_self_of_one_lt ring hn i) hr




/-- A certified pending handoff fixes both lease roles on the commit cut. -/
theorem pendingDoneHandoff_roles
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (h : PendingDoneHandoff hpsi ring S e) :
    S.role e = .predecessorPermit ∧
      S.role (ring.rightNeighbor e) = .frontier := by
  unfold PendingDoneHandoff at h
  unfold BirthDoneLineageLeaseActiveReservation.CertifiedCommitAt at h
  dsimp only at h
  rcases h with ⟨hguard, hinv⟩
  unfold LeaseCutInvariant at hinv
  have hready := hinv.1
  unfold DoneRoleReady at hready
  exact hready hguard




/-- Certified pending handoff implies the executable predecessor permit. -/
theorem pendingDoneHandoff_role
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (h : PendingDoneHandoff hpsi ring S e) :
    PendingLeaseToken S e :=
  (pendingDoneHandoff_roles hpsi ring S e h).1




/-- A certified pending handoff cannot live on the one-site self-loop: that
would force its single role to be both predecessorPermit and frontier. -/
theorem pendingDoneHandoff_ring_nontrivial
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (h : PendingDoneHandoff hpsi ring S e) :
    1 < n := by
  have hroles := pendingDoneHandoff_roles hpsi ring S e h
  have hp := hroles.1
  have hf := hroles.2
  refine Classical.byContradiction (fun hn => ?_)
  have hn1 : n = 1 := by have := e.isLt; omega
  subst n
  have heq : ring.rightNeighbor e = e := Subsingleton.elim _ _
  rw [heq, hp] at hf
  cases hf




/-! ## Two-step closure -/




private theorem leaseSchedulerStep_resolved
    (hpsi : 0 < psi) (ring : DirectedRing n) (commit : Fin n)
    (S : LeaseHostConfig n psi) (a : Fin n)
    (h : LeaseResolved S commit) :
    leaseSchedulerStep hpsi ring commit S a = S := by
  unfold LeaseResolved at h
  simp [leaseSchedulerStep, h]




private theorem leaseSchedulerStep_commit_of_pending
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (h : PendingLeaseToken S e) :
    leaseSchedulerStep hpsi ring e S e =
      BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
        hpsi ring S e := by
  unfold PendingLeaseToken at h
  simp [leaseSchedulerStep, h]




private theorem leaseSchedulerStep_predecessor_of_pending
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (h : PendingLeaseToken S e)
    (hne : ring.leftNeighbor e ≠ e) :
    leaseSchedulerStep hpsi ring e S (ring.leftNeighbor e) =
      activeOrAbandonPredecessorStep
        hpsi ring S (ring.leftNeighbor e) := by
  unfold PendingLeaseToken at h
  simp [leaseSchedulerStep, h, hne]




/-- If the permit is pending when the predecessor letter is selected, the
fallback either resolves it immediately or the strengthened guard certifies
that the following guarded commit resolves it. -/
private theorem activeOrAbandon_progress
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (p e : Fin n)
    (hright : ring.rightNeighbor p = e)
    (hpending : S.role e = .predecessorPermit) :
    let R := activeOrAbandonPredecessorStep hpsi ring S p
    LeaseResolved R e ∨
      (R.role e = .predecessorPermit ∧
        LeaseResolved
          (BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
            hpsi ring R e) e) := by
  by_cases hg : ActiveTwoStepClosureGuard hpsi ring S p
  · have hguard := hg
    unfold ActiveTwoStepClosureGuard at hguard
    dsimp only at hguard
    rcases hguard with ⟨_, hfuture⟩
    let T := activePredecessorHostStep ring S p
    have hfuture' :
        T.role e = .predecessorPermit ->
          LeaseResolved
            (BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
              hpsi ring T e) e := by
      simpa [T, hright] using hfuture
    have hstep :
        activeOrAbandonPredecessorStep hpsi ring S p = T := by
      simp [activeOrAbandonPredecessorStep, hg, T]
    rw [hstep]
    by_cases ht : T.role e = .predecessorPermit
    · exact Or.inr ⟨ht, hfuture' ht⟩
    · exact Or.inl ht
  · have hstep :
        activeOrAbandonPredecessorStep hpsi ring S p =
          abandonPendingEndpoint S e := by
      simp [activeOrAbandonPredecessorStep, hg, hright, hpending]
    rw [hstep]
    exact Or.inl (by
      unfold LeaseResolved abandonPendingEndpoint
      simp)




/-- The predecessor/commit word resolves every tracked permit on a nontrivial
ring.  This stronger retry-state form is what the block tail needs. -/
theorem leaseTwoStepReady_of_one_lt
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseTwoStepReady hpsi ring S e := by
  have hpne : ring.leftNeighbor e ≠ e :=
    leftNeighbor_ne_self_of_one_lt ring hn e
  have hright : ring.rightNeighbor (ring.leftNeighbor e) = e :=
    rightNeighbor_leftNeighbor_local ring e
  unfold LeaseTwoStepReady leaseEndpoint
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hp : PendingLeaseToken S e
  · rw [leaseSchedulerStep_predecessor_of_pending
      hpsi ring S e hp hpne]
    let R := activeOrAbandonPredecessorStep
      hpsi ring S (ring.leftNeighbor e)
    change LeaseResolved (leaseSchedulerStep hpsi ring e R e) e
    have hprog :
        LeaseResolved R e ∨
          (R.role e = .predecessorPermit ∧
            LeaseResolved
              (BirthDoneLineageLeaseActiveReservation.guardedLeaseHostStep
                hpsi ring R e) e) := by
      simpa [R] using
        (activeOrAbandon_progress hpsi ring S
          (ring.leftNeighbor e) e hright
          (by simpa [PendingLeaseToken] using hp))
    rcases hprog with hdone | ⟨hpR, hcommit⟩
    · rw [leaseSchedulerStep_resolved hpsi ring e R e hdone]
      exact hdone
    · have hpendingR : PendingLeaseToken R e := hpR
      rw [leaseSchedulerStep_commit_of_pending
        hpsi ring R e hpendingR]
      exact hcommit
  · have hres : LeaseResolved S e := by
      unfold PendingLeaseToken at hp
      exact hp
    rw [leaseSchedulerStep_resolved
      hpsi ring e S (ring.leftNeighbor e) hres]
    rw [leaseSchedulerStep_resolved hpsi ring e S e hres]
    exact hres




/-- Requested two-step closure.  `LeaseSafe` is retained in the public contract;
the predictive fallback gives the stronger retry-state resolution theorem above. -/
theorem leaseSafeTwoStepClosure :
    LeaseSafeTwoStepClosureStatement := by
  unfold LeaseSafeTwoStepClosureStatement
  intro n psi hpsi ring S e _hsafe hpending
  have hn : 1 < n :=
    pendingDoneHandoff_ring_nontrivial
      (n := n) (psi := psi) hpsi ring S e hpending
  exact leaseTwoStepReady_of_one_lt
    (n := n) (psi := psi) hpsi ring hn S e




/-! ## The finite prescribed word, not a deterministic scheduler-time bound -/




/-- On the prescribed predecessor/commit word, semantic resolution gives the
literal two-interaction bound.  This is a word-local fact only. -/
theorem leaseLife_pair_le_two
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (hpending : PendingLeaseToken S e)
    (hready : LeaseTwoStepReady hpsi ring S e) :
    LeaseLifetimeBound
      (leaseLife hpsi ring e S [ring.leftNeighbor e, e]) 2 := by
  let p := ring.leftNeighbor e
  let R := leaseSchedulerStep hpsi ring e S p
  let C := leaseSchedulerStep hpsi ring e R e
  have hp : S.role e = .predecessorPermit := hpending
  have hfinal : C.role e ≠ .predecessorPermit := by
    change C.role e ≠ .predecessorPermit at hready
    exact hready
  unfold LeaseLifetimeBound
  change
    (if S.role e = .predecessorPermit then
      1 + leaseLife hpsi ring e R [e] else 0) <= 2
  rw [if_pos hp]
  by_cases hR : R.role e = .predecessorPermit
  · change
      1 + (if R.role e = .predecessorPermit then
        1 + leaseLife hpsi ring e C [] else 0) <= 2
    rw [if_pos hR]
    change 1 + (1 +
      (if C.role e = .predecessorPermit then 1 else 0)) <= 2
    rw [if_neg hfinal]
    omega
  · change
      1 + (if R.role e = .predecessorPermit then
        1 + leaseLife hpsi ring e C [] else 0) <= 2
    rw [if_neg hR]
    omega




/-- Every nontrivial-ring retry state has the same two-letter word-local bound. -/
theorem leaseLife_pair_le_two_of_one_lt
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    LeaseLifetimeBound
      (leaseLife hpsi ring e S [ring.leftNeighbor e, e]) 2 := by
  by_cases hp : PendingLeaseToken S e
  · exact leaseLife_pair_le_two hpsi ring S e hp
      (leaseTwoStepReady_of_one_lt hpsi ring hn S e)
  · unfold LeaseLifetimeBound
    unfold PendingLeaseToken at hp
    simp [leaseLife, hp]




/-- Certified/safe specialization requested by the closure statement. -/
theorem leaseLife_pair_le_two_of_safe_pending
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (hsafe : LeaseSafe hpsi ring S.marked S.role)
    (hpending : PendingDoneHandoff hpsi ring S e) :
    LeaseLifetimeBound
      (leaseLife hpsi ring e S [ring.leftNeighbor e, e]) 2 := by
  have hrole := pendingDoneHandoff_role hpsi ring S e hpending
  have hready :=
    leaseSafeTwoStepClosure n psi hpsi ring S e hsafe hpending
  exact leaseLife_pair_le_two hpsi ring S e hrole hready




/-- Compatibility with the old arithmetic seam for one prescribed resolving
word only; this is not a pointwise raw-scheduler hitting-time theorem. -/
theorem leaseLife_pair_fits_existing_T
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) (T : Nat)
    (hpending : PendingLeaseToken S e)
    (hready : LeaseTwoStepReady hpsi ring S e)
    (hT : 2 <= T) :
    LeaseLifetimeBound
      (leaseLife hpsi ring e S [ring.leftNeighbor e, e]) T := by
  unfold LeaseLifetimeBound
  exact Nat.le_trans
    (leaseLife_pair_le_two hpsi ring S e hpending hready) hT




/-! ## Raw two-letter word mass -/




private theorem ofFn_zero_sum (m : Nat) :
    (List.ofFn (fun _ : Fin m => 0)).sum = 0 := by
  simpa using PPLLEpochVoterSumTools.sum_ofFn_const m 0




private theorem ofFn_indicator_sum_one
    {m : Nat} (a : Fin m) :
    (List.ofFn (fun i : Fin m => if i = a then 1 else 0)).sum = 1 := by
  have h := PPLLEpochVoterSumTools.sum_ofFn_balance_one
    (fun i : Fin m => if i = a then 1 else 0)
    (fun _ : Fin m => 0) a (by
      intro i hia
      simp [hia])
  have hz := ofFn_zero_sum m
  rw [hz] at h
  simpa using h




private theorem wordSum_zero
    {m : Nat} (f : List (Fin m) -> Nat) :
    FixedSpanRenewalPayload.wordSum m 0 f = f [] := by
  rfl




/-- Indicator of one literal two-letter scheduler word. -/
def leasePairWordWeight
    (p e : Fin n) (u : List (Fin n)) : Nat :=
  if u = [p, e] then 1 else 0




/-- Exactly one of the `n^2` raw words is `[p,e]`. -/
theorem leasePairWord_mass_one
    (p e : Fin n) :
    FixedSpanRenewalPayload.wordSum n 2
      (leasePairWordWeight p e) = 1 := by
  rw [show (2 : Nat) = 1 + 1 by rfl,
    FixedSpanRenewalPayload.wordSum_succ]
  calc
    _ = (List.ofFn (fun a : Fin n => if a = p then 1 else 0)).sum := by
      apply PPLLEpochVoterSumTools.sum_ofFn_eq
      intro a
      rw [show (1 : Nat) = 0 + 1 by rfl,
        FixedSpanRenewalPayload.wordSum_succ]
      by_cases ha : a = p
      · subst a
        rw [if_pos rfl]
        calc
          _ = (List.ofFn (fun b : Fin n =>
              if b = e then 1 else 0)).sum := by
            apply PPLLEpochVoterSumTools.sum_ofFn_eq
            intro b
            rw [wordSum_zero]
            simp [leasePairWordWeight]
          _ = 1 := ofFn_indicator_sum_one e
      · rw [if_neg ha]
        calc
          _ = (List.ofFn (fun _ : Fin n => 0)).sum := by
            apply PPLLEpochVoterSumTools.sum_ofFn_eq
            intro b
            rw [wordSum_zero]
            simp [leasePairWordWeight, ha]
          _ = 0 := ofFn_zero_sum n
    _ = 1 := ofFn_indicator_sum_one p




private theorem wordSum_mono
    {m T : Nat} (f g : List (Fin m) -> Nat)
    (h : forall u, u.length = T -> f u <= g u) :
    FixedSpanRenewalPayload.wordSum m T f <=
      FixedSpanRenewalPayload.wordSum m T g := by
  induction T generalizing f g with
  | zero =>
      have hz := h [] rfl
      simpa [FixedSpanRenewalPayload.wordSum, allSchedules] using hz
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ,
        FixedSpanRenewalPayload.wordSum_succ]
      apply PPLLEpochVoterSumTools.sum_ofFn_le
      intro a
      apply ih
      intro u hu
      apply h (a :: u)
      simp [hu]




/-- Success bit for one raw scheduler word. -/
def leaseResolutionWeight
    (hpsi : 0 < psi) (ring : DirectedRing n) (e : Fin n)
    (S : LeaseHostConfig n psi) (u : List (Fin n)) : Nat :=
  if leaseLife hpsi ring e S u <= u.length then 1 else 0




/-- Exact finite-horizon success numerator. -/
def leaseResolutionMass
    (hpsi : 0 < psi) (ring : DirectedRing n) (e : Fin n)
    (S : LeaseHostConfig n psi) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (leaseResolutionWeight hpsi ring e S)




/-- The prescribed two-letter word contributes one unit to the raw success
numerator from every retry state on a nontrivial ring. -/
theorem leaseResolutionMass_pos_of_one_lt
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    1 <= leaseResolutionMass hpsi ring e S 2 := by
  have hlife := leaseLife_pair_le_two_of_one_lt hpsi ring hn S e
  unfold LeaseLifetimeBound at hlife
  let p := ring.leftNeighbor e
  have hlife' :
      leaseLife hpsi ring e S [p, e] <= 2 := by
    simpa [p] using hlife
  have hm := wordSum_mono (m := n) (T := 2)
    (leasePairWordWeight p e)
    (leaseResolutionWeight hpsi ring e S) (by
      intro u _hu
      by_cases hw : u = [p, e]
      · subst u
        simp [leasePairWordWeight, leaseResolutionWeight, hlife']
      · simp [leasePairWordWeight, hw])
  unfold leaseResolutionMass
  rw [← leasePairWord_mass_one p e]
  exact hm




/-- Compatibility name; closure now supplies the semantic input. -/
theorem leaseResolutionMass_pos_of_twoStepReady
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (hpending : PendingDoneHandoff hpsi ring S e)
    (_hready : LeaseTwoStepReady hpsi ring S e) :
    1 <= leaseResolutionMass hpsi ring e S 2 := by
  have hn := pendingDoneHandoff_ring_nontrivial hpsi ring S e hpending
  exact leaseResolutionMass_pos_of_one_lt hpsi ring hn S e




/-- Project HMass arithmetic with raw physical block length `L = 2` and
`Q = n^2`. -/
theorem leaseResolutionBlockMass_of_one_lt
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    n ^ 2 <= n ^ 2 * leaseResolutionMass hpsi ring e S 2 := by
  have hm := leaseResolutionMass_pos_of_one_lt hpsi ring hn S e
  have h := Nat.mul_le_mul_left (n ^ 2) hm
  simpa using h




/-- Old conditional interface, now discharged by the proved closure. -/
theorem leaseResolutionBlockMass_of_twoStepReady
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (_hsafe : LeaseSafe hpsi ring S.marked S.role)
    (hpending : PendingDoneHandoff hpsi ring S e)
    (_hready : LeaseTwoStepReady hpsi ring S e) :
    n ^ 2 <= n ^ 2 * leaseResolutionMass hpsi ring e S 2 := by
  have hn := pendingDoneHandoff_ring_nontrivial hpsi ring S e hpending
  exact leaseResolutionBlockMass_of_one_lt hpsi ring hn S e




/-- The exact project word-sum block hypothesis: one resolving raw word out of
`n^2`, written without probability division. -/
theorem leaseResolutionHMass_of_safe_pending
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (_hsafe : LeaseSafe hpsi ring S.marked S.role)
    (hpending : PendingDoneHandoff hpsi ring S e) :
    n ^ 2 <= n ^ 2 *
      FixedSpanRenewalPayload.wordSum n 2
        (leaseResolutionWeight hpsi ring e S) := by
  have hn := pendingDoneHandoff_ring_nontrivial hpsi ring S e hpending
  simpa [leaseResolutionMass] using
    (leaseResolutionBlockMass_of_one_lt hpsi ring hn S e)




/-! ## Fixed-span macro block and geometric tail -/




/-- One macro scheduler symbol is one original raw word of length two.  Success
means that the word resolves the tracked lease; retry retains its actual raw
endpoint. -/
def leaseBlockStep
    (hpsi : 0 < psi) (ring : DirectedRing n) (e : Fin n)
    (S : LeaseHostConfig n psi) (i : Fin (n ^ 2)) :
    StopNode (LeaseHostConfig n psi) :=
  let u := FixedSpanRenewalPayload.rawWord n 2 i
  if leaseLife hpsi ring e S u <= u.length then
    .success
  else
    .active (leaseEndpoint hpsi ring e S u)




private theorem leaseBlockStep_ne_failure
    (hpsi : 0 < psi) (ring : DirectedRing n) (e : Fin n) :
    forall (S : LeaseHostConfig n psi) (i : Fin (n ^ 2)),
      leaseBlockStep hpsi ring e S i ≠ .failure := by
  intro S i
  unfold leaseBlockStep
  dsimp only
  split <;> simp




/-- The macro one-step success count is exactly the original raw `wordSum n 2`
numerator; `rawWord` changes only indexing, not multiplicity. -/
theorem leaseBlock_successCount_one_eq_mass
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    successCount (leaseBlockStep hpsi ring e) (.active S) 1 =
      leaseResolutionMass hpsi ring e S 2 := by
  unfold leaseResolutionMass
  rw [← FixedSpanRenewalPayload.rawWord_sum n 2
    (leaseResolutionWeight hpsi ring e S)]
  change
    (List.ofFn (fun i : Fin (n ^ 2) =>
      successWeight (leaseBlockStep hpsi ring e S i))).sum =
    (List.ofFn (fun i : Fin (n ^ 2) =>
      leaseResolutionWeight hpsi ring e S
        (FixedSpanRenewalPayload.rawWord n 2 i))).sum
  apply PPLLEpochVoterSumTools.sum_ofFn_eq
  intro i
  unfold leaseBlockStep leaseResolutionWeight
  dsimp only
  split <;> rfl




private theorem leaseBlock_success_mass_of_one_lt
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (S : LeaseHostConfig n psi) (e : Fin n) :
    n ^ 2 <= n ^ 2 *
      successCount (leaseBlockStep hpsi ring e) (.active S) 1 := by
  rw [leaseBlock_successCount_one_eq_mass]
  exact leaseResolutionBlockMass_of_one_lt hpsi ring hn S e




/-- Geometric retry tail over `k` raw two-letter blocks.  The macro alphabet
has size `n^2`; translating back gives denominator `n^(2*k)`. -/
theorem leaseResolution_geometric_tail_of_one_lt
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (S : LeaseHostConfig n psi) (e : Fin n) (k : Nat) :
    (n ^ 2) ^ k *
        activeCount
          (UniformBlockRenewal.retry (leaseBlockStep hpsi ring e))
          (.active S) k <=
      (n ^ 2 - 1) ^ k * n ^ (2 * k) := by
  have hQ : 0 < n ^ 2 := Nat.pow_pos ring.hn
  have hblock : forall X : LeaseHostConfig n psi,
      (n ^ 2) ^ (1 * 1) <=
        (n ^ 2) *
          successCount (leaseBlockStep hpsi ring e) (.active X) (1 * 1) := by
    intro X
    simpa using leaseBlock_success_mass_of_one_lt hpsi ring hn X e
  have ht := UniformBlockRenewal.block_tail
    (step := leaseBlockStep hpsi ring e)
    (K := 1) (q := 1) (q' := n ^ 2)
    hQ (leaseBlockStep_ne_failure hpsi ring e) hblock S k
  have ht' :
      (n ^ 2) ^ k *
          activeCount
            (UniformBlockRenewal.retry (leaseBlockStep hpsi ring e))
            (.active S) k <=
        (n ^ 2 - 1) ^ k * (n ^ 2) ^ k := by
    simpa [Nat.mul_one, Nat.one_mul] using ht
  calc
    (n ^ 2) ^ k *
          activeCount
            (UniformBlockRenewal.retry (leaseBlockStep hpsi ring e))
            (.active S) k <=
        (n ^ 2 - 1) ^ k * (n ^ 2) ^ k := ht'
    _ = (n ^ 2 - 1) ^ k * n ^ (2 * k) := by
      rw [Nat.pow_mul]




/-- Certified/safe public tail.  This is the mass-form replacement for the
false deterministic raw-scheduler `LeaseLifetimeBound` interpretation. -/
theorem leaseResolution_geometric_tail_of_safe_pending
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (S : LeaseHostConfig n psi) (e : Fin n)
    (_hsafe : LeaseSafe hpsi ring S.marked S.role)
    (hpending : PendingDoneHandoff hpsi ring S e) (k : Nat) :
    (n ^ 2) ^ k *
        activeCount
          (UniformBlockRenewal.retry (leaseBlockStep hpsi ring e))
          (.active S) k <=
      (n ^ 2 - 1) ^ k * n ^ (2 * k) := by
  have hn := pendingDoneHandoff_ring_nontrivial hpsi ring S e hpending
  exact leaseResolution_geometric_tail_of_one_lt
    hpsi ring hn S e k




/-! ## Fixture: stale permit guard stall and constant-state fallback -/




private theorem hTwo : 0 < 2 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def a0 : Fin 2 := 0
private def a1 : Fin 2 := 1




private def base2 (label : Fin 2) (state : MainState) : AgentState 2 :=
  { leader := false, probe := false, phase := false, bit := false, wait := true,
    state := state, path := .bot, reset := false, carry := false, count := 0,
    label := label, h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := true, write_state := .none, write := .none, last := false,
    last_set := false, last_unset := false, b_carry := false, gen_ws := false,
    ws_echo := false, signal_ws := false }




private def emptyHistory2 : LocalComparisonHistory 2 :=
  { state := .absent, path := .absent,
    path2 := .absent, pCarry := .absent }




private def badMarked (i : Fin 2) : MarkedAgentState 2 2 :=
  if i = a0 then
    ⟨{ base2 1 .none with path2 := some ⟨0, 0, 0, 3⟩ }, emptyHistory2⟩
  else
    ⟨{ base2 0 .CHECK_ready with path2 := some ⟨0, 0, 0, 5⟩ },
      emptyHistory2⟩




private def badRole (i : Fin 2) : LineageRole :=
  if i = a1 then .predecessorPermit else .none




private def badBefore : LeaseHostConfig 2 2 :=
  { marked := badMarked, role := badRole }




private def badFixed : LeaseHostConfig 2 2 :=
  activeOrAbandonPredecessorStep hTwo ring2 badBefore a0




/-- Smallest guard stall.  The conjuncts are deliberately discharged
separately so Lean never needs a Decidable instance for the entire nested
conjunction. -/
theorem q11791_guard_stall :
    LeaseSafe hTwo ring2 badBefore.marked badBefore.role ∧
      PendingLeaseToken badBefore a1 ∧
      ¬ ActiveIncidentClosureGuard hTwo ring2 badBefore a0 ∧
      (guardedActivePredecessorHostStep hTwo ring2 badBefore a0).marked a0 =
        badBefore.marked a0 ∧
      (guardedActivePredecessorHostStep hTwo ring2 badBefore a0).marked a1 =
        badBefore.marked a1 ∧
      (guardedActivePredecessorHostStep hTwo ring2 badBefore a0).role a0 =
        badBefore.role a0 ∧
      (guardedActivePredecessorHostStep hTwo ring2 badBefore a0).role a1 =
        badBefore.role a1 := by
  have hsafe : LeaseSafe hTwo ring2 badBefore.marked badBefore.role := by
    unfold LeaseSafe LeaseCutInvariant DoneRoleReady RoleLineageSound
    dsimp only
    decide
  have hpending : PendingLeaseToken badBefore a1 := by
    unfold PendingLeaseToken
    decide
  have hguard :
      ¬ ActiveIncidentClosureGuard hTwo ring2 badBefore a0 := by
    unfold ActiveIncidentClosureGuard ActiveReverseCutGuard
    unfold LeaseCutAt LeaseCutInvariant DoneRoleReady RoleLineageSound
    dsimp only
    decide
  have hframe :
      guardedActivePredecessorHostStep hTwo ring2 badBefore a0 =
        badBefore := by
    simp [guardedActivePredecessorHostStep, hguard]
  refine ⟨hsafe, hpending, hguard, ?_⟩
  rw [hframe]
  exact ⟨rfl, rfl, rfl, rfl⟩




/-- The no-new-state fallback resolves the literal guard stall while keeping
the action-3 predecessor blocker untouched; the fixture remains LeaseSafe. -/
theorem q11791_constant_state_abandon :
    LeaseSafe hTwo ring2 badFixed.marked badFixed.role ∧
      badFixed.role a1 = .none ∧
      (badFixed.marked a1).concrete.path2 = none ∧
      badFixed.marked a0 = badBefore.marked a0 := by
  have hold :
      ¬ ActiveIncidentClosureGuard hTwo ring2 badBefore a0 := by
    unfold ActiveIncidentClosureGuard ActiveReverseCutGuard
    unfold LeaseCutAt LeaseCutInvariant DoneRoleReady RoleLineageSound
    dsimp only
    decide
  have hnew :
      ¬ ActiveTwoStepClosureGuard hTwo ring2 badBefore a0 := by
    intro h
    unfold ActiveTwoStepClosureGuard at h
    exact hold h.1
  have hright : ring2.rightNeighbor a0 = a1 := by decide
  have hrole : badBefore.role a1 = .predecessorPermit := by decide
  have hfixed :
      badFixed = abandonPendingEndpoint badBefore a1 := by
    unfold badFixed activeOrAbandonPredecessorStep
    rw [if_neg hnew]
    dsimp only
    rw [hright, if_pos hrole]
  rw [hfixed]
  constructor
  · unfold LeaseSafe LeaseCutInvariant DoneRoleReady RoleLineageSound
    dsimp only
    decide
  constructor
  · unfold abandonPendingEndpoint
    dsimp only
    decide
  constructor
  · unfold abandonPendingEndpoint
    dsimp only
    unfold PPLLWallSweepHistory.markedClearComparisonSignal
      PPLLWallSweepRepair.clearComparisonSignal
    decide
  · unfold abandonPendingEndpoint
    dsimp only
    decide




end B9LeaseLifetime




#print axioms B9LeaseLifetime.pendingDoneHandoff_roles
#print axioms B9LeaseLifetime.pendingDoneHandoff_ring_nontrivial
#print axioms B9LeaseLifetime.leaseSafeTwoStepClosure
#print axioms B9LeaseLifetime.leaseLife_pair_le_two
#print axioms B9LeaseLifetime.leaseResolutionHMass_of_safe_pending
#print axioms B9LeaseLifetime.leaseBlock_successCount_one_eq_mass
#print axioms B9LeaseLifetime.leaseResolution_geometric_tail_of_safe_pending
#print axioms B9LeaseLifetime.q11791_guard_stall
#print axioms B9LeaseLifetime.q11791_constant_state_abandon
