import Leader.Wu.Birth.FullHostWaitedRulerCounterexample

set_option autoImplicit false

namespace BirthCheckCongestGuardRepair

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  BirthFullHostWaitedRulerCounterexample

variable {psi kappa : Nat}

/-! This separately named candidate changes only the CHECK invocation in the
complete wall-sweep host.  A congested component is waiting for comparison
control and must not be converted directly to CHECK-ready by the old local
rearming assignment.  The existing finite carrier and every other physical
stage are retained.  This is not a global provenance or stabilization theorem.

Requiring CHECK-ready on entry would have no initial producer: the original
CHECK rearming assignment is itself the only writer of that state.  The guard
therefore retains the original neutral-arrival rearming behavior and excludes
only the concretely witnessed congested pair boundary. -/

/-- Suspend CHECK while either endpoint is in the congest control phase. -/
def congestGuardCheck (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  if l.core.state = .congest ∨ r.core.state = .congest then (l, r)
  else authorizedCheckSig hpsi l r

/-- The blocked branch frames every field, in particular both leader bits. -/
theorem congestGuardCheck_of_congest (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (h : l.core.state = .congest ∨ r.core.state = .congest) :
    congestGuardCheck hpsi l r = (l, r) := by
  simp [congestGuardCheck, h]

/-- Outside congestion this is exactly the original physical CHECK. -/
theorem congestGuardCheck_of_clear (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.state ≠ .congest) (hr : r.core.state ≠ .congest) :
    congestGuardCheck hpsi l r = authorizedCheckSig hpsi l r := by
  simp [congestGuardCheck, hl, hr]

/-- The additional Boolean branch introduces no new numeric register. -/
theorem congestGuardCheck_inProtocolDomain
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := congestGuardCheck hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  unfold congestGuardCheck
  split
  · exact ⟨hl, hr⟩
  · exact authorizedReconcile_inProtocolDomain (checkSig hpsi) l r
      (checkSig_inProtocolDomain hpsi l.core r.core hl hr)

/-- The same exact sanitized CHECK input with the congest guard inserted. -/
def guardedAfterCheck (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r
  congestGuardCheck hpsi beforeCheck.1 beforeCheck.2

/-- The complete authorized host, with the CHECK call replaced by the guard.
Deletion priority, normalization, birth marking, and the full suffix are the
existing source stages. -/
def guardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    let afterCheck := guardedAfterCheck hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (wallSweepLeaderSinkAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible]
  wallSweepAuthorizedBeforeCheck wallSweepAuthorizedAfterCheckSuffix
  wallSweepResetProbeAuthorizedBeforeCheck wallSweepLeaderSinkAfterCheckSuffix

/-- The actual sanitized CHECK input contains no congested endpoint.  This
is an executable local branch condition, not a provenance assumption. -/
def CheckInputClear (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop :=
  let q := wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)
  q.1.core.state ≠ .congest ∧ q.2.core.state ≠ .congest

/-- Outside the new CHECK guard the entire authorized transition agrees
exactly with the existing source host, including deletion-priority branches. -/
theorem guardedAuthorizedTransition_eq_original_of_clear
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hclear : CheckInputClear hpsi kappa l r) :
    guardedAuthorizedTransition hpsi kappa l r =
      wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r := by
  dsimp only [CheckInputClear] at hclear
  unfold guardedAuthorizedTransition
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  split
  · rfl
  · split
    · rfl
    · dsimp only [guardedAfterCheck,
        wallSweepResetProbePreCheckResetAfterCheck]
      rw [congestGuardCheck_of_clear hpsi _ _ hclear.1 hclear.2]

/-- Domain closure uses the unchanged prefix and suffix closure theorems. -/
theorem guardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := guardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold guardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let q0 := wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l0 r0
      have h0 := wallSweepResetProbeAuthorizedBeforeCheck_inProtocolDomain
        hpsi kappa l0 r0 hl0 hr0
      let qR := preCheckResetWall q0.1 q0.2
      have hR := preCheckResetWall_inProtocolDomain q0.1 q0.2 h0.1 h0.2
      let q1 := sanitizeAuthorizedPair hpsi qR
      have h1 : q1.1.core.inProtocolDomain kappa ∧
          q1.2.core.inProtocolDomain kappa :=
        ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.1 hR.1,
          sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.2 hR.2⟩
      let q2 := congestGuardCheck hpsi q1.1 q1.2
      have h2 := congestGuardCheck_inProtocolDomain hpsi q1.1 q1.2 h1.1 h1.2
      let born := leaderBirthBeforeOrAtCheck l0 r0 q1 q2
      let tail := wallSweepLeaderSinkAfterCheckSuffix hpsi q2.1 q2.2
      have ht := wallSweepLeaderSinkAfterCheckSuffix_inProtocolDomain
        hpsi q2.1 q2.2 h2.1 h2.2
      exact markLeaderBirth_inProtocolDomain born tail ht

/-- Reification uses the original authorized bounded carrier. -/
def guardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := guardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := guardedAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- The candidate's finite reification is exact. -/
theorem erase_guardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := guardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) =
      guardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  let q := guardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := guardedAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Exact source agreement survives finite reification; domain proofs do
not alter either counted state. -/
theorem guardedBoundedTransition_eq_original_of_clear
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hclear : CheckInputClear hpsi kappa l.erase r.erase) :
    guardedBoundedTransition hpsi kappa l r =
      wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r := by
  unfold guardedBoundedTransition
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
  simp only [guardedAuthorizedTransition_eq_original_of_clear
    hpsi kappa l.erase r.erase hclear]

/-- The original two endpoint expiry policies follow the guarded core. -/
def guardedPathStallTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := guardedBoundedTransition hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne tau l lOut,
    deletionPriorityExpireOne tau r rOut)

/-- The final birth-signal initialization is the existing host wrapper. -/
def guardedFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  initializeFollowerPairBirthSignals l r
    (guardedPathStallTransition hpsi kappa tau l r)

/-- The full finite host differs only when the literal sanitized CHECK
boundary contains congestion.  Expiry and birth-signal initialization agree
pointwise whenever this branch is clear. -/
theorem guardedFullTransition_eq_original_of_clear
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hclear : CheckInputClear hpsi kappa l.core.erase r.core.erase) :
    guardedFullTransition hpsi kappa tau l r =
      wallSweepBirthSignalZeroPathStallTransition hpsi kappa tau l r := by
  unfold guardedFullTransition wallSweepBirthSignalZeroPathStallTransition
    guardedPathStallTransition
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
  rw [guardedBoundedTransition_eq_original_of_clear
    hpsi kappa l.core r.core hclear]

attribute [local irreducible] finalBeforeCheck

/-- At the verified congested mixed-component boundary the guarded CHECK
frames both followers instead of creating the terminal leader. -/
theorem guardedCheck_blocks_witnessed_mixed_components :
    congestGuardCheck (by omega) finalBeforeCheck.1 finalBeforeCheck.2 =
      finalBeforeCheck := by
  exact congestGuardCheck_of_congest (by omega) _ _
    (Or.inl check_accepts_congested_mixed_components.1)

attribute [local semireducible]
  wallSweepAuthorizedBeforeCheck wallSweepAuthorizedAfterCheckSuffix
  wallSweepResetProbeAuthorizedBeforeCheck wallSweepLeaderSinkAfterCheckSuffix
  finalBeforeCheck

/-! ## A complete ordinary WAIT/GEN/movement/CHECK witness

The two components below are born together at sites zero and one.  Their
payloads then move through sites one/two and two/three respectively, so the
last comparison uses one complete physical signal from one actual generation.
The initial state has no path or forged crossing permission. -/

abbrev WitnessLocal := ExpiringAgentState 2 2 16

/-- A leaderless, neutral comparison configuration of equal zero-bit groups. -/
def equalInitial (i : Fin 8) : WitnessLocal :=
  let s := waitedInitial i
  { s with core := { s.core with core :=
    { s.core.core with bit := false, leader := false } } }

theorem equalInitial_clean :
    ∀ i : Fin 8,
      (equalInitial i).core.core.leader = false ∧
      (equalInitial i).core.core.wait = true ∧
      (equalInitial i).core.core.count = 0 ∧
      (equalInitial i).core.core.path = .bot ∧
      (equalInitial i).core.path0Crossed = false ∧
      (equalInitial i).core.core.state = .none := by decide

/-- Eight interactions execute the real kappa-two WAIT counter.  The five
remaining interactions move both components across one group and compare. -/
def equalSchedule : DetSchedule 8 :=
  List.replicate 8 0 ++ [1, 0, 2, 1, 2]

def runGuarded (C : Fin 8 → WitnessLocal) (word : DetSchedule 8) :
    Fin 8 → WitnessLocal :=
  runLocalSchedule BirthFullHostRulerCounterexample.ringEight
    (guardedFullTransition (by omega) 2 16) C word

def equalPrefix (t : Nat) : Fin 8 → WitnessLocal :=
  runGuarded equalInitial (equalSchedule.take t)

private theorem get_ofFn (C : Fin 8 → WitnessLocal) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

/-- Tabulation only shares evaluation of the preceding physical state. -/
private def cachedRun : DetSchedule 8 → Vector WitnessLocal 8 →
    Vector WitnessLocal 8
  | [], C => C
  | e :: rest, C => cachedRun rest (Vector.ofFn
      (localStep BirthFullHostRulerCounterexample.ringEight
        (guardedFullTransition (by omega) 2 16) C.get e))

private theorem cachedRun_correct (C : Fin 8 → WitnessLocal)
    (word : DetSchedule 8) :
    (cachedRun word (Vector.ofFn C)).get = runGuarded C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simpa only [cachedRun, get_ofFn, runGuarded, runLocalSchedule] using
        (ih (localStep BirthFullHostRulerCounterexample.ringEight
          (guardedFullTransition (by omega) 2 16) C e))

/-- The first path appears only when the source terminal counter reaches
kappa; both components are generated together and start without permission. -/
theorem complete_signal_generation :
    (∀ t : Fin 8, ∀ i : Fin 8, (equalPrefix t.val i).core.core.path = .bot) ∧
      (equalPrefix 7 1).core.core.count = 1 ∧
      (equalPrefix 8 1).core.core.count = 2 ∧
      (equalPrefix 8 0).core.core.path = .some 0 0 ∧
      (equalPrefix 8 1).core.core.path = .some 1 0 ∧
      (equalPrefix 8 0).core.core.state = .depart ∧
      (equalPrefix 8 1).core.core.state = .depart ∧
      (equalPrefix 8 0).core.path0Crossed = false ∧
      (equalPrefix 8 1).core.path0Crossed = false := by
  unfold equalPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Both original components reach the next group.  The terminal component
is made ready after neutral arrival; the label-zero component gains its true
permission at the physical terminal-to-zero transfer. -/
theorem complete_signal_movement :
    (equalPrefix 9 2).core.core.path = .some 1 0 ∧
      (equalPrefix 10 1).core.core.path = .some 0 0 ∧
      (equalPrefix 11 3).core.core.path = .some 1 0 ∧
      (equalPrefix 11 3).core.core.state = .CHECK_ready ∧
      (equalPrefix 12 2).core.core.path = .some 0 0 ∧
      (equalPrefix 12 2).core.core.state = .CHECK_ready ∧
      (equalPrefix 12 2).core.path0Crossed = true ∧
      (equalPrefix 12 3).core.core.path = .some 1 0 ∧
      (equalPrefix 12 3).core.core.state = .CHECK_ready := by
  unfold equalPrefix
  simp only [← cachedRun_correct]
  decide

def legitimateBeforeCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  wallSweepResetProbePreCheckResetBeforeCheck (by omega) 2
    (normalizeDeletion (equalPrefix 12 2).core.erase)
    (normalizeDeletion (equalPrefix 12 3).core.erase)

def legitimateAfterCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  congestGuardCheck (by omega) legitimateBeforeCheck.1 legitimateBeforeCheck.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- At the actual last CHECK boundary both arrived components are ready,
the zero component has genuine crossing permission, and equality creates the
terminal leader under the guarded CHECK. -/
theorem complete_signal_check_accepts :
    legitimateBeforeCheck.1.core.state = .CHECK_ready ∧
      legitimateBeforeCheck.2.core.state = .CHECK_ready ∧
      legitimateBeforeCheck.1.path0Crossed = true ∧
      legitimateBeforeCheck.2.path0Crossed = false ∧
      legitimateBeforeCheck.1.core.path = .some 0 0 ∧
      legitimateBeforeCheck.2.core.path = .some 1 0 ∧
      legitimateAfterCheck.1.core.state = .equal ∧
      legitimateAfterCheck.2.core.state = .equal ∧
      legitimateAfterCheck.2.core.leader = true := by
  unfold legitimateAfterCheck legitimateBeforeCheck equalPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The entire guarded physical host, including the real suffix and expiry,
creates exactly one leader from the clean leaderless state in thirteen steps. -/
theorem complete_signal_creates_unique_leader :
    equalSchedule.length = 13 ∧
      (∀ i : Fin 8, (equalPrefix 13 i).core.core.leader = true ↔ i = 2) ∧
      (equalPrefix 13 2).core.core.label = 0 ∧
      (equalPrefix 13 2).core.core.signal_B = 0 := by
  unfold equalPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Along the previously refuting forty-two-edge word, every prefix of this
guarded host retains exactly the original leader at six.  The assertion is
about this word, not arbitrary scheduling or closure of the safe kernel. -/
theorem guarded_waited_word_has_no_second_birth :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runGuarded waitedInitial (waitedSchedule.take t.val) i).core.core.leader =
        true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

end BirthCheckCongestGuardRepair

#print axioms BirthCheckCongestGuardRepair.guardedAuthorizedTransition_inProtocolDomain
#print axioms BirthCheckCongestGuardRepair.erase_guardedBoundedTransition
#print axioms BirthCheckCongestGuardRepair.guardedFullTransition_eq_original_of_clear
#print axioms BirthCheckCongestGuardRepair.guardedCheck_blocks_witnessed_mixed_components
#print axioms BirthCheckCongestGuardRepair.complete_signal_generation
#print axioms BirthCheckCongestGuardRepair.complete_signal_movement
#print axioms BirthCheckCongestGuardRepair.complete_signal_check_accepts
#print axioms BirthCheckCongestGuardRepair.complete_signal_creates_unique_leader
#print axioms BirthCheckCongestGuardRepair.guarded_waited_word_has_no_second_birth
