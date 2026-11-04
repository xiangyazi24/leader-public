import Leader.Wu.Birth.WaitClockRows
import Leader.Wu.Birth.WaitClockPotential
import Leader.Wu.Birth.GenerationControlRepair
import Leader.Wu.Birth.RulerBarrierWitness
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy

/-!
# Actual generation-host WAIT counterexamples

The finite carrier, transition, and every scheduler prefix are literal.
WAIT-only execution is an observation comparison, never the physical host.
The two certificates concern terminal count, not a first leader or a
stochastic hitting law. Evaluation reuses the existing exact vector cache.
-/

namespace BirthWaitClockAudit

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLAuthorizedComparisonRepair
  PPLLNoCheckBirthOutputLegitimacy BirthGenerationControlRepair

set_option autoImplicit false
set_option Elab.async false

abbrev Local := ExpiringAgentState 3 2 16

theorem ring6 : DirectedRing 6 := ⟨by decide⟩

/-- Canonical neutral finite cells, with WAIT armed and the old timer fresh. -/
def initial (i : Fin 6) : Local :=
  let s := trapFinite (n := 6) (by decide : 0 < 3) 2 16 i
  { s with
    core := { s.core with core := { s.core.core with wait := true } }
    stall := freshStall 16 }

def rawInitial (i : Fin 6) : AgentState 3 := (initial i).core.core.erase

/-- A carry reaches the terminal in the same row as a delayed reset. -/
def acrossReset : DetSchedule 6 := [0,0,0,0,1,5,0,0,0,0,1]

/-- Service the first carry before the second is produced. -/
def drained : DetSchedule 6 := [0,0,0,0,1,0,0,0,0,1]

/-- Both carry productions occur before any internal service. -/
def coalesced : DetSchedule 6 := [0,0,0,0,0,0,0,0,1,1]

/-- A finite index quantifies every prefix of all three physical words. -/
def fixtureWord (j : Fin 3) : DetSchedule 6 :=
  if j = 0 then acrossReset else if j = 1 then drained else coalesced

/-- The complete current generation host on the original finite cells. -/
def host (word : DetSchedule 6) : Fin 6 → Local :=
  runLocalSchedule ring6 (generationFullTransition (by decide) 2 16) initial word

/-- A comparison observation on the identical word and erased initial state. -/
def waitOnly (word : DetSchedule 6) : Fin 6 → AgentState 3 :=
  runLocalSchedule ring6 (waitSaturated (by decide) 2) rawInitial word

/-- All WAIT fields, including the physical label used by the guards. -/
structure ClockView where
  label : Nat
  h : Bool
  carry : Bool
  reset : Bool
  count : Nat
  wait : Bool
  deriving DecidableEq, Repr

def clock {psi : Nat} (u : AgentState psi) : ClockView :=
  ⟨u.label.val, u.h_field, u.carry, u.reset, u.count, u.wait⟩

/-- The non-clock fields other than WRITE's passive departure marker. -/
def Quiet {psi : Nat} (u : AgentState psi) : Prop :=
  u.leader = false ∧ u.probe = false ∧ u.phase = false ∧ u.bit = false ∧
  u.state = .none ∧ u.path = .bot ∧ u.path2 = none ∧ u.path3 = none ∧
  u.path4 = none ∧ u.path5 = none ∧ u.p = false ∧ u.p_carry = false ∧
  u.reset_cmd = false ∧ u.echo = false ∧ u.bullet = 0 ∧ u.signal_B = 0 ∧
  u.shield = false ∧ u.write = .none ∧
  u.last = false ∧ u.last_set = false ∧ u.last_unset = false ∧
  u.b_carry = false ∧ u.gen_ws = false ∧ u.ws_echo = false ∧ u.signal_ws = false

instance {psi : Nat} (u : AgentState psi) : Decidable (Quiet u) := by
  unfold Quiet
  infer_instance

/-- Full neutrality is required at the actual initial state. -/
def Neutral {psi : Nat} (u : AgentState psi) : Prop := Quiet u ∧ u.write_state = .none

instance {psi : Nat} (u : AgentState psi) : Decidable (Neutral u) := by
  unfold Neutral
  infer_instance

/-- The actual host can install WRITE's departure marker without a writer
payload or GEN event. This is the corrected finite-prefix predicate. -/
def Passive {psi : Nat} (u : AgentState psi) : Prop :=
  Quiet u ∧ (u.write_state = .none ∨ u.write_state = .depart)

instance {psi : Nat} (u : AgentState psi) : Decidable (Passive u) := by
  unfold Passive
  infer_instance

/-- This is a two-group finite fixture in the stated advice window. -/
theorem fixture_parameters : 3 ∣ 6 ∧ 2 * 3 ≤ 6 ∧ 3 ≤ 2 + 1 := by decide

/-- The initial neutral fields and every initial WAIT value are explicit. -/
theorem initial_clean : ∀ i : Fin 6,
    Neutral (rawInitial i) ∧
    clock (rawInitial i) = ⟨i.val % 3, false, false, false, 0, true⟩ ∧
    (initial i).core.path0Crossed = false ∧ (initial i).stall.val = 16 := by decide

/-- The existing bounded carrier supplies its actual declared field domains. -/
theorem initial_domain (i : Fin 6) : (rawInitial i).inProtocolDomain 2 :=
  (initial i).core.core.erase_inProtocolDomain

/-- The wrap edge is as correctly labelled as each internal edge. -/
theorem initial_barrier_free : ∀ e : Fin 6,
    ¬ isBarrier (by decide : 0 < 3) (rawInitial e) (rawInitial (ring6.rightNeighbor e)) := by
  unfold isBarrier
  decide

/-- Identical labels and all five clock registers at every full-host prefix
of all three words, including the final and empty prefixes. -/
theorem full_host_wait_projection :
    ∀ j : Fin 3, ∀ t : Fin ((fixtureWord j).length + 1), ∀ i : Fin 6,
      clock ((host ((fixtureWord j).take t.val) i).core.core.erase) =
        clock (waitOnly ((fixtureWord j).take t.val) i) := by
  unfold host waitOnly
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

/-- All examined prefixes stay leaderless and have no comparison or writer
payload; the passive WRITE departure marker is allowed. WAIT stays armed
and every terminal count is below the cap. -/
theorem full_host_cold_prefix :
    ∀ j : Fin 3, ∀ t : Fin ((fixtureWord j).length + 1), ∀ i : Fin 6,
      Passive ((host ((fixtureWord j).take t.val) i).core.core.erase) ∧
      (host ((fixtureWord j).take t.val) i).core.core.wait = true ∧
      (host ((fixtureWord j).take t.val) i).core.core.count.val < 2 ∧
      (host ((fixtureWord j).take t.val) i).core.core.label.val = i.val % 3 ∧
      (host ((fixtureWord j).take t.val) i).core.path0Crossed = false := by
  unfold host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

/-- The stronger claim that every writer field stays neutral already fails
at the first actual edge, even though both actual GEN guards are false. -/
theorem passive_departure_is_actual :
    (initial 1).core.core.write_state = .none ∧
    (host [0] 1).core.core.write_state = .depart ∧
    ¬ Neutral ((host [0] 1).core.core.erase) := by
  unfold host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

/-- Exactly the actual pre-GEN input used by the complete host's no-write
comparison theorem, including prepared disposal and the probe/reset wall. -/
def beforeGen (word : DetSchedule 6) (e : Fin 6) :=
  PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall (by decide : 0 < 3)
    (BirthMismatchDisposalProducer.preparedInput (by decide) (host word e).core.erase)
    (BirthMismatchDisposalProducer.preparedInput (by decide)
      (host word (ring6.rightNeighbor e)).core.erase)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- Both actual payload-writer guards are false at every scheduled row in
all three words; absence of later paths is not used as a substitute. -/
theorem no_generation_writers :
    ∀ j : Fin 3, ∀ t : Fin (fixtureWord j).length,
      let e := (fixtureWord j)[t.val]
      let p := beforeGen ((fixtureWord j).take t.val) e
      generationWrites (by decide : 0 < 3) 2 p.1.core p.2.core = (false, false) := by
  unfold beforeGen host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

/-- Root outgoing/incoming projection of the raw scheduler word. -/
def coins (word : DetSchedule 6) : DetSchedule 6 :=
  word.filter (fun e => e == 0 || e == 5)

def longestOutgoingRun (word : DetSchedule 6) : Nat :=
  ((coins word).foldl (fun (p : Nat × Nat) e =>
    if e = 0 then (p.1 + 1, max p.2 (p.1 + 1)) else (0, p.2)) (0, 0)).2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The terminal count increments despite a simultaneous pending reset,
after eleven actual rows whose root word has longest outgoing run four. -/
theorem hit_crosses_pending_reset :
    acrossReset.length = 11 ∧
    (host (acrossReset.take 10) 1).core.core.carry = true ∧
    (host (acrossReset.take 10) 1).core.core.reset = true ∧
    (host (acrossReset.take 10) 2).core.core.h_field = true ∧
    (host (acrossReset.take 10) 2).core.core.count.val = 0 ∧
    (host acrossReset 2).core.core.count.val = 1 ∧
    (host acrossReset 2).core.core.h_field = false ∧
    coins acrossReset = [0,0,0,0,5,0,0,0,0] ∧
    longestOutgoingRun acrossReset = 4 ∧ longestOutgoingRun acrossReset < 2 ^ 3 := by
  unfold host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- Equal-length actual words with exactly the same eight root outgoing
letters produce distinct terminal counts because carry registers coalesce. -/
theorem root_projection_does_not_determine_count :
    drained.length = 10 ∧ coalesced.length = 10 ∧
    coins drained = coins coalesced ∧ coins drained = List.replicate 8 0 ∧
    (host drained 2).core.core.count.val = 1 ∧
    (host coalesced 2).core.core.count.val = 0 := by
  unfold host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

/-- Even with the raw length fixed at ten, no function of the root word
recovers the actual terminal count on all full-host executions. -/
theorem no_root_word_count_function :
    ¬ ∃ f : DetSchedule 6 → Nat, ∀ word : DetSchedule 6,
      word.length = 10 → (host word 2).core.core.count.val = f (coins word) := by
  rintro ⟨f, hf⟩
  obtain ⟨hd, hc, he, _, hv, hw⟩ := root_projection_does_not_determine_count
  have h1 := hf drained hd
  have h0 := hf coalesced hc
  rw [hv, he] at h1
  rw [hw] at h0
  omega

/-- The passive zero-carry boundary premise of the general row law is
produced on all full-host prefixes of the three concrete words. -/
theorem prefix_boundary_carry_zero :
    ∀ j : Fin 3, ∀ t : Fin ((fixtureWord j).length + 1), ∀ i : Fin 6,
      i.val % 3 = 0 ∨ i.val % 3 = 2 →
        (host ((fixtureWord j).take t.val) i).core.core.carry = false := by
  unfold host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

/-- The proposed physical work potential for the first three-site group;
root and terminal carry registers do not contribute. -/
def groupEnergy (C : Fin 6 → AgentState 3) : Nat :=
  energy 1 0 0 (C 0) + energy 2 4 0 (C 1) + energy 4 0 8 (C 2)

/-- Literal full-host work accounting on every examined prefix. The count
hit is funded by eight total outgoing edges, with no consecutive-run claim. -/
theorem fixture_energy_charge :
    ∀ j : Fin 3, ∀ t : Fin ((fixtureWord j).length + 1),
      groupEnergy (fun i => (host ((fixtureWord j).take t.val) i).core.core.erase) ≤
        ((fixtureWord j).take t.val).count 0 := by
  unfold host
  simp only [← BirthRulerBarrier.cachedRun_correct]
  decide

end BirthWaitClockAudit

#print axioms BirthWaitClockAudit.initial_clean
#print axioms BirthWaitClockAudit.initial_domain
#print axioms BirthWaitClockAudit.full_host_wait_projection
#print axioms BirthWaitClockAudit.full_host_cold_prefix
#print axioms BirthWaitClockAudit.passive_departure_is_actual
#print axioms BirthWaitClockAudit.no_generation_writers
#print axioms BirthWaitClockAudit.hit_crosses_pending_reset
#print axioms BirthWaitClockAudit.root_projection_does_not_determine_count
#print axioms BirthWaitClockAudit.no_root_word_count_function
#print axioms BirthWaitClockAudit.prefix_boundary_carry_zero
#print axioms BirthWaitClockAudit.fixture_energy_charge
