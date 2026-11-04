import Leader.Wu.Birth.ShortDoneTerminalBirthPhysical

/-!
# First metadata birth = first physical positive prefix

This module stays on the original full `ExpiringAgentState` execution.  The
shadow row is used only inside the one-step proof that a false birth cannot
create a leader from a leaderless state; no shadow run or conditioned word is
defined here.
-/

namespace BirthShortDoneTerminalFirstHit

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair K2OutputSafety
open K2BirthDispatcher ExpiringK2Projection LDSinkBoundedKernel

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-- Literal physical count zero. -/
def Leaderless (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  ∀ i, (C i).core.core.leader = false

/-- Every full configuration from the start through the end of this exact
scheduler prefix is leaderless.  The successor is the real terminal consumer
state, not an observed/shadow state. -/
def LeaderlessAlong (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : List (Fin n) → Prop
  | [] => Leaderless C
  | e :: es =>
      Leaderless C ∧
      LeaderlessAlong hψ hwidth hle ring
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es

theorem LeaderlessAlong.head (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hz : LeaderlessAlong hψ hwidth hle ring C es) : Leaderless C := by
  cases es with
  | nil => exact hz
  | cons e es => exact hz.1

theorem LeaderlessAlong.run_leaderless
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) (hz : LeaderlessAlong hψ hwidth hle ring C es) :
    Leaderless (run
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C es) := by
  induction es generalizing C with
  | nil =>
      change Leaderless C at hz
      simpa only [run] using hz
  | cons e es ih =>
      change Leaderless C ∧
        LeaderlessAlong hψ hwidth hle ring
          (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es at hz
      simpa only [run] using
        ih (C := BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) hz.2

private theorem shadowRow_leaderless (l r : AgentState 1)
    (hl : l.leader = false) (hr : r.leader = false) :
    (K2BirthDispatcher.shadowRow l r).1.leader = false ∧
      (K2BirthDispatcher.shadowRow l r).2.leader = false := by
  unfold K2BirthDispatcher.shadowRow
  dsimp only
  have hl' : (signalView l).leader = false := hl
  have hr' : (signalView r).leader = false := hr
  have hnot : ¬ ((signalView l).leader = true ∧
      (signalView r).leader = true) := by
    intro h
    have hbad : false = true := hl'.symm.trans h.1
    cases hbad
  rw [if_neg hnot]
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
    (by decide : 0 < 1) (signalView l) (signalView r)
  exact ⟨hk.1 hl', hk.2 hr'⟩

private theorem shadowStep_leaderless (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (e : Fin n)
    (hC : ∀ i, (C i).leader = false) :
    ∀ i, (K2BirthDispatcher.shadowStep ring C e i).leader = false := by
  intro i
  have hq := shadowRow_leaderless (C e) (C (ring.rightNeighbor e))
    (hC e) (hC (ring.rightNeighbor e))
  simp only [K2BirthDispatcher.shadowStep, updatePair]
  split
  · exact hq.1
  · split
    · exact hq.2
    · exact hC i

/-- A false metadata birth cannot be the first physical positive event.
Starting from literal count zero, the actual complete consumer step remains
literal count zero.  No safety, label, path or timer premise is used. -/
theorem step_leaderless_of_no_birth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (e : Fin n) (hC : Leaderless C)
    (hb : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
      (C e) (C (ring.rightNeighbor e)) = false) :
    Leaderless
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) := by
  have ho := BirthShortDoneTerminalObserver.observe_step_of_no_birth
    hψ hwidth hle ring C e hb
  have hobs : ∀ j, (ExpiringK2Projection.observe C j).leader = false := by
    intro j
    exact hC j
  have hz := shadowStep_leaderless ring (ExpiringK2Projection.observe C) e hobs
  intro i
  have hi := congrArg AgentState.leader (congrFun ho i)
  change
    (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e i).core.core.leader =
      (K2BirthDispatcher.shadowStep ring
        (ExpiringK2Projection.observe C) e i).leader at hi
  exact hi.trans (hz i)

/-- Derived, not assumed: an actual no-birth prefix starting at count zero
ends at count zero. -/
theorem noBirth_run_leaderless
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) (hC : Leaderless C)
    (hn : BirthShortDoneTerminalObserver.NoBirthAlong
      hψ hwidth hle ring C es) :
    Leaderless (run
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C es) := by
  induction es generalizing C with
  | nil => simpa only [run] using hC
  | cons e es ih =>
      change
        BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
            (C e) (C (ring.rightNeighbor e)) = false ∧
          BirthShortDoneTerminalObserver.NoBirthAlong hψ hwidth hle ring
            (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es at hn
      have h1 := step_leaderless_of_no_birth
        hψ hwidth hle ring C e hC hn.1
      simpa only [run] using
        ih (C := BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e)
          h1 hn.2

/-- Every ordinary `List.take` prefix of the same physical word is leaderless
before the first birth. -/
theorem noBirth_all_prefixes_leaderless
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) (hC : Leaderless C)
    (hn : BirthShortDoneTerminalObserver.NoBirthAlong
      hψ hwidth hle ring C es) (t : Nat) :
    Leaderless (run
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring)
      C (es.take t)) :=
  noBirth_run_leaderless hψ hwidth hle ring C (es.take t) hC
    (BirthShortDoneTerminalObserver.NoBirthAlong.take
      hψ hwidth hle ring C es hn t)

/-- Existing `NoBirthAlong` plus an initial count-zero state gives the stronger
full-state statement that every successive physical prefix state is zero. -/
theorem leaderlessAlong_of_noBirthAlong
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) (hC : Leaderless C)
    (hn : BirthShortDoneTerminalObserver.NoBirthAlong
      hψ hwidth hle ring C es) :
    LeaderlessAlong hψ hwidth hle ring C es := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih =>
      change
        BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
            (C e) (C (ring.rightNeighbor e)) = false ∧
          BirthShortDoneTerminalObserver.NoBirthAlong hψ hwidth hle ring
            (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es at hn
      refine ⟨hC, ?_⟩
      exact ih
        (C := BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e)
        (step_leaderless_of_no_birth hψ hwidth hle ring C e hC hn.1) hn.2

/-- Conversely, on a non-singleton ring, if every physical prefix state is
still leaderless then every preceding metadata event was false.  A true one
would contradict the actual distinct-edge survival theorem. -/
theorem noBirthAlong_of_leaderlessAlong
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hz : LeaderlessAlong hψ hwidth hle ring C es) :
    BirthShortDoneTerminalObserver.NoBirthAlong hψ hwidth hle ring C es := by
  induction es generalizing C with
  | nil => trivial
  | cons e es ih =>
      change Leaderless C ∧
        LeaderlessAlong hψ hwidth hle ring
          (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es at hz
      have hnext := LeaderlessAlong.head hψ hwidth hle ring
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es hz.2
      cases hb : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
          (C e) (C (ring.rightNeighbor e)) with
      | false =>
          refine ⟨hb, ?_⟩
          exact ih
            (C := BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) hz.2
      | true =>
          have hp :=
            BirthShortDoneTerminalBirthPhysical.birthEvent_true_step_has_physical_leader_of_one_lt
              hψ hwidth hle ring hn C e hb
          obtain ⟨i, hi⟩ := hp
          have hf := hnext i
          have hbad : false = true := hf.symm.trans hi
          cases hbad

/-- **First-hit equivalence on the original physical word.**
`pre` is the exact already-executed scheduler prefix and `e` is its next edge.
The left side says every physical prefix through `pre` is count zero and the
next actual step is count positive.  The right side says exactly that every
metadata event on `pre` was false and the next actual metadata event is true. -/
theorem first_physical_hit_iff_first_birth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (h0 : Leaderless C)
    (pre : List (Fin n)) (e : Fin n) :
    (LeaderlessAlong hψ hwidth hle ring C pre ∧
      ∃ i : Fin n,
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring
          (run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre)
          e i).core.core.leader = true) ↔
    (BirthShortDoneTerminalObserver.NoBirthAlong hψ hwidth hle ring C pre ∧
      BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
        ((run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre) e)
        ((run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre)
          (ring.rightNeighbor e)) = true) := by
  constructor
  · rintro ⟨hz, hpos⟩
    have hnb := noBirthAlong_of_leaderlessAlong
      hψ hwidth hle ring hn C pre hz
    have hpre := LeaderlessAlong.run_leaderless
      hψ hwidth hle ring C pre hz
    cases hb : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
        ((run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre) e)
        ((run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre)
          (ring.rightNeighbor e)) with
    | true => exact ⟨hnb, rfl⟩
    | false =>
        have hs := step_leaderless_of_no_birth hψ hwidth hle ring
          (run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre)
          e hpre hb
        obtain ⟨i, hi⟩ := hpos
        have hf := hs i
        have hbad : false = true := hf.symm.trans hi
        cases hbad
  · rintro ⟨hnb, hb⟩
    have hz := leaderlessAlong_of_noBirthAlong
      hψ hwidth hle ring C pre h0 hnb
    refine ⟨hz, ?_⟩
    exact
      BirthShortDoneTerminalBirthPhysical.birthEvent_true_step_has_physical_leader_of_one_lt
        hψ hwidth hle ring hn
        (run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C pre)
        e hb

#print axioms BirthShortDoneTerminalFirstHit.step_leaderless_of_no_birth
#print axioms BirthShortDoneTerminalFirstHit.noBirth_all_prefixes_leaderless
#print axioms BirthShortDoneTerminalFirstHit.first_physical_hit_iff_first_birth

end BirthShortDoneTerminalFirstHit
