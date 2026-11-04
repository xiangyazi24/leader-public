import Leader.Wu.Birth.ShortDoneTerminalEntranceDrain
import Leader.Wu.Birth.ShortDoneTerminalPassiveFirstCapClosed
import Leader.Wu.Birth.ClockSourceFromPassiveCyclic

namespace Q11632RightDrainCollar

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3Rotation
open BirthShortDoneTerminalB1EntranceR2

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FullConfig (n psi kappa tau : Nat) :=
  Fin n -> ExpiringAgentState psi kappa tau

/-- The smallest static one-successor collar worth testing:
    the outside cell is already passive and cyclically aligned, the exact
    prepared/normalized ordinary gate is open, and the outgoing width-two row
    is strictly pre-cap.  The counterexample below shows that even this is not
    a sanitation producer. -/
def RightDrainCollar
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau)
    (tail : Fin n) : Prop :=
  let out := ring.rightNeighbor tail
  Passive (raw (C out)) ∧
    (raw (C out)).label =
      ⟨((raw (C tail)).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∧
    PreparedOrdinaryOpen hpsi (C tail) (C out) ∧
    RowPreCap2 hpsi h2 kappa ring C tail

/-- Exactly the three ruler equations needed by the local clock source. -/
def TripleLabels
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (a : Fin n) : Prop :=
  (raw (C a)).label.val = 0 ∧
    (raw (C (ring.rightNeighbor a))).label.val = 1 ∧
    (raw (C (ring.rightNeighbor (ring.rightNeighbor a)))).label.val =
      2 % psi

/-- Purely local sanitation: no global HostPassive or HostCyclic premise. -/
def ThreeSiteSanitized
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (a : Fin n) : Prop :=
  Passive (raw (C a)) ∧
    Passive (raw (C (ring.rightNeighbor a))) ∧
    Passive (raw (C (ring.rightNeighbor (ring.rightNeighbor a)))) ∧
    TripleLabels hpsi ring C a

def HasLeader (C : FullConfig n psi kappa tau) : Prop :=
  ∃ i, (C i).core.core.leader = true

def SanitationSuccess
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (a : Fin n) : Prop :=
  HasLeader C ∨ ThreeSiteSanitized hpsi ring C a

/-- `Passive` forces the reset command to its canonical cell value. -/
theorem passive_resetCmd_false {u : AgentState psi}
    (h : Passive u) : u.reset_cmd = false := by
  have hm := h.1
  unfold Metadata at hm
  have hf := congrArg (fun v : AgentState psi => v.reset_cmd) hm
  simpa [BirthWaitPassive.cell] using hf

/-- `Passive` likewise forces the echo bit to false. -/
theorem passive_echo_false {u : AgentState psi}
    (h : Passive u) : u.echo = false := by
  have hm := h.1
  unfold Metadata at hm
  have hf := congrArg (fun v : AgentState psi => v.echo) hm
  simpa [BirthWaitPassive.cell] using hf

/-! ## Finite actual-current-consumer counterexample -/

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hFour : 4 <= 4 := by decide

def ringFour : DirectedRing 4 := ⟨by decide⟩

abbrev E := ExpiringAgentState 2 2 0
abbrev FC4 := Fin 4 -> E

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  omega

private def d0 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def d1 : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

/-- Labels 0,1,0,1.  The tail site 2 alone carries reset_cmd=true. -/
private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell d0
  else if i = 1 then cell d1
  else if i = 2 then { cell d0 with reset_cmd := true }
  else cell d1

private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, d0, d1, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private def source : FC4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩

/-- The smallest egress schedule: execute the tail's outgoing edge 2 -> 3. -/
def rightDrainWord : List (Fin 4) := [(2 : Fin 4)]

/-- Literal exact current width-two consumer execution. -/
def afterRightDrain : FC4 :=
  BirthShortDoneTerminalB1EntranceR2.currentRun
    hTwo hTwoLe ringFour source rightDrainWord

private theorem source_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless source := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide

private theorem source_labels :
    TripleLabels hTwo ringFour source 0 := by
  unfold TripleLabels
  decide

private theorem source_collar :
    RightDrainCollar hTwo hTwoLe ringFour source 2 := by
  unfold RightDrainCollar
  dsimp only
  unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata
    BirthWaitPassive.InertWriter
    BirthShortDoneTerminalB1EntranceR2.PreparedOrdinaryOpen
    BirthShortDoneTerminalPassiveR4.RowPreCap2
    BirthShortDoneTerminalPassiveR4.RowCap2
  dsimp only
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem after_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless afterRightDrain := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem after_labels :
    TripleLabels hTwo ringFour afterRightDrain 0 := by
  unfold TripleLabels
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- The reset front leaves a non-passive echo behind at the protected tail. -/
private theorem after_tail_echo :
    (raw (afterRightDrain 2)).echo = true := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- The same row exports the reset command to the quiet outside successor. -/
private theorem after_outside_reset :
    (raw (afterRightDrain 3)).reset_cmd = true := by
  decide

private theorem after_tail_not_passive :
    ¬ Passive (raw (afterRightDrain 2)) := by
  intro hp
  have hf := passive_echo_false hp
  have hbad : true = false := after_tail_echo.symm.trans hf
  cases hbad

/-- Concrete refutation of the static one-successor collar.  The source is
    leaderless and has labels 0,1,0 on the protected triple.  Its outside
    successor is passive/aligned, the exact ordinary gate is open and pre-cap,
    yet the single permitted tail-outgoing current-consumer row neither creates
    a leader nor sanitizes the triple.  The ruler labels are still 0,1,0. -/
theorem one_successor_right_drain_counterexample :
    RightDrainCollar hTwo hTwoLe ringFour source 2 ∧
      BirthShortDoneTerminalFirstHit.Leaderless source ∧
      TripleLabels hTwo ringFour source 0 ∧
      BirthShortDoneTerminalFirstHit.Leaderless afterRightDrain ∧
      TripleLabels hTwo ringFour afterRightDrain 0 ∧
      (raw (afterRightDrain 2)).echo = true ∧
      (raw (afterRightDrain 3)).reset_cmd = true ∧
      ¬ SanitationSuccess hTwo ringFour afterRightDrain 0 := by
  refine ⟨source_collar, source_leaderless, source_labels,
    after_leaderless, after_labels, after_tail_echo,
    after_outside_reset, ?_⟩
  intro hsuccess
  unfold SanitationSuccess at hsuccess
  rcases hsuccess with hleader | hsan
  · unfold HasLeader at hleader
    rcases hleader with ⟨i, hi⟩
    have hz := after_leaderless i
    have hbad : true = false := hi.symm.trans hz
    cases hbad
  · unfold ThreeSiteSanitized at hsan
    rcases hsan with ⟨_, _, hp2, _⟩
    exact after_tail_not_passive hp2

/-! ## The deletion drain does not produce the collar -/

/-- Same cyclic labels, but now the outside successor itself carries reset
    garbage.  Prepared-deletion inactivity cannot see this field. -/
private def outsideDirtyRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell d0
  else if i = 1 then cell d1
  else if i = 2 then cell d0
  else { cell d1 with reset_cmd := true }

private theorem outsideDirtyRaw_domain (i : Fin 4) :
    (outsideDirtyRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [outsideDirtyRaw, d0, d1, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private def outsideDirtySource : FC4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (outsideDirtyRaw i) (outsideDirtyRaw_domain i), false⟩, 0⟩

private theorem outsideDirty_noPreparedDeletion :
    CurrentNoPreparedDeletion hTwo outsideDirtySource := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide

private theorem outsideDirty_reset :
    (raw (outsideDirtySource 3)).reset_cmd = true := by
  decide

private theorem outsideDirty_not_passive :
    ¬ Passive (raw (outsideDirtySource 3)) := by
  intro hp
  have hf := passive_resetCmd_false hp
  have hbad : true = false := outsideDirty_reset.symm.trans hf
  cases hbad

/-- The exact endpoint predicate produced by the prepared-deletion drain
    has no `Passive` consequence, even on the would-be outside successor. -/
theorem q11532_drain_predicate_not_passive_producer :
    CurrentNoPreparedDeletion hTwo outsideDirtySource ∧
      ¬ Passive (raw (outsideDirtySource 3)) := by
  exact ⟨outsideDirty_noPreparedDeletion, outsideDirty_not_passive⟩

/-! ## Purely local clock-source composition -/

/-- Local replacement for using
`BirthPhaseClockSourceAudit.localLine3At_of_hostPassive_hostCyclic_zero` with
its global hypotheses.  `LocalLine3At` itself asks for exactly these three
passivity facts and three ruler equations, so no state outside the triple is
mentioned. -/
theorem localLine3At_of_threeSiteSanitized
    (hpsi : 0 < psi) (hn : 4 <= n)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau)
    (a : Fin n)
    (h : ThreeSiteSanitized hpsi ring C a) :
    LocalLine3At hpsi hn ring a C := by
  unfold ThreeSiteSanitized TripleLabels at h
  rcases h with ⟨hp0, hp1, hp2, hl0, hl1, hl2⟩
  exact
    { pass0 := hp0
      pass1 := hp1
      pass2 := hp2
      lab0 := hl0
      lab1 := hl1
      lab2 := hl2 }

end Q11632RightDrainCollar

#print axioms Q11632RightDrainCollar.passive_resetCmd_false
#print axioms Q11632RightDrainCollar.passive_echo_false
#print axioms Q11632RightDrainCollar.one_successor_right_drain_counterexample
#print axioms Q11632RightDrainCollar.q11532_drain_predicate_not_passive_producer
#print axioms Q11632RightDrainCollar.localLine3At_of_threeSiteSanitized
