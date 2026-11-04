import Leader.Wu.Elimination.SinkEvidenceUnshieldKernel


open LDSinkGapCleanup LDSinkKernelC LDSinkKernelCPrime
  LDSinkStallWitness PPLLRepair


namespace LDSinkKernelCDouble


/-- K2'' carries one additional finite bit without modifying `AgentState`. -/
structure LState (ψ : Nat) where
  core : AgentState ψ
  livePending : Bool


/--
Post-FIRE MOVE for K2''.  On the parked-live/follower-responder cell, an
unshielded leader is killed exactly as by the egress MOVE; a shielded leader
with post-FIRE `signal_B = 0` and entry snapshot `hadLive = false` is unshielded
without consuming the parked live bullet; otherwise the protected live bullet
is absorbed.  Off that cell, use the original zero-leader-egress MOVE.


The `r.leader = false` conjunct is intentional and forced by the requested
arbitrary-state K2 core-equality theorem: K2's `absorbProtectedMove` has exactly
that responder-follower guard.  Without it, a shielded initiator facing a live
bullet stored on a responder leader would be absorbed here but not by K2.
-/
def pendingShotMove {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (hadLive : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if r.bullet = (2 : Fin 3) ∧ l.leader = true ∧ r.leader = false then
    if l.shield = false then
      ({ l with leader := false }, { r with bullet := (1 : Fin 3) })
    else if l.signal_B = (0 : Fin 2) ∧ hadLive = false then
      ({ l with shield := false }, r)
    else
      (l, { r with bullet := (0 : Fin 3) })
  else
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r


/-- With an entry live shot pending, the new unshield branch is disabled and
MOVE is exactly K2's protected MOVE on arbitrary cores. -/
private theorem pendingShotMove_true_eq_absorbProtectedMove {ψ : Nat}
    (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ) :
    pendingShotMove hψ nl true l r = absorbProtectedMove hψ nl l r := by
  by_cases hb : r.bullet = (2 : Fin 3)
  · cases hl : l.leader <;>
      cases hs : l.shield <;>
      cases hr : r.leader <;>
      simp [pendingShotMove, absorbProtectedMove,
        eliminateLeadersNoCollisionZeroLeaderEgressMove,
        hb, hl, hs, hr]
  · simp [pendingShotMove, absorbProtectedMove, hb]


/--
K2'' runs FIRE/MOVE/SIGNAL/dummy-sink on `core`.


`hadLive` is the entry snapshot `l.livePending`.  The initiator bit is set to
`true` exactly when the pre-FIRE core satisfies the LIVE FIRE guard
`leader = true ∧ signal_B = 1`; otherwise it is retained.  The responder bit is
cleared exactly when the post-SIGNAL responder is still a leader and has
`signal_B = 1`; otherwise it is retained.  The clear test is deliberately on
`q2`, before `dummyBulletSink`, which changes only the bullet field.
-/
def sinkKernelC'' {ψ : Nat} (hψ : ψ > 0)
    (l r : LState ψ) : LState ψ × LState ψ :=
  let hadLive := l.livePending
  let nl : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l.core r.core
  let q1 := pendingShotMove hψ nl hadLive q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  let q3 := dummyBulletSink q2
  let leftPending :=
    if l.core.leader = true ∧ l.core.signal_B = (1 : Fin 2) then
      true
    else
      l.livePending
  let rightPending :=
    if q2.2.signal_B = (1 : Fin 2) ∧ q2.2.leader = true then
      false
    else
      r.livePending
  ({ core := q3.1, livePending := leftPending },
   { core := q3.2, livePending := rightPending })


/-- If the initiator already has a LIVE shot pending, K2'' is K2 on both
physical cores. -/
theorem kernelC''_core_eq_kernelC_of_hadLive {ψ : Nat}
    (hψ : ψ > 0) (l r : LState ψ)
    (hhad : l.livePending = true) :
    (sinkKernelC'' hψ l r).1.core =
        (sinkKernelC hψ l.core r.core).1 ∧
      (sinkKernelC'' hψ l r).2.core =
        (sinkKernelC hψ l.core r.core).2 := by
  simp only [sinkKernelC'', sinkKernelC, hhad,
    pendingShotMove_true_eq_absorbProtectedMove]
  exact ⟨trivial, trivial⟩


/-! ## Six-agent parked-bullet stall -/


/-- Lift the checked six-agent stall.  Exactly the three leaders carry the
extra evidence that their left-going LIVE shots are still outstanding. -/
def stallL (i : Fin 6) : LState 1 :=
  { core := LDSinkStallWitness.stall i
    livePending :=
      match i.val with
      | 0 => true
      | 2 => true
      | 4 => true
      | _ => false }


/-- On edge `(0,1)`, K2'' takes the K2 absorption branch: the parked LIVE is
consumed and leader 0 survives. -/
theorem stallL_edge0_absorbs :
    let q := sinkKernelC'' (by decide : 1 > 0)
      (stallL (0 : Fin 6)) (stallL (1 : Fin 6))
    q.2.core.bullet = (0 : Fin 3) ∧
      q.1.core.leader = true ∧ q.1.livePending = true := by
  decide


/-- One wrapped local edge update on the six-cycle. -/
def stepL (C : Fin 6 → LState 1) (e : Fin 6) : Fin 6 → LState 1 :=
  let j := LDSinkStallWitness.rightNeighbor e
  let q := sinkKernelC'' (by decide : 1 > 0) (C e) (C j)
  fun i =>
    if i = e then q.1
    else if i = j then q.2
    else C i


/-- Execute a finite edge schedule in its listed order. -/
def runL : List (Fin 6) → (Fin 6 → LState 1) → (Fin 6 → LState 1)
  | [], C => C
  | e :: es, C => runL es (stepL C e)


/-- Boolean enumeration of the six possible leader locations. -/
def hasLeader (C : Fin 6 → LState 1) : Bool :=
  (C 0).core.leader || (C 1).core.leader || (C 2).core.leader ||
    (C 3).core.leader || (C 4).core.leader || (C 5).core.leader


/-- The explicit adversarial schedule from the stall witness. -/
def stallSchedule : List (Fin 6) := [0, 2, 4, 0, 2, 4]


/-- Exactly all seven prefixes, including the empty and full schedules. -/
def stallPrefixes : List (List (Fin 6)) :=
  [[],
   [0],
   [0, 2],
   [0, 2, 4],
   [0, 2, 4, 0],
   [0, 2, 4, 0, 2],
   [0, 2, 4, 0, 2, 4]]


/-- The full schedule and every one of its prefixes retain at least one leader. -/
theorem stallL_run_keeps_leader :
    hasLeader (runL stallSchedule stallL) = true ∧
      stallPrefixes.all (fun pfx => hasLeader (runL pfx stallL)) = true := by
  decide


/-! ## Nonempty renewal/unshield branch -/


/--
A concrete two-gap renewal cell inside six agents.  Leader 2 is shielded and
ready (`signal_B = 1`) with no old LIVE pending; cell 3 holds the parked LIVE
shot from leader 4; cell 1, on leader 2's left/attack gap, is empty.  Leaders 0
and 4 retain the outstanding-shot evidence from the stall lift.
-/
def renewL (i : Fin 6) : LState 1 :=
  match i.val with
  | 0 =>
      { core := LDSinkStallWitness.stall i, livePending := true }
  | 1 =>
      { core := { LDSinkStallWitness.stall i with
          bullet := (0 : Fin 3), signal_B := (0 : Fin 2) }
        livePending := false }
  | 2 =>
      { core := { LDSinkStallWitness.stall i with
          bullet := (0 : Fin 3), signal_B := (1 : Fin 2), shield := true }
        livePending := false }
  | 3 =>
      { core := { LDSinkStallWitness.stall i with
          bullet := (2 : Fin 3), signal_B := (0 : Fin 2) }
        livePending := false }
  | 4 =>
      { core := LDSinkStallWitness.stall i, livePending := true }
  | 5 =>
      { core := LDSinkStallWitness.stall i, livePending := false }
  | _ =>
      { core := LDSinkStallWitness.stall i, livePending := false }


/-- On `(2,3)`, leader 2 first fires its own LIVE, then the K2'' evidence branch
unshields it without consuming the parked LIVE at cell 3. -/
theorem renewL_edge2_unshields :
    let q := sinkKernelC'' (by decide : 1 > 0)
      (renewL (2 : Fin 6)) (renewL (3 : Fin 6))
    q.1.core.leader = true ∧
      q.1.core.shield = false ∧
      q.1.core.bullet = (2 : Fin 3) ∧
      q.1.core.signal_B = (0 : Fin 2) ∧
      q.1.livePending = true ∧
      q.2.core.bullet = (2 : Fin 3) := by
  decide


/-- A second `(2,3)` interaction has inert FIRE at leader 2 (`signal_B = 0`),
so the still-parked LIVE takes the ordinary unshielded kill branch. -/
theorem renewL_edge2_again_kills :
    let q1 := sinkKernelC'' (by decide : 1 > 0)
      (renewL (2 : Fin 6)) (renewL (3 : Fin 6))
    let q2 := sinkKernelC'' (by decide : 1 > 0) q1.1 q1.2
    q2.1.core.leader = false ∧ q2.2.core.bullet = (1 : Fin 3) := by
  decide


#print axioms kernelC''_core_eq_kernelC_of_hadLive
#print axioms stallL_edge0_absorbs
#print axioms stallL_run_keeps_leader
#print axioms renewL_edge2_unshields
#print axioms renewL_edge2_again_kills


end LDSinkKernelCDouble
