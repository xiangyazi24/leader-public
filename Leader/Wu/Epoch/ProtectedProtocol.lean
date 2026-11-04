import Leader.Wu.Safety.CorrectedFormulation
import Leader.Wu.Protocol.BoundedProtocol

/-!
# An n-indexed distributed protected epoch

`RemoteLeaderGuardNoGo` rules out immediate protection inferred only from one
remote leader.  This separately named feasibility protocol escapes by storing a
full physical cycle certificate: each agent has `slot : Fin n`, neighboring
slots advance by one modulo `n`, and the leader role is exactly `slot = 0`.

A selected edge rewrites the responder slot to the successor of the initiator,
repairs both endpoint roles, and sanitizes all election/write carrier controls.
A globally rotated slot cycle is therefore a closed, output-preserving physical
legitimate set with exactly one leader.  The construction pays an explicit
factor `n` in local state and does not yet prove convergence from arbitrary
state; it is a viability witness, not a small-state P_PLL repair.
-/

namespace PPLLProtectedEpochProtocol

open PPLL PPLLResearchFormulation

/-- Physical bounded protocol state plus an exact ring-sized slot certificate. -/
structure EpochAgentState (n ψ κ : Nat) where
  core : BoundedAgentState ψ κ
  slot : Fin n
  deriving DecidableEq, Repr

/-- The next certificate slot on a nonempty directed ring. -/
def nextSlot (hn : n > 0) (slot : Fin n) : Fin n :=
  ⟨(slot.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The output role dictated by a physical slot. -/
def slotLeader (slot : Fin n) : Bool :=
  decide (slot.val = 0)

/-- Aggressively remove every current comparison/write/election transient while
setting the endpoint's leader bit to its slot role.  Stable data fields `bit`
and `label` are retained but are irrelevant to the epoch protocol. -/
def sanitizeEpochCore (leader : Bool)
    (u : BoundedAgentState ψ κ) : BoundedAgentState ψ κ :=
  { leader, probe := false, phase := false, bit := u.bit,
    wait := true, state := .none, path := .bot, reset := false,
    carry := false, count := 0, label := u.label, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := 0, bullet := 0, shield := true, write_state := .none,
    write := .none, last := false, last_set := false,
    last_unset := false, b_carry := false, gen_ws := false,
    ws_echo := false, signal_ws := false }

/-- Canonicalize one full endpoint without changing its slot. -/
def sanitizeEpochState (u : EpochAgentState n ψ κ) : EpochAgentState n ψ κ :=
  ⟨sanitizeEpochCore (slotLeader u.slot) u.core, u.slot⟩

/-- A local endpoint is clean exactly when canonicalization is identity. -/
def EpochClean (u : EpochAgentState n ψ κ) : Prop :=
  sanitizeEpochState u = u

/-- Sanitization is idempotent. -/
theorem sanitizeEpochState_idempotent (u : EpochAgentState n ψ κ) :
    sanitizeEpochState (sanitizeEpochState u) = sanitizeEpochState u := by
  rfl

/-- A clean endpoint's leader bit is exactly its slot role. -/
theorem EpochClean.leader_eq {u : EpochAgentState n ψ κ}
    (hu : EpochClean u) : u.core.leader = slotLeader u.slot := by
  have h := congrArg (fun s : EpochAgentState n ψ κ => s.core.leader) hu
  simpa [EpochClean, sanitizeEpochState, sanitizeEpochCore] using h.symm

/-- Local epoch transition.  Rewriting the responder is harmless on an already
covered edge because its slot is already the required successor. -/
def epochTransition (hn : n > 0)
    (l r : EpochAgentState n ψ κ) :
    EpochAgentState n ψ κ × EpochAgentState n ψ κ :=
  let lOut := sanitizeEpochState l
  let rOut := sanitizeEpochState { r with slot := nextSlot hn l.slot }
  (lOut, rOut)

/-- Every arbitrary selected edge leaves with a valid successor slot relation and
both endpoints clean.  Establishing all edges simultaneously remains the
separate convergence obligation. -/
theorem epochTransition_covers_selected (hn : n > 0)
    (l r : EpochAgentState n ψ κ) :
    let q := epochTransition hn l r
    q.2.slot = nextSlot hn q.1.slot ∧ EpochClean q.1 ∧ EpochClean q.2 := by
  unfold epochTransition
  dsimp only
  exact ⟨rfl, sanitizeEpochState_idempotent l,
    sanitizeEpochState_idempotent { r with slot := nextSlot hn l.slot }⟩

/-- Packaged finite epoch protocol. -/
def epochProtocol (hn : n > 0) (ψ κ : Nat) : PopulationProtocol where
  Q := EpochAgentState n ψ κ
  Y := LeaderOutput
  transition := epochTransition hn
  output := fun s => if s.core.leader then .leader else .follower

/-- A physical slot rotation, all local successor edges, and endpoint cleanliness.
The explicit rotation witness makes unique slot zero transparent; edge coverage
makes one-step closure local. -/
def ProtectedEpoch (hn : n > 0) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) : Prop :=
  ∃ anchor : Fin n,
    (∀ i, (C i).slot.val = (anchor.val + i.val) % n) ∧
    (∀ i, (C (ring.rightNeighbor i)).slot = nextSlot hn (C i).slot) ∧
    (∀ i, EpochClean (C i))

/-! ## Unique zero in a rotation -/

/-- Position at which a rotation with anchor `a` reaches slot zero. -/
def rotationRoot (hn : n > 0) (a : Fin n) : Fin n :=
  ⟨(n - a.val) % n, Nat.mod_lt _ hn⟩

private theorem rotationRoot_mod_zero (hn : n > 0) (a : Fin n) :
    (a.val + (rotationRoot hn a).val) % n = 0 := by
  change (a.val + (n - a.val) % n) % n = 0
  by_cases ha : a.val = 0
  · simp [ha]
  · have hsub : n - a.val < n := by omega
    rw [Nat.mod_eq_of_lt hsub]
    have hsum : a.val + (n - a.val) = n := by omega
    rw [hsum]
    exact Nat.mod_self n

private theorem rotation_mod_zero_unique (hn : n > 0) (a i : Fin n)
    (hzero : (a.val + i.val) % n = 0) : i = rotationRoot hn a := by
  apply Fin.ext
  change i.val = (n - a.val) % n
  by_cases ha : a.val = 0
  · have hi : i.val % n = i.val := Nat.mod_eq_of_lt i.isLt
    rw [ha, Nat.zero_add, hi] at hzero
    simp [ha, hzero]
  · have hsub : n - a.val < n := by omega
    rw [Nat.mod_eq_of_lt hsub]
    by_cases hlt : a.val + i.val < n
    · rw [Nat.mod_eq_of_lt hlt] at hzero
      omega
    · have hge : a.val + i.val ≥ n := by omega
      rw [Nat.mod_eq_sub_mod hge] at hzero
      have hsmall : a.val + i.val - n < n := by omega
      rw [Nat.mod_eq_of_lt hsmall] at hzero
      omega

/-! ## Operational legitimacy and semantic safety -/

/-- Every protected rotation has exactly one leader output. -/
theorem protectedEpoch_unique (hn : n > 0) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch hn ring C) :
    UniqueLeaderOutput (epochProtocol hn ψ κ) n C isLeaderOutput := by
  obtain ⟨anchor, hrotation, hcovered, hclean⟩ := hC
  let root := rotationRoot hn anchor
  refine ⟨root, ?_, ?_⟩
  · have hslot : (C root).slot.val = 0 := by
      rw [hrotation root]
      exact rotationRoot_mod_zero hn anchor
    have hleader := (hclean root).leader_eq
    change isLeaderOutput
      (if (C root).core.leader then LeaderOutput.leader
        else LeaderOutput.follower) = true
    rw [hleader]
    simp [slotLeader, hslot, isLeaderOutput]
  · intro j hj
    have hleader := (hclean j).leader_eq
    change isLeaderOutput
      (if (C j).core.leader then LeaderOutput.leader
        else LeaderOutput.follower) = true at hj
    rw [hleader] at hj
    have hrole : slotLeader (C j).slot = true := by
      cases hrole : slotLeader (C j).slot
      · simp [hrole, isLeaderOutput] at hj
      · rfl
    have hslot : (C j).slot.val = 0 := by
      apply of_decide_eq_true
      simpa [slotLeader] using hrole
    have hmod : (anchor.val + j.val) % n = 0 := by
      rw [← hrotation j]
      exact hslot
    exact rotation_mod_zero_unique hn anchor j hmod

/-- On every protected edge, the local transition is exact identity. -/
theorem epochTransition_eq_of_protected (hn : n > 0)
    (ring : DirectedRing n) (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch hn ring C) (e : Fin n) :
    epochTransition hn (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e)) := by
  obtain ⟨anchor, hrotation, hcovered, hclean⟩ := hC
  have hslot : { C (ring.rightNeighbor e) with
      slot := nextSlot hn (C e).slot } = C (ring.rightNeighbor e) := by
    exact congrArg (fun slot =>
      EpochAgentState.mk (C (ring.rightNeighbor e)).core slot)
      (hcovered e).symm
  unfold epochTransition
  rw [hslot]
  exact Prod.ext (hclean e) (hclean (ring.rightNeighbor e))

/-- Every protected configuration is a fixed point of every scheduled edge. -/
theorem epoch_step_eq_of_protected (hn : n > 0)
    (ring : DirectedRing n) (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch hn ring C) (e : Fin n) :
    PopulationProtocol.step (epochProtocol hn ψ κ) ring C e = C := by
  funext i
  have hpair := epochTransition_eq_of_protected hn ring C hC e
  unfold PopulationProtocol.step
  dsimp only [epochProtocol]
  rw [hpair]
  by_cases hi : i = e
  · simp [hi]
  · by_cases hj : i = ring.rightNeighbor e
    · rw [if_neg hi, if_pos hj]
      exact (congrArg C hj).symm
    · simp [hi, hj]

/-- The distributed protected epoch is one-step closed. -/
theorem protectedEpoch_closed (hn : n > 0) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (epochProtocol hn ψ κ) ring
      (ProtectedEpoch hn ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [epoch_step_eq_of_protected hn ring C hC e]
  exact hC

/-- Every step inside the protected epoch preserves the full pointwise output
vector; in fact it preserves the whole configuration. -/
theorem protectedEpoch_step_output (hn : n > 0) (ring : DirectedRing n) :
    StepOutputPreservingOn (epochProtocol hn ψ κ) ring
      (ProtectedEpoch hn ring) := by
  intro C hC C' hstep i
  obtain ⟨e, rfl⟩ := hstep
  rw [epoch_step_eq_of_protected hn ring C hC e]

/-- Protected epoch membership implies Wu's Definition-1 semantic safety. -/
theorem protectedEpoch_isSafe (hn : n > 0) (ring : DirectedRing n)
    {C : Fin n → EpochAgentState n ψ κ}
    (hC : ProtectedEpoch hn ring C) :
    PopulationProtocol.IsSafe (epochProtocol hn ψ κ) ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (epochProtocol hn ψ κ) ring isLeaderOutput (ProtectedEpoch hn ring)
    (protectedEpoch_closed hn ring)
    (protectedEpoch_unique hn ring)
    (protectedEpoch_step_output hn ring) hC

/-! ## Explicit non-vacuity and finite state cost -/

/-- Canonical protected rotation with anchor zero, built over arbitrary bounded
stable data. -/
def canonicalEpochConfig (base : Fin n → BoundedAgentState ψ κ) :
    Fin n → EpochAgentState n ψ κ := fun i =>
  sanitizeEpochState ⟨base i, i⟩

/-- The canonical slot assignment is an inhabited protected epoch. -/
theorem canonicalEpochConfig_protected (hn : n > 0)
    (ring : DirectedRing n) (base : Fin n → BoundedAgentState ψ κ) :
    ProtectedEpoch hn ring (canonicalEpochConfig base) := by
  refine ⟨⟨0, hn⟩, ?_, ?_, ?_⟩
  · intro i
    simp [canonicalEpochConfig, sanitizeEpochState]
    exact (Nat.mod_eq_of_lt i.isLt).symm
  · intro i
    apply Fin.ext
    simp [canonicalEpochConfig, sanitizeEpochState, DirectedRing.rightNeighbor,
      nextSlot]
  · intro i
    exact sanitizeEpochState_idempotent ⟨base i, i⟩

/-- Constructive exhaustive certificate for the explicit factor-`n` state. -/
def epochAgentState (n ψ κ : Nat) :
    ExhaustiveList (EpochAgentState n ψ κ) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (PPLLFinite.boundedAgentState ψ κ)
      (ExhaustiveList.fin n))
    (fun x => ⟨x.1, x.2⟩)
    (by intro s; exact ⟨(s.core, s.slot), rfl⟩)

/-- The distributed epoch certificate is duplicate-free. -/
theorem epochAgentState_values_nodup (n ψ κ : Nat) :
    (epochAgentState n ψ κ).values.Nodup := by
  unfold epochAgentState
  apply ExhaustiveList.values_nodup_mapSurjective
  · apply ExhaustiveList.values_nodup_prod
    · exact PPLLFinite.boundedAgentState_values_nodup ψ κ
    · exact ExhaustiveList.values_nodup_fin n
  · intro x y h
    rcases x with ⟨xc, xs⟩
    rcases y with ⟨yc, ys⟩
    cases h
    rfl

/-- The distributed epoch multiplies exact semantic cardinality by `n`. -/
theorem epochAgentState_values_length (n ψ κ : Nat) :
    (epochAgentState n ψ κ).values.length =
      (PPLLFinite.boundedAgentState ψ κ).values.length * n := by
  unfold epochAgentState ExhaustiveList.mapSurjective
  rw [List.length_map, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_fin]

/-- Every epoch state has an explicit finite index. -/
theorem epochAgentState_decode_surjective (n ψ κ : Nat) :
    Function.Surjective (epochAgentState n ψ κ).decode :=
  (epochAgentState n ψ κ).decode_surjective

/-- Exact finite-index representation of epoch states. -/
theorem epochAgentState_decode_bijective (n ψ κ : Nat) :
    Function.Injective (epochAgentState n ψ κ).decode ∧
      Function.Surjective (epochAgentState n ψ κ).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (epochAgentState_values_nodup n ψ κ),
    epochAgentState_decode_surjective n ψ κ⟩

end PPLLProtectedEpochProtocol
