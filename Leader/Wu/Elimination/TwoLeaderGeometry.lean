import Leader.Wu.Elimination.CyclicLayout
import Leader.Wu.RaceEntrance.ArrivalRaceMass

/-!
The last two separated leaders determine two complementary gaps.  Their
outer endpoints coincide and their lengths sum to the whole ring.  This
proof-side interface is the actual two-entry canonical cyclic layout; it
does not construct a `TwoGapFrame`, whose strict span bound would be false.

The race below starts with an explicit parked live bullet and a signaled
victim.  It follows the same raw K2 scheduler word, including early endpoint
deletions.  It supplies no procedure for producing that initial readiness.
-/

set_option autoImplicit false

namespace K2TwoLeaderGeometry

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDTwoGapFrame K2OutputSafety K2GlobalGapClosure K2CyclicLayout
  FiniteUniformStoppingTree LDSinkTwoGapDeletion

variable {n ψ : Nat}

/-- Only existing geometric data: two consecutive gaps covering the ring. -/
abbrev TwoLeaderFrame (n : Nat) := CyclicLayout n 2

namespace TwoLeaderFrame

def recovery (F : TwoLeaderFrame n) : GapFrame n := F.gap 0
def attack (F : TwoLeaderFrame n) : GapFrame n := F.gap 1

theorem shared_endpoint (F : TwoLeaderFrame n) :
    F.recovery.pos F.recovery.d = F.attack.pos 0 := F.shared 0

/-- The attack shooter is the recovery victim: one physical outer leader. -/
theorem outer_alias (F : TwoLeaderFrame n) :
    F.attack.pos F.attack.d = F.recovery.pos 0 := F.shared 1

theorem lengths_sum (F : TwoLeaderFrame n) :
    F.recovery.d + F.attack.d = n := by
  simpa [recovery, attack, List.ofFn_succ] using F.mass

theorem four_le (F : TwoLeaderFrame n) : 4 ≤ n := by
  have := F.recovery.hd
  have := F.attack.hd
  have := F.lengths_sum
  omega

private theorem pos_zero (G : GapFrame n) : G.pos 0 = G.low := by
  apply Fin.ext
  simp [GapFrame.pos, Nat.mod_eq_of_lt G.low.isLt]

/-- Coordinate translation remains valid when the combined arc wraps. -/
theorem attack_pos_offset (F : TwoLeaderFrame n) (t : Nat) :
    F.attack.pos t = F.recovery.pos (F.recovery.d + t) := by
  have hlow : F.attack.low = F.recovery.pos F.recovery.d :=
    (pos_zero F.attack).symm.trans F.shared_endpoint.symm
  have hval := congrArg Fin.val hlow
  apply Fin.ext
  change (F.attack.low.val + t) % n =
    (F.recovery.low.val + (F.recovery.d + t)) % n
  change F.attack.low.val = (F.recovery.low.val + F.recovery.d) % n at hval
  rw [hval, Nat.add_mod, Nat.mod_mod]
  simpa only [Nat.add_assoc] using
    (Nat.add_mod (F.recovery.low.val + F.recovery.d) t n).symm

end TwoLeaderFrame

private theorem ring_eq (R R' : DirectedRing n) : R = R' := by
  cases R
  cases R'
  rfl

/-- Canonical selection changes no protocol field or configuration. -/
def canonicalFrame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) :
    TwoLeaderFrame n := canonicalLayout hψ ring C hC

def WrapInvariant (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  GapInvariant hψ F.recovery C ∧ GapInvariant hψ F.attack C

theorem canonical_invariants (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) :
    WrapInvariant hψ (canonicalFrame hψ ring C hC) C :=
  ⟨canonicalLayout_invariants hψ ring C hC 0,
    canonicalLayout_invariants hψ ring C hC 1⟩

def preparePort (F : TwoLeaderFrame n) : Fin n :=
  F.recovery.pos (F.recovery.d - 1)
def deletePort (F : TwoLeaderFrame n) : Fin n := F.attack.pos 0
def overwritePort (F : TwoLeaderFrame n) : Fin n := F.attack.pos 1
def outerLeader (F : TwoLeaderFrame n) : Fin n := F.recovery.pos 0
def outerIncoming (F : TwoLeaderFrame n) : Fin n :=
  F.attack.pos (F.attack.d - 1)

/-- These are exactly the two actual leader positions, not a supplied list. -/
theorem canonical_leaders (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) (v : Fin n) :
    (C v).leader = true ↔
      v = outerLeader (canonicalFrame hψ ring C hC) ∨
      v = deletePort (canonicalFrame hψ ring C hC) := by
  rw [canonicalLayout_covers hψ ring C hC v]
  constructor
  · rintro ⟨i, hi⟩
    rcases fin2_cases i with rfl | rfl
    · left
      simpa [outerLeader, TwoLeaderFrame.recovery, canonicalFrame,
        GapFrame.pos, Nat.mod_eq_of_lt] using hi.symm
    · right
      simpa [deletePort, TwoLeaderFrame.attack, canonicalFrame,
        GapFrame.pos, Nat.mod_eq_of_lt] using hi.symm
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [outerLeader, TwoLeaderFrame.recovery, canonicalFrame,
        GapFrame.pos, Nat.mod_eq_of_lt]⟩
    · exact ⟨1, by simp [deletePort, TwoLeaderFrame.attack, canonicalFrame,
        GapFrame.pos, Nat.mod_eq_of_lt]⟩

theorem prepare_ne_delete (F : TwoLeaderFrame n) :
    preparePort F ≠ deletePort F := by
  unfold preparePort deletePort
  rw [← F.shared_endpoint]
  exact F.recovery.pos_ne (by have := F.recovery.hdn; omega)
    F.recovery.hdn (by have := F.recovery.hd; omega)

theorem prepare_ne_overwrite (F : TwoLeaderFrame n) :
    preparePort F ≠ overwritePort F := by
  unfold preparePort overwritePort
  rw [F.attack_pos_offset]
  have := F.lengths_sum
  have := F.recovery.hd
  have := F.attack.hd
  exact F.recovery.pos_ne (by omega) (by omega) (by omega)

theorem delete_ne_overwrite (F : TwoLeaderFrame n) :
    deletePort F ≠ overwritePort F := by
  exact F.attack.pos_ne (by have := F.four_le; omega)
    (by have := F.four_le; omega) (by omega)

/-- The aliased outer leader is a fourth site, distinct from all race ports. -/
theorem outer_ne_ports (F : TwoLeaderFrame n) :
    outerLeader F ≠ preparePort F ∧ outerLeader F ≠ deletePort F ∧
      outerLeader F ≠ overwritePort F := by
  have hr := F.recovery.hd
  have ha := F.attack.hd
  have hn := F.lengths_sum
  constructor
  · exact F.recovery.pos_ne (by omega) (by omega) (by omega)
  constructor
  · unfold outerLeader deletePort
    rw [← F.shared_endpoint]
    exact F.recovery.pos_ne (by omega) (by omega) (by omega)
  · unfold outerLeader overwritePort
    rw [F.attack_pos_offset]
    exact F.recovery.pos_ne (by omega) (by omega) (by omega)

theorem prepare_right (F : TwoLeaderFrame n) (ring : DirectedRing n) :
    ring.rightNeighbor (preparePort F) = deletePort F := by
  rw [ring_eq ring F.recovery.ring]
  unfold preparePort deletePort
  rw [GapFrame.rightNeighbor_pos,
    show F.recovery.d - 1 + 1 = F.recovery.d by have := F.recovery.hd; omega]
  exact F.shared_endpoint

theorem delete_right (F : TwoLeaderFrame n) (ring : DirectedRing n) :
    ring.rightNeighbor (deletePort F) = overwritePort F := by
  rw [ring_eq ring F.attack.ring]
  exact GapFrame.rightNeighbor_pos F.attack 0

theorem outerIncoming_right (F : TwoLeaderFrame n) (ring : DirectedRing n) :
    ring.rightNeighbor (outerIncoming F) = outerLeader F := by
  rw [ring_eq ring F.attack.ring]
  unfold outerIncoming outerLeader
  rw [GapFrame.rightNeighbor_pos,
    show F.attack.d - 1 + 1 = F.attack.d by have := F.attack.hd; omega]
  exact F.outer_alias

/-- At recovery length two, the outer outgoing row writes A as responder.
The race proof therefore preserves only A's follower flag and label there. -/
theorem outer_right_eq_prepare_iff (F : TwoLeaderFrame n) (ring : DirectedRing n) :
    ring.rightNeighbor (outerLeader F) = preparePort F ↔ F.recovery.d = 2 := by
  rw [ring_eq ring F.recovery.ring]
  unfold outerLeader preparePort
  rw [GapFrame.rightNeighbor_pos]
  constructor
  · intro h
    have he := F.recovery.pos_inj (by have := F.four_le; omega)
      (by have := F.recovery.hdn; omega) h
    have := F.recovery.hd
    omega
  · intro h
    simp [h]

/-- At the shortest separated attack gap, the outer leader's incoming edge
is precisely competitor C.  It is never silently treated as a neutral row. -/
theorem outerIncoming_eq_overwrite_iff (F : TwoLeaderFrame n) :
    outerIncoming F = overwritePort F ↔ F.attack.d = 2 := by
  constructor
  · intro h
    have he := F.attack.pos_inj
      (by have := F.attack.hdn; omega) (by have := F.four_le; omega) h
    have := F.attack.hd
    omega
  · intro h
    simp [outerIncoming, overwritePort, h]

theorem outerIncoming_ne_prepare (F : TwoLeaderFrame n) :
    outerIncoming F ≠ preparePort F := by
  unfold outerIncoming preparePort
  rw [F.attack_pos_offset]
  have := F.recovery.hd
  have := F.attack.hd
  have := F.lengths_sum
  exact F.recovery.pos_ne (by omega) (by omega) (by omega)

theorem outerIncoming_ne_delete (F : TwoLeaderFrame n) :
    outerIncoming F ≠ deletePort F := by
  have := F.attack.hd
  have := F.attack.hdn
  exact F.attack.pos_ne (by omega) (by omega) (by omega)

def ports (F : TwoLeaderFrame n) : ThreePortSerialCount.Ports n :=
  ⟨preparePort F, deletePort F, overwritePort F,
    prepare_ne_delete F, prepare_ne_overwrite F, delete_ne_overwrite F⟩

/-- The stopping event names both real endpoints, with the outer alias
resolved.  Either leader may be deleted before the protected race finishes. -/
def Deleted (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (deletePort F)).leader = false ∨ (C (outerLeader F)).leader = false

theorem deleted_iff_attack (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) :
    Deleted F C ↔ EndpointDeleted F.attack C := by
  unfold Deleted EndpointDeleted deletePort outerLeader
  rw [F.outer_alias]

theorem deleted_iff_recovery (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) :
    Deleted F C ↔ EndpointDeleted F.recovery C := by
  unfold Deleted EndpointDeleted deletePort outerLeader
  rw [F.shared_endpoint]
  exact Or.comm

/-- Both actual gap invariants survive every nondeleting raw row, including
both edges incident to the same outer leader.  No disjointness is assumed. -/
theorem wrapInvariant_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (h : WrapInvariant hψ F C) (e : Fin n)
    (hd : ¬ Deleted F (rawStep hψ ring C e)) :
    WrapInvariant hψ F (rawStep hψ ring C e) := by
  constructor
  · rw [rawStep_eq_frame hψ ring F.recovery]
    apply gap_step hψ F.recovery C h.1 e
    rw [← rawStep_eq_frame hψ ring F.recovery]
    exact fun he => hd ((deleted_iff_recovery F _).mpr he)
  · rw [rawStep_eq_frame hψ ring F.attack]
    apply gap_step hψ F.attack C h.2 e
    rw [← rawStep_eq_frame hψ ring F.attack]
    exact fun he => hd ((deleted_iff_attack F _).mpr he)

private theorem right_injective (ring : DirectedRing n) (e f : Fin n)
    (h : ring.rightNeighbor e = ring.rightNeighbor f) : e = f := by
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at hv
  have he := e.isLt
  have hf := f.isLt
  apply Fin.ext
  by_cases he1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he1] at hv
    by_cases hf1 : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf1] at hv
      omega
    · rw [show f.val + 1 = n by omega, Nat.mod_self] at hv
      omega
  · rw [show e.val + 1 = n by omega, Nat.mod_self] at hv
    by_cases hf1 : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf1] at hv
      omega
    · omega

/-- Equality of complete states at B and C, hence of signal, shield, and
bullet fields, for every edge outside A/B/C.  A itself need not be framed. -/
theorem neutral_frames (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (e : Fin n)
    (ha : e ≠ preparePort F) (hb : e ≠ deletePort F)
    (hc : e ≠ overwritePort F) :
    rawStep hψ ring C e (deletePort F) = C (deletePort F) ∧
      rawStep hψ ring C e (overwritePort F) = C (overwritePort F) := by
  constructor
  · apply updatePair_other _ _ _ _ _ hb.symm
    intro he
    exact ha (right_injective ring e (preparePort F)
      (he.symm.trans (prepare_right F ring).symm))
  · apply updatePair_other _ _ _ _ _ hc.symm
    intro he
    exact hb (right_injective ring e (deletePort F)
      (he.symm.trans (delete_right F ring).symm))

/-- The outer leader's outgoing edge frames the race's victim and live shot,
even when its responder is A (recovery length two). -/
theorem outer_outgoing_frames (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) :
    rawStep hψ ring C (outerLeader F) (deletePort F) = C (deletePort F) ∧
      rawStep hψ ring C (outerLeader F) (overwritePort F) = C (overwritePort F) :=
  neutral_frames hψ ring F C _ (outer_ne_ports F).1
    (outer_ne_ports F).2.1 (outer_ne_ports F).2.2

/-- At attack length greater than two the outer incoming edge is neutral;
at length two it is C, as proved above.  These exhaust the wraparound cases. -/
theorem outer_incoming_frames (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (hb : 2 < F.attack.d) :
    rawStep hψ ring C (outerIncoming F) (deletePort F) = C (deletePort F) ∧
      rawStep hψ ring C (outerIncoming F) (overwritePort F) = C (overwritePort F) := by
  apply neutral_frames hψ ring F C _ (outerIncoming_ne_prepare F)
    (outerIncoming_ne_delete F)
  intro he
  have := (outerIncoming_eq_overwrite_iff F).mp he
  omega

/-- Literal source FIRE row, including the subsequent MOVE, SIGNAL, and
dummy sink: the firing source remains shielded with its fresh live bullet. -/
theorem kernel_source_fire (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = 1) :
    (sinkKernelC hψ l r).1 =
      { l with bullet := 2, shield := true, signal_B := 0 } := by
  rcases fin2_cases r.signal_B with hsg | hsg <;>
    cases hr : r.leader <;>
    rcases fin3_cases r.bullet with hb | hb | hb <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire,
      absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
      hl, hs, hr, hsg, hb]

/-- The same outer node fires as a source on its outgoing edge; neither its
state nor its shield is incorrectly framed across that physical row. -/
theorem outer_outgoing_fire (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (hl : (C (outerLeader F)).leader = true)
    (hs : (C (outerLeader F)).signal_B = 1) :
    rawStep hψ ring C (outerLeader F) (F.attack.pos F.attack.d) =
      { C (outerLeader F) with bullet := 2, shield := true, signal_B := 0 } := by
  rw [F.outer_alias]
  change rawStep hψ ring C (outerLeader F) (outerLeader F) = _
  simpa [rawStep, updatePair] using kernel_source_fire hψ
    (C (outerLeader F)) (C (ring.rightNeighbor (outerLeader F))) hl hs

/-- On its incoming edge the very same outer leader is a responder.  The
actual aligned follower/leader row clears its shield, signal, and bullet. -/
theorem outer_incoming_prepare (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (hi : GapInvariant hψ F.attack C)
    (hs : (C (outerLeader F)).signal_B = 1) :
    let q := rawStep hψ ring C (outerIncoming F) (outerLeader F)
    q.leader = true ∧ q.shield = false ∧ q.signal_B = 0 ∧ q.bullet = 0 := by
  have hd := F.attack.hd
  have hn := F.attack.hdn
  have hp : F.attack.d - 1 + 1 = F.attack.d := by omega
  have hl : (C (outerIncoming F)).leader = false := hi.2.1 _ (by omega) (by omega)
  have hr : (C (outerLeader F)).leader = true := by
    simpa only [F.outer_alias, outerLeader] using hi.1.2
  have ha : (C (outerLeader F)).label = nextLabel hψ (C (outerIncoming F)) := by
    have hh := hi.2.2.1 (F.attack.d - 1) (by omega)
    simpa only [hp, F.outer_alias, outerLeader, outerIncoming] using hh
  have hne : outerLeader F ≠ outerIncoming F := by
    unfold outerLeader outerIncoming
    rw [← F.outer_alias]
    exact F.attack.pos_ne hn (by omega) (by omega)
  have hrow := LDSinkTwoGapArrivalRaceMass.kernelC_prepare_responder hψ
    (C (outerIncoming F)) (C (outerLeader F)) hl hr hs ha
  simpa only [rawStep, outerIncoming_right, updatePair, if_neg hne, ite_true]
    using hrow

/-- Explicit entrance condition.  No fresh-state producer is assumed or
encoded as a field: the two values are read from the supplied configuration. -/
def RaceReady (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (overwritePort F)).bullet = 2 ∧ (C (deletePort F)).signal_B = 1

structure FirstReady (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) : Prop where
  incoming_follower : (C (preparePort F)).leader = false
  victim_leader : (C (deletePort F)).leader = true
  victim_signal : (C (deletePort F)).signal_B = 1
  incoming_aligned : (C (deletePort F)).label = nextLabel hψ (C (preparePort F))
  parked_follower : (C (overwritePort F)).leader = false
  parked_live : (C (overwritePort F)).bullet = 2

structure SecondReady (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) : Prop where
  victim_leader : (C (deletePort F)).leader = true
  victim_shield : (C (deletePort F)).shield = false
  victim_signal : (C (deletePort F)).signal_B = 0
  parked_follower : (C (overwritePort F)).leader = false
  parked_live : (C (overwritePort F)).bullet = 2

theorem firstReady_of_invariant (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C)
    (hr : RaceReady F C) : FirstReady hψ F C := by
  have hd := F.recovery.hd
  have ha := F.attack.hd
  have hp : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  refine ⟨hg.1.2.1 _ (by omega) (by omega), hg.2.1.1, hr.2, ?_,
    hg.2.2.1 1 (by omega) (by omega), hr.1⟩
  have hh := hg.1.2.2.1 (F.recovery.d - 1) (by omega)
  simpa only [hp, F.shared_endpoint, deletePort, preparePort] using hh

/-- Incoming follower status and labels have unconditional K2 preservation;
the two race cells have the exact state equalities proved above. -/
theorem firstReady_neutral (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (h : FirstReady hψ F C)
    (e : Fin n) (ha : e ≠ preparePort F) (hb : e ≠ deletePort F)
    (hc : e ≠ overwritePort F) : FirstReady hψ F (rawStep hψ ring C e) := by
  have hf := neutral_frames hψ ring F C e ha hb hc
  constructor
  · exact rawStep_follower hψ ring C e _ h.incoming_follower
  · exact (congrArg AgentState.leader hf.1).trans h.victim_leader
  · exact (congrArg AgentState.signal_B hf.1).trans h.victim_signal
  · simpa only [nextLabel, rawStep_label] using h.incoming_aligned
  · exact (congrArg AgentState.leader hf.2).trans h.parked_follower
  · exact (congrArg AgentState.bullet hf.2).trans h.parked_live

/-- The A row prepares B and frames the parked live bullet at C. -/
theorem firstReady_prepare (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (h : FirstReady hψ F C) :
    SecondReady F (rawStep hψ ring C (preparePort F)) := by
  have hrow := LDSinkTwoGapArrivalRaceMass.kernelC_prepare_responder hψ
    (C (preparePort F)) (C (deletePort F)) h.incoming_follower h.victim_leader
    h.victim_signal h.incoming_aligned
  have hv : rawStep hψ ring C (preparePort F) (deletePort F) =
      (sinkKernelC hψ (C (preparePort F)) (C (deletePort F))).2 := by
    simp only [rawStep, prepare_right]
    exact updatePair_responder _ _ _ _ (prepare_ne_delete F).symm
  have hp : rawStep hψ ring C (preparePort F) (overwritePort F) =
      C (overwritePort F) := by
    apply updatePair_other _ _ _ _ _ (prepare_ne_overwrite F).symm
    rw [prepare_right]
    exact (delete_ne_overwrite F).symm
  exact ⟨(congrArg AgentState.leader hv).trans hrow.1,
    (congrArg AgentState.shield hv).trans hrow.2.1,
    (congrArg AgentState.signal_B hv).trans hrow.2.2.1,
    (congrArg AgentState.leader hp).trans h.parked_follower,
    (congrArg AgentState.bullet hp).trans h.parked_live⟩

theorem secondReady_neutral (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (h : SecondReady F C)
    (e : Fin n) (ha : e ≠ preparePort F) (hb : e ≠ deletePort F)
    (hc : e ≠ overwritePort F) : SecondReady F (rawStep hψ ring C e) := by
  have hf := neutral_frames hψ ring F C e ha hb hc
  exact ⟨(congrArg AgentState.leader hf.1).trans h.victim_leader,
    (congrArg AgentState.shield hf.1).trans h.victim_shield,
    (congrArg AgentState.signal_B hf.1).trans h.victim_signal,
    (congrArg AgentState.leader hf.2).trans h.parked_follower,
    (congrArg AgentState.bullet hf.2).trans h.parked_live⟩

/-- The B row deletes the actual victim after its own FIRE test. -/
theorem secondReady_delete (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (h : SecondReady F C) :
    Deleted F (rawStep hψ ring C (deletePort F)) := by
  have hrow := LDSinkTwoGapArrivalRaceMass.kernelC_delete_prepared hψ
    (C (deletePort F)) (C (overwritePort F)) h.victim_leader h.victim_shield
    h.victim_signal h.parked_follower h.parked_live
  apply Or.inl
  simpa [rawStep, delete_right, updatePair] using hrow

/-- An observation wrapper around the actual raw K2 configuration update.
There are no failure/reset rows and no physical ghost-phase changes. -/
noncomputable def physicalStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    StopNode (Fin n → AgentState ψ) := by
  classical
  exact if Deleted F (rawStep hψ ring C e) then .success
    else .active (rawStep hψ ring C e)

theorem physicalStep_active_iff (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C C' : Fin n → AgentState ψ) (e : Fin n) :
    physicalStep hψ ring F C e = .active C' ↔
      ¬ Deleted F (rawStep hψ ring C e) ∧ C' = rawStep hψ ring C e := by
  classical
  simp only [physicalStep]
  split <;> simp_all [eq_comm]

theorem physicalStep_success_iff (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    physicalStep hψ ring F C e = .success ↔ Deleted F (rawStep hψ ring C e) := by
  classical
  simp only [physicalStep]
  split <;> simp_all

/-- The counted Boolean phase is a proof-side progress marker.  In either
phase the target remains the actual configuration on the same edge word. -/
def raceRel (hψ : 0 < ψ) (F : TwoLeaderFrame n) :
    StopNode Bool → StopNode (Fin n → AgentState ψ) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active false, .active C => FirstReady hψ F C
  | .active true, .active C => SecondReady F C
  | _, _ => False

private theorem raceRel_success (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (u : StopNode Bool) : raceRel hψ F u .success := by
  cases u with
  | failure => trivial
  | success => trivial
  | active p => cases p <;> trivial

private theorem raceRel_active_next (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (p : Bool) (C : Fin n → AgentState ψ)
    (h : raceRel hψ F (.active p) (.active C)) (e : Fin n) :
    raceRel hψ F (ThreePortSerialCount.serialStep (ports F) p e)
      (physicalStep hψ ring F C e) := by
  classical
  unfold physicalStep
  by_cases hd : Deleted F (rawStep hψ ring C e)
  · rw [if_pos hd]
    exact raceRel_success hψ F _
  · rw [if_neg hd]
    cases p with
    | false =>
      change FirstReady hψ F C at h
      change raceRel hψ F
        (if e = preparePort F then .active true
          else if e = deletePort F then .failure
          else if e = overwritePort F then .failure else .active false)
        (.active (rawStep hψ ring C e))
      by_cases ha : e = preparePort F
      · rw [if_pos ha]
        subst e
        exact firstReady_prepare hψ ring F C h
      · rw [if_neg ha]
        by_cases hb : e = deletePort F
        · rw [if_pos hb]
          trivial
        · rw [if_neg hb]
          by_cases hc : e = overwritePort F
          · rw [if_pos hc]
            trivial
          · rw [if_neg hc]
            exact firstReady_neutral hψ ring F C h e ha hb hc
    | true =>
      change SecondReady F C at h
      change raceRel hψ F
        (if e = deletePort F then .success
          else if e = preparePort F then .failure
          else if e = overwritePort F then .failure else .active true)
        (.active (rawStep hψ ring C e))
      by_cases hb : e = deletePort F
      · subst e
        exact (hd (secondReady_delete hψ ring F C h)).elim
      · rw [if_neg hb]
        by_cases ha : e = preparePort F
        · rw [if_pos ha]
          trivial
        · rw [if_neg ha]
          by_cases hc : e = overwritePort F
          · rw [if_pos hc]
            trivial
          · rw [if_neg hc]
            exact secondReady_neutral hψ ring F C h e ha hb hc

/-- Exact same-edge simulation of the existing serial three-port tree.
Source failures may be discarded; an early physical deletion is success. -/
theorem race_simulation (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) :
    SuccessSimulation (ThreePortSerialCount.serialStep (ports F))
      (physicalStep hψ ring F) (raceRel hψ F) where
  terminal := by
    intro u v h
    cases u with
    | failure => exact Nat.zero_le _
    | active p => exact Nat.zero_le _
    | success =>
      cases v with
      | success => exact Nat.le_refl _
      | failure => exact h.elim
      | active C => exact h.elim
  next := by
    intro u v h e
    cases u with
    | failure => trivial
    | success =>
      cases v with
      | success => trivial
      | failure => exact h.elim
      | active C => exact h.elim
    | active p =>
      cases v with
      | success => exact raceRel_success hψ F _
      | failure => cases p <;> exact h.elim
      | active C => exact raceRel_active_next hψ ring F p C h e

theorem serial_count_le_physical (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (h : FirstReady hψ F C) (T : Nat) :
    successCount (ThreePortSerialCount.serialStep (ports F)) (.active false) T ≤
      successCount (physicalStep hψ ring F) (.active C) T :=
  successCount_le_of_simulation (ThreePortSerialCount.serialStep (ports F))
    (physicalStep hψ ring F) (raceRel hψ F) (race_simulation hψ ring F)
    (.active false) (.active C) h T

/-- At least one sixteenth of all length-4n scheduler words delete an actual
endpoint.  Both race events consume interactions; success suffixes are
charged to the full horizon by the existing finite stopped-tree count. -/
theorem firstReady_deletion_sixteenth (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (h : FirstReady hψ F C) :
    n ^ (4 * n) ≤ 16 * successCount (physicalStep hψ ring F) (.active C) (4 * n) := by
  have hs := ThreePortSerialCount.serial_sixteenth (ports F)
    (show 3 ≤ n by have := F.four_le; omega)
  exact Nat.le_trans hs (Nat.mul_le_mul_left 16
    (serial_count_le_physical hψ ring F C h (4 * n)))

/-- The two-leader geometry and all local row premises come from the actual
count-two global class and its canonical layout.  Initial readiness remains
explicit; this theorem is not a stabilization or readiness-production bound. -/
theorem canonical_raceReady_deletion_sixteenth (hψ : 0 < ψ)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : GlobalClass hψ ring 2 C)
    (hr : RaceReady (canonicalFrame hψ ring C hC) C) :
    n ^ (4 * n) ≤ 16 * successCount
      (physicalStep hψ ring (canonicalFrame hψ ring C hC)) (.active C) (4 * n) :=
  firstReady_deletion_sixteenth hψ ring _ C
    (firstReady_of_invariant hψ _ C (canonical_invariants hψ ring C hC) hr)

/-- The initial two physical leaders, still at the fixed selected endpoints. -/
def TwoLeaderSupport (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) : Prop :=
  physicalLeaderCount C = 2 ∧
    ∀ v, (C v).leader = true ↔ v = outerLeader F ∨ v = deletePort F

theorem canonical_support (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) :
    TwoLeaderSupport (canonicalFrame hψ ring C hC) C :=
  ⟨hC.2.1, canonical_leaders hψ ring C hC⟩

/-- A first endpoint deletion leaves exactly one actual leader.  Every
other row retains the same two endpoints and count; K2 creates no leader. -/
theorem support_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (h : TwoLeaderSupport F C) (e : Fin n) :
    (Deleted F (rawStep hψ ring C e) ∧ physicalLeaderCount (rawStep hψ ring C e) = 1) ∨
      (¬ Deleted F (rawStep hψ ring C e) ∧ TwoLeaderSupport F (rawStep hψ ring C e)) := by
  rcases rawStep_layout_cases hψ ring C e with hsame | ⟨hp, hd, _⟩
  · right
    have heq : physicalLeaderCount (rawStep hψ ring C e) = physicalLeaderCount C := by
      unfold physicalLeaderCount
      apply ofFn_sum_eq
      intro i
      rw [hsame]
    have hS : TwoLeaderSupport F (rawStep hψ ring C e) :=
      ⟨heq.trans h.1, fun v => by rw [hsame]; exact h.2 v⟩
    refine ⟨?_, hS⟩
    rintro (hv | hs)
    · exact Bool.noConfusion (((hS.2 _).mpr (.inr rfl)).symm.trans hv)
    · exact Bool.noConfusion (((hS.2 _).mpr (.inl rfl)).symm.trans hs)
  · left
    have hc := physical_count_drop hψ ring C e hp hd
    rw [h.1] at hc
    refine ⟨?_, by omega⟩
    rcases (h.2 e).mp hp with he | he
    · right
      simpa only [he] using hd
    · left
      simpa only [he] using hd

/-- Ring-only observation of the actual count-one hitting event, for use by
the last-two-leaders tail.  Its continuing state is exactly the raw update. -/
noncomputable def countOneStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) : StopNode (Fin n → AgentState ψ) := by
  classical
  exact if physicalLeaderCount (rawStep hψ ring C e) = 1 then .success
    else .active (rawStep hψ ring C e)

theorem countOneStep_active_iff (hψ : 0 < ψ) (ring : DirectedRing n)
    (C C' : Fin n → AgentState ψ) (e : Fin n) :
    countOneStep hψ ring C e = .active C' ↔
      physicalLeaderCount (rawStep hψ ring C e) ≠ 1 ∧ C' = rawStep hψ ring C e := by
  classical
  simp only [countOneStep]
  split <;> simp_all [eq_comm]

theorem countOneStep_success_iff (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    countOneStep hψ ring C e = .success ↔ physicalLeaderCount (rawStep hψ ring C e) = 1 := by
  classical
  simp only [countOneStep]
  split <;> simp_all

private def countOneRel (F : TwoLeaderFrame n) :
    StopNode (Fin n → AgentState ψ) → StopNode (Fin n → AgentState ψ) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active C, .active D => C = D ∧ TwoLeaderSupport F C
  | _, _ => False

private theorem countOneRel_success (F : TwoLeaderFrame n)
    (u : StopNode (Fin n → AgentState ψ)) : countOneRel F u .success := by
  cases u <;> trivial

/-- Endpoint success is an actual first hit of count one on the identical
physical word.  The support condition is proved to persist, not assumed. -/
theorem countOne_simulation (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) :
    SuccessSimulation (physicalStep hψ ring F) (countOneStep hψ ring)
      (countOneRel F) where
  terminal := by
    intro u v h
    cases u with
    | failure => exact Nat.zero_le _
    | active C => exact Nat.zero_le _
    | success =>
      cases v with
      | success => exact Nat.le_refl _
      | failure => exact h.elim
      | active D => exact h.elim
  next := by
    intro u v h e
    cases u with
    | failure => trivial
    | success =>
      cases v with
      | success => trivial
      | failure => exact h.elim
      | active D => exact h.elim
    | active C =>
      cases v with
      | success => exact countOneRel_success F _
      | failure => exact h.elim
      | active D =>
        change C = D ∧ TwoLeaderSupport F C at h
        rcases h with ⟨rfl, h⟩
        change countOneRel F (physicalStep hψ ring F C e) (countOneStep hψ ring C e)
        classical
        rcases support_step hψ ring F C h e with ⟨hd, hc⟩ | ⟨hd, hc⟩
        · simp only [physicalStep, countOneStep, if_pos hd, if_pos hc, countOneRel]
        · have hn : physicalLeaderCount (rawStep hψ ring C e) ≠ 1 := by
            rw [hc.1]
            decide
          simp only [physicalStep, countOneStep, if_neg hd, if_neg hn, countOneRel]
          exact ⟨trivial, hc⟩

theorem endpoint_count_le_countOne (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (h : TwoLeaderSupport F C) (T : Nat) :
    successCount (physicalStep hψ ring F) (.active C) T ≤
      successCount (countOneStep hψ ring) (.active C) T :=
  successCount_le_of_simulation (physicalStep hψ ring F) (countOneStep hψ ring)
    (countOneRel F) (countOne_simulation hψ ring F)
    (.active C) (.active C) ⟨rfl, h⟩ T

/-- Concrete count-one hitting mass from the actual count-two global class.
The sole additional physical premise is the displayed initial readiness. -/
theorem canonical_raceReady_countOne_sixteenth (hψ : 0 < ψ)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : GlobalClass hψ ring 2 C)
    (hr : RaceReady (canonicalFrame hψ ring C hC) C) :
    n ^ (4 * n) ≤ 16 * successCount (countOneStep hψ ring) (.active C) (4 * n) :=
  Nat.le_trans (canonical_raceReady_deletion_sixteenth hψ ring C hC hr)
    (Nat.mul_le_mul_left 16 (endpoint_count_le_countOne hψ ring _ C
      (canonical_support hψ ring C hC) (4 * n)))

/-- A four-site, two-leader global configuration with all signals zero. -/
def seed4Start (i : Fin 4) : AgentState 1 :=
  { PPLLNoCheckBirthOutputLegitimacy.outputCore (by decide) i with
    leader := decide (i.val % 2 = 0)
    shield := false
    signal_B := 0
    bullet := if i = 3 then 2 else 0 }

theorem seed4Start_class : GlobalClass (by decide) ⟨by decide⟩ 2 seed4Start := by
  refine ⟨by decide, by decide, ?_⟩
  apply global_of_signals_zero
  · unfold Separated
    decide
  · exact cyclicLabels_one _ _
  · intro i
    rfl

/-- Two actual signal-propagation rows yield a nonempty race-ready example.
This finite witness is not a uniform entrance theorem. -/
def seed4Ready : Fin 4 → AgentState 1 :=
  rawStep (by decide) ⟨by decide⟩
    (rawStep (by decide) ⟨by decide⟩ seed4Start 0) 1

theorem seed4Ready_class : GlobalClass (by decide) ⟨by decide⟩ 2 seed4Ready := by
  refine ⟨by decide, by decide, ?_⟩
  exact global_step (by decide) ⟨by decide⟩ _
    (global_step (by decide) ⟨by decide⟩ seed4Start seed4Start_class.2.2 0) 1

/-- The minimal separated geometry exercises the endpoint alias and the
outer incoming edge's equality with C simultaneously. -/
theorem seed4Ready_geometry :
    let F := canonicalFrame (by decide) ⟨by decide⟩ seed4Ready seed4Ready_class
    F.recovery.d = 2 ∧ F.attack.d = 2 ∧
      preparePort F = 1 ∧ deletePort F = 2 ∧ overwritePort F = 3 ∧
      outerLeader F = 0 ∧ outerIncoming F = overwritePort F := by
  decide

theorem seed4Ready_raceReady :
    RaceReady (canonicalFrame (by decide) ⟨by decide⟩ seed4Ready seed4Ready_class)
      seed4Ready := by
  unfold RaceReady
  decide

/-- The concrete A,B word removes the victim and leaves the outer leader. -/
theorem seed4Ready_deletion :
    let D := rawStep (by decide) ⟨by decide⟩
      (rawStep (by decide) ⟨by decide⟩ seed4Ready 1) 2
    physicalLeaderCount D = 1 ∧ (D 2).leader = false ∧ (D 0).leader = true := by
  decide

end K2TwoLeaderGeometry

#print axioms K2TwoLeaderGeometry.TwoLeaderFrame.lengths_sum
#print axioms K2TwoLeaderGeometry.TwoLeaderFrame.outer_alias
#print axioms K2TwoLeaderGeometry.canonical_invariants
#print axioms K2TwoLeaderGeometry.canonical_leaders
#print axioms K2TwoLeaderGeometry.ports
#print axioms K2TwoLeaderGeometry.outer_right_eq_prepare_iff
#print axioms K2TwoLeaderGeometry.outerIncoming_eq_overwrite_iff
#print axioms K2TwoLeaderGeometry.wrapInvariant_step
#print axioms K2TwoLeaderGeometry.neutral_frames
#print axioms K2TwoLeaderGeometry.outer_outgoing_fire
#print axioms K2TwoLeaderGeometry.outer_incoming_prepare
#print axioms K2TwoLeaderGeometry.firstReady_prepare
#print axioms K2TwoLeaderGeometry.secondReady_delete
#print axioms K2TwoLeaderGeometry.physicalStep_active_iff
#print axioms K2TwoLeaderGeometry.physicalStep_success_iff
#print axioms K2TwoLeaderGeometry.race_simulation
#print axioms K2TwoLeaderGeometry.canonical_raceReady_deletion_sixteenth
#print axioms K2TwoLeaderGeometry.support_step
#print axioms K2TwoLeaderGeometry.countOneStep_active_iff
#print axioms K2TwoLeaderGeometry.countOneStep_success_iff
#print axioms K2TwoLeaderGeometry.countOne_simulation
#print axioms K2TwoLeaderGeometry.canonical_raceReady_countOne_sixteenth
#print axioms K2TwoLeaderGeometry.seed4Ready_class
#print axioms K2TwoLeaderGeometry.seed4Ready_geometry
#print axioms K2TwoLeaderGeometry.seed4Ready_raceReady
#print axioms K2TwoLeaderGeometry.seed4Ready_deletion
