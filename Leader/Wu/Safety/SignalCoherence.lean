import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
# Ghost history for coherent comparison signals

This module begins the strengthened invariant required by the closedness audit.
It intentionally does **not** claim that concrete `AgentState.path` values carry
such a history yet. Instead it isolates the mathematical certificate that a
faithfully sourced signal must eventually be connected to.

For a non-wrapping interval of positive stable-group indices, a signal records
its source ID and may survive a crossed group only if that group's ID is no
larger than its payload. The ruler-sequence peak theorem then prevents the
signal from reaching a later equal-ID group.
-/

/-- Ghost traversal evidence for one comparison signal in Wu's stable ruler
sequence. `source` and `target` are positive group indices; `payload` is the ID
carried by the signal. `survived_crossing` abstracts the intended rule that a
strictly larger encountered group eliminates the signal. -/
structure RulerSignalHistory where
  source : Nat
  target : Nat
  payload : Nat
  source_pos : 0 < source
  travels_forward : source < target
  payload_from_source : payload = trailingZeros source
  survived_crossing : ∀ k, source < k → k < target →
    trailingZeros k ≤ payload

namespace RulerSignalHistory

/-- A signal with a valid non-wrapping ruler history cannot carry the target
ID. This is the static theorem needed to rule out CHECK's `.equal` branch once
concrete path/state fields are connected to ghost histories. -/
theorem payload_ne_target (h : RulerSignalHistory) :
    h.payload ≠ trailingZeros h.target := by
  rw [h.payload_from_source]
  apply trailingZeros_survivor_cannot_match h.source h.target
    h.source_pos h.travels_forward
  intro k hsk hkt
  rw [← h.payload_from_source]
  exact h.survived_crossing k hsk hkt

/-- Equivalent formulation: an equality result contradicts a coherent history. -/
theorem not_equal_result (h : RulerSignalHistory)
    (hequal : h.payload = trailingZeros h.target) : False :=
  h.payload_ne_target hequal

end RulerSignalHistory

/-! ## Connection to concrete stable group bits -/

/-- Start position of group `i` relative to a stable-sequence leader witness. -/
def stableGroupStart {n : Nat} (ring : DirectedRing n)
    (leaderPos : Fin n) (ψ i : Nat) : Fin n :=
  ⟨(leaderPos.val + i * ψ) % n, Nat.mod_lt _ ring.hn⟩

/-- Ghost history whose payload and survival inequalities are stated using the
actual group bits of a concrete configuration. -/
structure StableSignalHistory {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n) where
  source : Nat
  target : Nat
  payload : Nat
  source_pos : 0 < source
  travels_forward : source < target
  target_in_range : target < n / ψ
  payload_from_source :
    payload = groupID ring.hn C (stableGroupStart ring leaderPos ψ source)
  survived_crossing : ∀ k, source < k → k < target →
    groupID ring.hn C (stableGroupStart ring leaderPos ψ k) ≤ payload

namespace StableSignalHistory

/-- In an actual stable group layout, a concretely sourced signal satisfying
the larger-group elimination rule cannot match its concrete target group ID. -/
theorem payload_ne_target {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn C (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (h : StableSignalHistory ring C leaderPos) :
    h.payload ≠
      groupID ring.hn C (stableGroupStart ring leaderPos ψ h.target) := by
  have hsourceRange : h.source < n / ψ :=
    Nat.lt_trans h.travels_forward h.target_in_range
  have hsourceID := hgroups h.source h.source_pos hsourceRange
  have htargetPos : 0 < h.target :=
    Nat.lt_trans h.source_pos h.travels_forward
  have htargetID := hgroups h.target htargetPos h.target_in_range
  have hpayload : h.payload = trailingZeros h.source :=
    h.payload_from_source.trans hsourceID
  have hsurvives : ∀ k, h.source < k → k < h.target →
      trailingZeros k ≤ trailingZeros h.source := by
    intro k hsk hkt
    have hkRange : k < n / ψ :=
      Nat.lt_trans hkt h.target_in_range
    calc
      trailingZeros k =
          groupID ring.hn C (stableGroupStart ring leaderPos ψ k) :=
        (hgroups k (Nat.lt_trans h.source_pos hsk) hkRange).symm
      _ ≤ h.payload := h.survived_crossing k hsk hkt
      _ = trailingZeros h.source := hpayload
  have hne := trailingZeros_survivor_cannot_match
    h.source h.target h.source_pos h.travels_forward hsurvives
  intro hequal
  apply hne
  exact hpayload.symm.trans (hequal.trans htargetID)

end StableSignalHistory

/-! ## Routes that also admit a freshly generated signal -/

/-- Stable-signal provenance at its current target group. Unlike
`StableSignalHistory`, a route permits `source = target`, which is necessary for
a signal that has just been generated inside its source group. Strict movement
turns it into the earlier history object. -/
structure StableSignalRoute {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n) where
  source : Nat
  target : Nat
  payload : Nat
  source_pos : 0 < source
  travels_forward : source ≤ target
  target_in_range : target < n / ψ
  payload_from_source :
    payload = groupID ring.hn C (stableGroupStart ring leaderPos ψ source)
  survived_crossing : ∀ k, source < k → k < target →
    groupID ring.hn C (stableGroupStart ring leaderPos ψ k) ≤ payload

namespace StableSignalRoute

/-- Once a route has left its source group it supplies the strict history used
by the ruler-sequence theorem. -/
def toHistory {ψ n : Nat} {ring : DirectedRing n}
    {C : Fin n → AgentState ψ} {leaderPos : Fin n}
    (route : StableSignalRoute ring C leaderPos)
    (hstrict : route.source < route.target) :
    StableSignalHistory ring C leaderPos where
  source := route.source
  target := route.target
  payload := route.payload
  source_pos := route.source_pos
  travels_forward := hstrict
  target_in_range := route.target_in_range
  payload_from_source := route.payload_from_source
  survived_crossing := route.survived_crossing

/-- A strictly advanced route cannot carry the stable target group's ID. -/
theorem payload_ne_target {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn C (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (route : StableSignalRoute ring C leaderPos)
    (hstrict : route.source < route.target) :
    route.payload ≠
      groupID ring.hn C
        (stableGroupStart ring leaderPos ψ route.target) :=
  (route.toHistory hstrict).payload_ne_target ring C leaderPos hgroups

end StableSignalRoute

/-! ## Concrete comparison payload extraction -/

/-- Bit carried by the path sub-signal at offset `k`, or zero when absent. -/
def comparisonPathBitAt {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n) (k : Nat) : Nat :=
  match (C ⟨(start.val + k) % n, Nat.mod_lt _ ring.hn⟩).path with
  | .some _ bit => bit
  | .bot => 0

/-- ID encoded by path sub-signals currently aligned over a group. -/
def comparisonSignalIDAt {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n) : Nat :=
  (List.range ψ).foldl (fun acc k =>
    acc + comparisonPathBitAt ring C start k * 2 ^ (ψ - 1 - k)) 0

/-- Every path component in `signalC` is present at its matching offset and
carries the corresponding bit from `targetC`. Separating the two configurations
lets a CHECK-boundary state be related back to the pre-step stable IDs. -/
def comparisonBitsMatchConfigAt {ψ n : Nat} (ring : DirectedRing n)
    (signalC targetC : Fin n → AgentState ψ) (start : Fin n) : Prop :=
  ∀ k : Nat, k < ψ →
    ∃ label bit,
      (signalC ⟨(start.val + k) % n, Nat.mod_lt _ ring.hn⟩).path =
        .some label bit ∧
      label = k ∧
      bit = if (targetC ⟨(start.val + k) % n,
        Nat.mod_lt _ ring.hn⟩).bit then 1 else 0

/-- A complete current path payload whose bits come from a possibly different
source-group start in a reference configuration. This is the runtime-field
bridge needed by provenance: the signal lives at `signalStart`, while its bits
are authenticated against `sourceStart`. -/
def comparisonBitsMatchBetweenAt {ψ n : Nat} (ring : DirectedRing n)
    (signalC sourceC : Fin n → AgentState ψ)
    (signalStart sourceStart : Fin n) : Prop :=
  ∀ k : Nat, k < ψ →
    ∃ label bit,
      (signalC ⟨(signalStart.val + k) % n, Nat.mod_lt _ ring.hn⟩).path =
        .some label bit ∧
      label = k ∧
      bit = if (sourceC ⟨(sourceStart.val + k) % n,
        Nat.mod_lt _ ring.hn⟩).bit then 1 else 0

/-- Same-configuration specialization. -/
def comparisonBitsMatchAt {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n) : Prop :=
  comparisonBitsMatchConfigAt ring C C start

private theorem foldl_binary_pointwise_congr (xs : List Nat)
    (f g : Nat → Nat → Nat)
    (h : ∀ acc x, x ∈ xs → f acc x = g acc x) (acc : Nat) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [h acc x (by simp)]
    apply ih
    intro a y hy
    exact h a y (by simp [hy])

private theorem foldl_add_pointwise_congr (xs : List Nat)
    (f g : Nat → Nat) (h : ∀ x, x ∈ xs → f x = g x) (acc : Nat) :
    xs.foldl (fun a x => a + f x) acc =
      xs.foldl (fun a x => a + g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [h x (by simp)]
    apply ih
    intro y hy
    exact h y (by simp [hy])

/-- A completed path payload has exactly the referenced target
configuration's group ID. -/
theorem comparisonSignalID_eq_groupID_of_bits_match_config
    {ψ n : Nat} (ring : DirectedRing n)
    (signalC targetC : Fin n → AgentState ψ) (start : Fin n)
    (h : comparisonBitsMatchConfigAt ring signalC targetC start) :
    comparisonSignalIDAt ring signalC start = groupID ring.hn targetC start := by
  unfold comparisonSignalIDAt groupID
  apply foldl_add_pointwise_congr
  intro k hk
  have hlt : k < ψ := List.mem_range.mp hk
  obtain ⟨label, bit, hpath, _, hbit⟩ := h k hlt
  unfold comparisonPathBitAt
  rw [hpath, hbit]

/-- Source-authenticated complete path components encode exactly the source
configuration's group ID. -/
theorem comparisonSignalID_eq_groupID_of_bits_match_between
    {ψ n : Nat} (ring : DirectedRing n)
    (signalC sourceC : Fin n → AgentState ψ)
    (signalStart sourceStart : Fin n)
    (h : comparisonBitsMatchBetweenAt ring signalC sourceC
      signalStart sourceStart) :
    comparisonSignalIDAt ring signalC signalStart =
      groupID ring.hn sourceC sourceStart := by
  unfold comparisonSignalIDAt groupID
  apply foldl_add_pointwise_congr
  intro k hk
  have hlt : k < ψ := List.mem_range.mp hk
  obtain ⟨label, bit, hpath, _, hbit⟩ := h k hlt
  unfold comparisonPathBitAt
  rw [hpath, hbit]

/-- Same-configuration specialization. -/
theorem comparisonSignalID_eq_groupID_of_bits_match
    {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n)
    (h : comparisonBitsMatchAt ring C start) :
    comparisonSignalIDAt ring C start = groupID ring.hn C start :=
  comparisonSignalID_eq_groupID_of_bits_match_config ring C C start h

/-- Nonterminal runtime-field certificate for one complete comparison carrier.
The current path payload is tied to a stable source route; no CHECK result or
boundary-safety proposition is stored. `signalC` may be an intermediate
configuration while `referenceC` supplies the stable source/target group bits. -/
structure CompleteComparisonCarrier {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n) where
  route : StableSignalRoute ring referenceC leaderPos
  payload_at_target :
    comparisonSignalIDAt ring signalC
        (stableGroupStart ring leaderPos ψ route.target) = route.payload

namespace CompleteComparisonCarrier

/-- A complete carrier that has strictly left its source group cannot encode
its stable target group. -/
theorem signalID_ne_targetGroup {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn referenceC (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (carrier : CompleteComparisonCarrier ring signalC referenceC leaderPos)
    (hstrict : carrier.route.source < carrier.route.target) :
    comparisonSignalIDAt ring signalC
        (stableGroupStart ring leaderPos ψ carrier.route.target) ≠
      groupID ring.hn referenceC
        (stableGroupStart ring leaderPos ψ carrier.route.target) := by
  rw [carrier.payload_at_target]
  exact carrier.route.payload_ne_target
    ring referenceC leaderPos hgroups hstrict

/-- In particular, a coherent strictly advanced carrier cannot have all path
bits match the target configuration. This is the non-boundary theorem that
rules out the payload pattern used by T1. -/
theorem not_bits_match_target {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn referenceC (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (carrier : CompleteComparisonCarrier ring signalC referenceC leaderPos)
    (hstrict : carrier.route.source < carrier.route.target) :
    ¬comparisonBitsMatchConfigAt ring signalC referenceC
      (stableGroupStart ring leaderPos ψ carrier.route.target) := by
  intro hbits
  apply carrier.signalID_ne_targetGroup
    ring signalC referenceC leaderPos hgroups hstrict
  exact comparisonSignalID_eq_groupID_of_bits_match_config
    ring signalC referenceC
      (stableGroupStart ring leaderPos ψ carrier.route.target) hbits

end CompleteComparisonCarrier

/-- Lower-level complete carrier certificate: every runtime path component at
the current target is authenticated against the corresponding bit of the
route's stable source group. -/
structure SourceTaggedCompleteComparisonCarrier {ψ n : Nat}
    (ring : DirectedRing n) (signalC referenceC : Fin n → AgentState ψ)
    (leaderPos : Fin n) where
  route : StableSignalRoute ring referenceC leaderPos
  components : comparisonBitsMatchBetweenAt ring signalC referenceC
    (stableGroupStart ring leaderPos ψ route.target)
    (stableGroupStart ring leaderPos ψ route.source)

namespace SourceTaggedCompleteComparisonCarrier

/-- Source-tagged components provide the payload equality required by the
higher-level complete-carrier interface. -/
def toCompleteComparisonCarrier {ψ n : Nat} {ring : DirectedRing n}
    {signalC referenceC : Fin n → AgentState ψ} {leaderPos : Fin n}
    (carrier : SourceTaggedCompleteComparisonCarrier
      ring signalC referenceC leaderPos) :
    CompleteComparisonCarrier ring signalC referenceC leaderPos where
  route := carrier.route
  payload_at_target := by
    calc
      comparisonSignalIDAt ring signalC
          (stableGroupStart ring leaderPos ψ carrier.route.target) =
        groupID ring.hn referenceC
          (stableGroupStart ring leaderPos ψ carrier.route.source) :=
        comparisonSignalID_eq_groupID_of_bits_match_between
          ring signalC referenceC
          (stableGroupStart ring leaderPos ψ carrier.route.target)
          (stableGroupStart ring leaderPos ψ carrier.route.source)
          carrier.components
      _ = carrier.route.payload := carrier.route.payload_from_source.symm

/-- A strict source-tagged carrier cannot match its target bits. -/
theorem not_bits_match_target {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn referenceC (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (carrier : SourceTaggedCompleteComparisonCarrier
      ring signalC referenceC leaderPos)
    (hstrict : carrier.route.source < carrier.route.target) :
    ¬comparisonBitsMatchConfigAt ring signalC referenceC
      (stableGroupStart ring leaderPos ψ carrier.route.target) :=
  carrier.toCompleteComparisonCarrier.not_bits_match_target
    ring signalC referenceC leaderPos hgroups hstrict

end SourceTaggedCompleteComparisonCarrier

/-- Prefix form of source authentication. Only offsets through `upto` are
required to carry bits from `sourceStart`. -/
def comparisonPrefixBitsMatchBetweenAt {ψ n : Nat}
    (ring : DirectedRing n) (signalC sourceC : Fin n → AgentState ψ)
    (signalStart sourceStart : Fin n) (upto : Nat) : Prop :=
  ∀ k : Nat, k ≤ upto →
    ∃ label bit,
      (signalC (groupOffset ring signalStart k)).path = .some label bit ∧
      label = k ∧
      bit = if (sourceC (groupOffset ring sourceStart k)).bit then 1 else 0

/-- Prefix form of comparison against the current target bits. -/
def comparisonPrefixBitsMatchConfigAt {ψ n : Nat}
    (ring : DirectedRing n) (signalC targetC : Fin n → AgentState ψ)
    (start : Fin n) (upto : Nat) : Prop :=
  comparisonPrefixBitsMatchBetweenAt ring signalC targetC start start upto

/-- Runtime certificate for an `.equal` CHECK prefix. The same path components
are authenticated against one stable source route and are known equal to the
current target bits through `upto`. This is a lower-level object than a terminal
carrier or `CheckBoundarySafe`. -/
structure EqualPrefixCarrier {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n) where
  route : StableSignalRoute ring referenceC leaderPos
  upto : Nat
  upto_lt : upto < ψ
  source_components : comparisonPrefixBitsMatchBetweenAt
    ring signalC referenceC
    (stableGroupStart ring leaderPos ψ route.target)
    (stableGroupStart ring leaderPos ψ route.source) upto
  target_components : comparisonPrefixBitsMatchConfigAt
    ring signalC referenceC
    (stableGroupStart ring leaderPos ψ route.target) upto
  endpoint_equal :
    (signalC (groupOffset ring
      (stableGroupStart ring leaderPos ψ route.target) upto)).state = .equal

namespace EqualPrefixCarrier

/-- Base `.equal` prefix at offset zero, corresponding to a successful
`checkSigCheckL` bit comparison. -/
def zero {ψ n : Nat} (hψ : ψ > 0) {ring : DirectedRing n}
    {signalC referenceC : Fin n → AgentState ψ} {leaderPos : Fin n}
    (route : StableSignalRoute ring referenceC leaderPos)
    (hsource : ∃ label bit,
      (signalC (groupOffset ring
        (stableGroupStart ring leaderPos ψ route.target) 0)).path =
          .some label bit ∧
      label = 0 ∧
      bit = if (referenceC (groupOffset ring
        (stableGroupStart ring leaderPos ψ route.source) 0)).bit then 1 else 0)
    (htarget : ∃ label bit,
      (signalC (groupOffset ring
        (stableGroupStart ring leaderPos ψ route.target) 0)).path =
          .some label bit ∧
      label = 0 ∧
      bit = if (referenceC (groupOffset ring
        (stableGroupStart ring leaderPos ψ route.target) 0)).bit then 1 else 0)
    (hequal : (signalC (groupOffset ring
      (stableGroupStart ring leaderPos ψ route.target) 0)).state = .equal) :
    EqualPrefixCarrier ring signalC referenceC leaderPos where
  route := route
  upto := 0
  upto_lt := hψ
  source_components k hk := by
    have hk0 : k = 0 := by omega
    subst k
    exact hsource
  target_components k hk := by
    have hk0 : k = 0 := by omega
    subst k
    exact htarget
  endpoint_equal := hequal

/-- Extend one equal prefix by the next adjacent path component, mirroring a
successful `checkSigCheckR` bit comparison. The old and new components must
carry the same route because the route is fixed in the result. -/
def extend {ψ n : Nat} {ring : DirectedRing n}
    {signalC referenceC : Fin n → AgentState ψ} {leaderPos : Fin n}
    (carrier : EqualPrefixCarrier ring signalC referenceC leaderPos)
    (hnext : carrier.upto + 1 < ψ)
    (hsourceNext : ∃ label bit,
      (signalC (groupOffset ring
        (stableGroupStart ring leaderPos ψ carrier.route.target)
        (carrier.upto + 1))).path = .some label bit ∧
      label = carrier.upto + 1 ∧
      bit = if (referenceC (groupOffset ring
        (stableGroupStart ring leaderPos ψ carrier.route.source)
        (carrier.upto + 1))).bit then 1 else 0)
    (htargetNext : ∃ label bit,
      (signalC (groupOffset ring
        (stableGroupStart ring leaderPos ψ carrier.route.target)
        (carrier.upto + 1))).path = .some label bit ∧
      label = carrier.upto + 1 ∧
      bit = if (referenceC (groupOffset ring
        (stableGroupStart ring leaderPos ψ carrier.route.target)
        (carrier.upto + 1))).bit then 1 else 0)
    (hequal : (signalC (groupOffset ring
      (stableGroupStart ring leaderPos ψ carrier.route.target)
      (carrier.upto + 1))).state = .equal) :
    EqualPrefixCarrier ring signalC referenceC leaderPos where
  route := carrier.route
  upto := carrier.upto + 1
  upto_lt := hnext
  source_components k hk := by
    by_cases hold : k ≤ carrier.upto
    · exact carrier.source_components k hold
    · have hkeq : k = carrier.upto + 1 := by omega
      subst k
      exact hsourceNext
  target_components k hk := by
    by_cases hold : k ≤ carrier.upto
    · exact carrier.target_components k hold
    · have hkeq : k = carrier.upto + 1 := by omega
      subst k
      exact htargetNext
  endpoint_equal := hequal

/-- A prefix through the terminal offset contains every source-tagged path
component and therefore becomes a complete source-tagged carrier. -/
def toSourceTaggedComplete {ψ n : Nat} {ring : DirectedRing n}
    {signalC referenceC : Fin n → AgentState ψ} {leaderPos : Fin n}
    (carrier : EqualPrefixCarrier ring signalC referenceC leaderPos)
    (hterminal : carrier.upto = ψ - 1) :
    SourceTaggedCompleteComparisonCarrier ring signalC referenceC leaderPos where
  route := carrier.route
  components k hk := by
    apply carrier.source_components k
    omega

/-- A terminal prefix also has all current path bits equal to the target group
bits. -/
theorem terminal_bits_match_target {ψ n : Nat}
    {ring : DirectedRing n}
    {signalC referenceC : Fin n → AgentState ψ} {leaderPos : Fin n}
    (carrier : EqualPrefixCarrier ring signalC referenceC leaderPos)
    (hterminal : carrier.upto = ψ - 1) :
    comparisonBitsMatchConfigAt ring signalC referenceC
      (stableGroupStart ring leaderPos ψ carrier.route.target) := by
  intro k hk
  apply carrier.target_components k
  omega

/-- A strict stable route cannot support an equal prefix through the terminal
bit. This is the local CHECK contradiction derived from source tags. -/
theorem not_terminal_of_strict_route {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn referenceC (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (carrier : EqualPrefixCarrier ring signalC referenceC leaderPos)
    (hterminal : carrier.upto = ψ - 1)
    (hstrict : carrier.route.source < carrier.route.target) : False := by
  exact carrier.toSourceTaggedComplete hterminal |>.not_bits_match_target
    ring signalC referenceC leaderPos hgroups hstrict
    (carrier.terminal_bits_match_target hterminal)

end EqualPrefixCarrier

/-! ## Source tagging for overwriting carriers -/

/-- Complete path3 payload at `signalStart`, authenticated against the bits at
`sourceStart` and carrying one shared write flag. -/
def overwritingBitsMatchBetweenAt {ψ n : Nat} (ring : DirectedRing n)
    (signalC sourceC : Fin n → AgentState ψ)
    (signalStart sourceStart : Fin n) (flag : Nat) : Prop :=
  flag ≤ 1 ∧ ∀ k : Nat, k < ψ →
    ∃ p : Path3Info,
      (signalC (groupOffset ring signalStart k)).path3 = some p ∧
      p.label = k ∧
      p.bit = (if (sourceC (groupOffset ring sourceStart k)).bit then 1 else 0) ∧
      p.flag = flag

/-- A source-tagged complete overwriting path carries exactly the source group
ID, independently of its current target group. -/
theorem overwritingSignalID_eq_groupID_of_bits_match_between
    {ψ n : Nat} (ring : DirectedRing n)
    (signalC sourceC : Fin n → AgentState ψ)
    (signalStart sourceStart : Fin n) (flag : Nat)
    (h : overwritingBitsMatchBetweenAt ring signalC sourceC
      signalStart sourceStart flag) :
    overwritingSignalIDAt ring signalC signalStart =
      groupID ring.hn sourceC sourceStart := by
  unfold overwritingSignalIDAt groupID
  calc
    (List.range ψ).foldl (fun acc k =>
        match (signalC (groupOffset ring signalStart k)).path3 with
        | some p => acc + p.bit * 2 ^ (ψ - 1 - k)
        | none => acc) 0 =
      (List.range ψ).foldl (fun acc k => acc +
        (match (signalC (groupOffset ring signalStart k)).path3 with
         | some p => p.bit * 2 ^ (ψ - 1 - k)
         | none => 0)) 0 := by
      apply foldl_binary_pointwise_congr
      intro acc k hk
      cases hp : (signalC (groupOffset ring signalStart k)).path3 <;> simp
    _ = (List.range ψ).foldl (fun acc k => acc +
        (if (sourceC (groupOffset ring sourceStart k)).bit then 1 else 0) *
          2 ^ (ψ - 1 - k)) 0 := by
      apply foldl_add_pointwise_congr
      intro k hk
      have hlt : k < ψ := List.mem_range.mp hk
      obtain ⟨p, hpath, _, hbit, _⟩ := h.2 k hlt
      rw [hpath]
      change p.bit * 2 ^ (ψ - 1 - k) = _
      rw [hbit]

/-- Current location and stable source of one overwriting carrier. No free-
signal or group-ID boundary conclusion is stored. -/
structure OverwritingCarrierRoute {ψ n : Nat} (ring : DirectedRing n)
    (referenceC : Fin n → AgentState ψ) (leaderPos : Fin n) where
  source : Nat
  target : Nat
  payload : Nat
  source_in_range : source < n / ψ
  target_in_range : target < n / ψ
  payload_from_source :
    payload = groupID ring.hn referenceC
      (stableGroupStart ring leaderPos ψ source)

/-- Complete runtime path3 carrier tied componentwise to its source route. -/
structure SourceTaggedCompleteOverwritingCarrier {ψ n : Nat}
    (ring : DirectedRing n) (signalC referenceC : Fin n → AgentState ψ)
    (leaderPos : Fin n) where
  route : OverwritingCarrierRoute ring referenceC leaderPos
  flag : Nat
  components : overwritingBitsMatchBetweenAt ring signalC referenceC
    (stableGroupStart ring leaderPos ψ route.target)
    (stableGroupStart ring leaderPos ψ route.source) flag

namespace SourceTaggedCompleteOverwritingCarrier

/-- The runtime carrier ID equals its authenticated route payload. -/
theorem signalID_eq_payload {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring signalC referenceC leaderPos) :
    overwritingSignalIDAt ring signalC
      (stableGroupStart ring leaderPos ψ carrier.route.target) =
        carrier.route.payload := by
  calc
    overwritingSignalIDAt ring signalC
        (stableGroupStart ring leaderPos ψ carrier.route.target) =
      groupID ring.hn referenceC
        (stableGroupStart ring leaderPos ψ carrier.route.source) :=
      overwritingSignalID_eq_groupID_of_bits_match_between
        ring signalC referenceC
        (stableGroupStart ring leaderPos ψ carrier.route.target)
        (stableGroupStart ring leaderPos ψ carrier.route.source)
        carrier.flag carrier.components
    _ = carrier.route.payload := carrier.route.payload_from_source.symm

end SourceTaggedCompleteOverwritingCarrier

/-! ## Ruler-certified overwriting carriers -/

/-- A complete source-tagged writer whose control flag equals the ruler
automaton state immediately before its current target group. This is a static
history certificate; transition preservation is a separate obligation. -/
structure RulerOverwritingHistory {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring C C leaderPos) : Prop where
  target_pos : 0 < carrier.route.target
  flag_before_target : carrier.flag =
    if rulerWriterFlagBefore carrier.route.payload carrier.route.target
      then 1 else 0

namespace RulerOverwritingHistory

/-- The certified flag update after processing the current group is exactly
the ruler automaton state before the next group. -/
theorem flag_after_target {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring C C leaderPos)
    (history : RulerOverwritingHistory ring C leaderPos carrier) :
    (if carrier.route.payload ≤ trailingZeros carrier.route.target then
        1 - carrier.flag else carrier.flag) =
      if rulerWriterFlagBefore carrier.route.payload
          (carrier.route.target + 1) then 1 else 0 := by
  rw [history.flag_before_target,
    rulerWriterFlagBefore_succ _ _ history.target_pos]
  by_cases hle : carrier.route.payload ≤
      trailingZeros carrier.route.target
  · simp only [if_pos hle]
    cases hflag : rulerWriterFlagBefore carrier.route.payload
        carrier.route.target <;> simp
  · simp only [if_neg hle]

/-- One-group transport of the ruler certificate.  A physical transition need
only prove payload preservation, target advancement, and the repaired local
flag update to instantiate this theorem. -/
theorem advance {ψ n : Nat} (ring : DirectedRing n)
    (C D : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring C C leaderPos)
    (next : SourceTaggedCompleteOverwritingCarrier
      ring D D leaderPos)
    (history : RulerOverwritingHistory ring C leaderPos carrier)
    (hpayload : next.route.payload = carrier.route.payload)
    (htarget : next.route.target = carrier.route.target + 1)
    (hflag : next.flag =
      if carrier.route.payload ≤ trailingZeros carrier.route.target then
        1 - carrier.flag else carrier.flag) :
    RulerOverwritingHistory ring D leaderPos next := by
  refine ⟨?_, ?_⟩
  · rw [htarget]
    omega
  · rw [hflag, hpayload, htarget]
    exact history.flag_after_target ring C leaderPos carrier

end RulerOverwritingHistory

/-- A source-tagged writer that follows the ruler flag automaton cannot be free
at its current target. The contradiction is exact: a target ID larger than the
payload forces the certified flag to zero, while free status requires every
component flag to be one. -/
theorem sourceTaggedOverwriting_not_free_of_ruler_history
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn C (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring C C leaderPos)
    (history : RulerOverwritingHistory ring C leaderPos carrier) :
    ¬isFreeOverwritingSignalAt ring C leaderPos carrier.route.target := by
  intro hfree
  change
    isAlignedOverwritingSignalAt ring C
        (stableGroupStart ring leaderPos ψ carrier.route.target) 1 ∧
      overwritingSignalIDAt ring C
          (stableGroupStart ring leaderPos ψ carrier.route.target) ≠
        trailingZeros carrier.route.target ∧
      groupID ring.hn C
          (stableGroupStart ring leaderPos ψ carrier.route.target) >
        overwritingSignalIDAt ring C
          (stableGroupStart ring leaderPos ψ carrier.route.target)
    at hfree
  have hsignal := carrier.signalID_eq_payload ring C C leaderPos
  have htarget := hgroups carrier.route.target history.target_pos
    carrier.route.target_in_range
  have hgreater : carrier.route.payload <
      trailingZeros carrier.route.target := by
    rw [← htarget, ← hsignal]
    exact hfree.2.2
  have hflagFalse := rulerWriterFlagBefore_false_of_payload_lt_target
    carrier.route.target carrier.route.payload history.target_pos hgreater
  have hcarrierZero : carrier.flag = 0 := by
    simpa [hflagFalse] using history.flag_before_target
  obtain ⟨pFree, hpFree, _, _, hpFreeFlag⟩ :=
    hfree.1.2 0 hψ
  obtain ⟨pCarrier, hpCarrier, _, _, hpCarrierFlag⟩ :=
    carrier.components.2 0 hψ
  rw [hpCarrier] at hpFree
  cases hpFree
  have hcarrierOne : carrier.flag = 1 := by omega
  omega

/-- Every complete flag-one writer at a positive group is backed by one
source-tagged ruler history. Partial and flag-zero paths need no certificate
because they are not free by definition. -/
def AllFlagOneOverwritingRulerCertified
    {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n) : Prop :=
  ∀ i : Nat, i > 0 → i < n / ψ →
    isAlignedOverwritingSignalAt ring C
      (stableGroupStart ring leaderPos ψ i) 1 →
    ∃ carrier : SourceTaggedCompleteOverwritingCarrier
        ring C C leaderPos,
      carrier.route.target = i ∧
        RulerOverwritingHistory ring C leaderPos carrier

/-- **Condition-4 kernel.** Stable ruler IDs plus source/flag history for every
complete flag-one overwriting carrier imply Wu's no-free-signal condition. -/
theorem noFreeOverwritingSignal_of_ruler_certified
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n)
    (hleader : (C leaderPos).isLeader)
    (hlabel : (C leaderPos).label = ⟨0, hψ⟩)
    (hgroups : ∀ i : Nat, i > 0 → i < n / ψ →
      groupID ring.hn C (stableGroupStart ring leaderPos ψ i) =
        trailingZeros i)
    (hcert : AllFlagOneOverwritingRulerCertified ring C leaderPos) :
    noFreeOverwritingSignal hψ ring C := by
  refine ⟨leaderPos, hleader, hlabel, ?_⟩
  intro i hi hbound hfree
  change
    isAlignedOverwritingSignalAt ring C
        (stableGroupStart ring leaderPos ψ i) 1 ∧
      overwritingSignalIDAt ring C
          (stableGroupStart ring leaderPos ψ i) ≠ trailingZeros i ∧
      groupID ring.hn C (stableGroupStart ring leaderPos ψ i) >
        overwritingSignalIDAt ring C
          (stableGroupStart ring leaderPos ψ i)
    at hfree
  obtain ⟨carrier, htarget, history⟩ :=
    hcert i hi hbound hfree.1
  subst i
  exact sourceTaggedOverwriting_not_free_of_ruler_history
    hψ ring C leaderPos hgroups carrier history hfree

/-! ## Concrete CHECK-boundary obligation

The ghost history is not yet attached to every path field. The following
predicate records the exact concrete consequence required at Algorithm 11: no
edge may finish CHECK in the terminal equal state. Unlike a vague
`no active signal` condition, it is stated at the named intermediate boundary
that `ppll` actually inspects.
-/

open PPLL

/-- A successful bit comparison exposes equality between the path bit and the
agent's Boolean bit. -/
theorem checkBit_signal_eq_of_equal {agentBit : Bool} {signalBit : Nat}
    (h : checkBit agentBit signalBit = MainState.equal) :
    signalBit = if agentBit then 1 else 0 := by
  let bitNat := if agentBit then 1 else 0
  change (if bitNat = signalBit then MainState.equal
    else if bitNat > signalBit then MainState.larger else MainState.less) =
      MainState.equal at h
  by_cases heq : bitNat = signalBit
  · exact heq.symm
  · rw [if_neg heq] at h
    split at h <;> contradiction

/-- If `checkSigCheckL` newly creates `.equal`, the exact offset-zero path,
ready-state, label, and target-bit facts are present. -/
theorem checkSigCheckL_new_equal_fields {ψ : Nat} (hψ : ψ > 0)
    (u : AgentState ψ)
    (hnew : (checkSigCheckL hψ u).state = .equal)
    (hold : u.state ≠ .equal) :
    ∃ pathBit,
      u.path = .some 0 pathBit ∧
      u.label = ⟨0, hψ⟩ ∧
      u.state = .CHECK_ready ∧
      pathBit = if u.bit then 1 else 0 := by
  cases hp : u.path with
  | bot =>
    simp [checkSigCheckL, hp] at hnew
    exact (hold hnew).elim
  | some label bit =>
    by_cases hlabel : label = 0
    · subst label
      by_cases hg : u.label = ⟨0, hψ⟩ ∧ u.state = .CHECK_ready
      · refine ⟨bit, rfl, hg.1, hg.2, ?_⟩
        apply checkBit_signal_eq_of_equal
        simpa [checkSigCheckL, hp, hg] using hnew
      · simp [checkSigCheckL, hp, hg] at hnew
        exact (hold hnew).elim
    · simp [checkSigCheckL, hp, hlabel] at hnew
      exact (hold hnew).elim

/-- If `checkSigCheckR` newly creates `.equal`, it extends an equal predecessor
with one ready path component whose bit equals the responder's target bit. -/
theorem checkSigCheckR_new_equal_fields {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hnew : (checkSigCheckR hψ l r).state = .equal)
    (hold : r.state ≠ .equal) :
    ∃ label pathBit,
      r.path = .some label pathBit ∧
      l.label.val < ψ - 1 ∧
      l.state = .equal ∧
      r.state = .CHECK_ready ∧
      pathBit = if r.bit then 1 else 0 := by
  cases hp : r.path with
  | bot =>
    simp [checkSigCheckR, hp] at hnew
    exact (hold hnew).elim
  | some label pathBit =>
    by_cases hg : l.label.val < ψ - 1 ∧ l.state = .equal
    · by_cases hr : r.state = .CHECK_ready
      · refine ⟨label, pathBit, rfl, hg.1, hg.2, hr, ?_⟩
        apply checkBit_signal_eq_of_equal
        simpa [checkSigCheckR, hp, hg, hr] using hnew
      · simp [checkSigCheckR, hp, hg, hr] at hnew
        exact (hold hnew).elim
    · simp [checkSigCheckR, hp, hg] at hnew
      exact (hold hnew).elim

/-- Exact one-step comparison obligation at CHECK boundaries. This is a target
for the eventual field-level `SignalCoherent` invariant, not claimed to be
preserved yet. -/
def CheckBoundarySafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ e : Fin n,
    let q := ppllAfterCheck hψ κ (C e) (C (ring.rightNeighbor e))
    ¬(q.2.label = ⟨ψ - 1, by omega⟩ ∧ q.2.state = .equal)

/-- Intermediate refinement interface: every terminal equality produced at a
CHECK boundary must be explained by a concretely sourced stable-signal history
whose payload equals its target group. The ruler theorem proves that such an
explanation is impossible. Future work must derive this certificate from
`path/state/path2` evolution rather than assume it. -/
structure CheckHistoryCertified {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) where
  leaderPos : Fin n
  groupIDs : ∀ i : Nat, i > 0 → i < n / ψ →
    groupID ring.hn C (stableGroupStart ring leaderPos ψ i) = trailingZeros i
  terminal_history : ∀ e : Fin n,
    let q := ppllAfterCheck hψ κ (C e) (C (ring.rightNeighbor e))
    q.2.label = ⟨ψ - 1, by omega⟩ ∧ q.2.state = .equal →
      ∃ history : StableSignalHistory ring C leaderPos,
        history.payload = groupID ring.hn C
          (stableGroupStart ring leaderPos ψ history.target)

/-- A certified stable traversal history discharges the exact CHECK-boundary
obligation used by the concrete leader-preservation theorem. -/
theorem CheckHistoryCertified.toCheckBoundarySafe
    {ψ n : Nat} {hψ : ψ > 0} {κ : Nat}
    {ring : DirectedRing n} {C : Fin n → AgentState ψ}
    (h : CheckHistoryCertified hψ κ ring C) :
    CheckBoundarySafe hψ κ ring C := by
  intro e
  dsimp only
  intro hterminal
  obtain ⟨history, hequal⟩ := h.terminal_history e hterminal
  exact (history.payload_ne_target ring C h.leaderPos h.groupIDs hequal).elim

/-- Wu's no-free-barrier condition plus the concrete CHECK-boundary obligation
blocks every responder-side leader creation in a complete P_PLL interaction. -/
theorem no_new_responder_of_noFreeBarrier_checkBoundary
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hbarriers : noFreeBarrier hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (e : Fin n)
    (hfollower : (C (ring.rightNeighbor e)).leader = false) :
    (ppll hψ κ (C e) (C (ring.rightNeighbor e))).2.leader ≠ true := by
  intro hnew
  rcases PPLLVerify.ppll_new_responder_leader_requires_barrier_or_check
      hψ κ (C e) (C (ring.rightNeighbor e)) hnew hfollower with
    hprobeBarrier | hterminal
  · have hleader := hbarriers e hprobeBarrier.2
    simp [AgentState.isLeader, hfollower] at hleader
  · exact hcheck e hterminal

/-- Every leader in the output-relevant safety kernel has label zero.  The
historical name is retained for downstream API compatibility; PaperSafe proofs
coerce to `OutputSafeConfig`. -/
theorem paperSafe_unique_leader_label_zero
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (lp : Fin n) (hlp : (C lp).isLeader) :
    (C lp).label = ⟨0, hψ⟩ :=
  hSafe.leader_label_zero lp hlp

/-- In a paper-safe configuration, both endpoint labels are preserved by a
concrete P_PLL interaction. A non-barrier responder is unchanged; a barrier
responder is the unique label-zero leader and is also unchanged. -/
theorem ppll_local_labels_preserved_of_paperSafe
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C) (e : Fin n) :
    (ppll hψ κ (C e) (C (ring.rightNeighbor e))).1.label = (C e).label ∧
    (ppll hψ κ (C e) (C (ring.rightNeighbor e))).2.label =
      (C (ring.rightNeighbor e)).label := by
  constructor
  · exact PPLLVerify.ppll_initiator_label_stable hψ κ _ _
  · by_cases hb : isBarrier hψ (C e) (C (ring.rightNeighbor e))
    · have hrProp := hSafe.no_free_barrier e hb
      have hr : (C (ring.rightNeighbor e)).leader = true := by
        simpa [AgentState.isLeader] using hrProp
      have hrLabel := paperSafe_unique_leader_label_zero
        hψ ring C hSafe (ring.rightNeighbor e) hrProp
      exact PPLLVerify.ppll_responder_label_stable_of_leader_zero
        hψ κ _ _ hr hrLabel
    · exact PPLLVerify.ppll_responder_label_stable_of_nonbarrier
        hψ κ _ _ hb

/-- Under the same two assumptions, every output leader of the interacting
pair comes from an input leader. The initiator may receive a migrated responder
leader, so its conclusion is a disjunction; the responder cannot receive such a
migration. -/
theorem ppll_local_leaders_have_input_origin
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hbarriers : noFreeBarrier hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (e : Fin n) :
    ((ppll hψ κ (C e) (C (ring.rightNeighbor e))).1.leader = true →
      (C e).leader = true ∨ (C (ring.rightNeighbor e)).leader = true) ∧
    ((ppll hψ κ (C e) (C (ring.rightNeighbor e))).2.leader = true →
      (C (ring.rightNeighbor e)).leader = true) := by
  constructor
  · intro hleft
    rcases PPLLVerify.ppll_initiator_leader_has_origin hψ κ
        (C e) (C (ring.rightNeighbor e)) hleft with
      hOldLeft | hOldRight | hprobeBarrier | hterminal
    · exact .inl hOldLeft
    · exact .inr hOldRight
    · right
      have hleader := hbarriers e hprobeBarrier.2
      simpa [AgentState.isLeader] using hleader
    · exact (hcheck e hterminal).elim
  · intro hright
    by_cases hold : (C (ring.rightNeighbor e)).leader = true
    · exact hold
    · have holdFalse : (C (ring.rightNeighbor e)).leader = false := by
        cases h : (C (ring.rightNeighbor e)).leader
        · rfl
        · exact (hold h).elim
      exact (no_new_responder_of_noFreeBarrier_checkBoundary
        hψ κ ring C hbarriers hcheck e holdFalse hright).elim

/-- Update exactly two positions by an already computed transition pair. -/
def updatePair {ψ n : Nat} (C : Fin n → AgentState ψ)
    (i j : Fin n) (q : AgentState ψ × AgentState ψ) :
    Fin n → AgentState ψ :=
  fun k => if k = i then q.1 else if k = j then q.2 else C k

/-- One concrete P_PLL configuration step, named without packaging through the
existential state type of `PopulationProtocol`. -/
def ppllStep {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (e : Fin n) :
    Fin n → AgentState ψ :=
  updatePair C e (ring.rightNeighbor e)
    (ppll hψ κ (C e) (C (ring.rightNeighbor e)))

/-- The specialized configuration update is exactly the step of the packaged
concrete protocol. -/
theorem ppllStep_eq_protocol_step {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (e : Fin n) :
    ppllStep hψ κ ring C e = (PPLL.protocol hψ κ).step ring C e := by
  rfl

@[simp] theorem updatePair_initiator {ψ n : Nat}
    (C : Fin n → AgentState ψ) (i j : Fin n)
    (q : AgentState ψ × AgentState ψ) :
    updatePair C i j q i = q.1 := by
  simp [updatePair]

@[simp] theorem updatePair_responder {ψ n : Nat}
    (C : Fin n → AgentState ψ) (i j : Fin n)
    (q : AgentState ψ × AgentState ψ) (hne : j ≠ i) :
    updatePair C i j q j = q.2 := by
  simp [updatePair, hne]

@[simp] theorem updatePair_other {ψ n : Nat}
    (C : Fin n → AgentState ψ) (i j k : Fin n)
    (q : AgentState ψ × AgentState ψ) (hki : k ≠ i) (hkj : k ≠ j) :
    updatePair C i j q k = C k := by
  simp [updatePair, hki, hkj]

/-- Clockwise offset and containing group index relative to a leader
witness. -/
def clockwiseOffset {n : Nat} (leaderPos pos : Fin n) : Nat :=
  (pos.val + n - leaderPos.val) % n

def containingGroupIndex {n : Nat} (leaderPos pos : Fin n) (ψ : Nat) : Nat :=
  clockwiseOffset leaderPos pos / ψ

/-- Configuration-level assignment of complete runtime comparison carriers to
stable target groups. The assignment exists independently of CHECK. A terminal
CHECK must select one assigned carrier, prove that it strictly left its source,
and expose target-matching bits. This separates carrier provenance from the
boundary conclusion and makes malformed/fused carriers falsifiable. -/
structure AssignedComparisonProvenance {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (signalC referenceC : Fin n → AgentState ψ) where
  leaderPos : Fin n
  groupIDs : ∀ i : Nat, i > 0 → i < n / ψ →
    groupID ring.hn referenceC (stableGroupStart ring leaderPos ψ i) =
      trailingZeros i
  routeFor : ∀ i : Nat, i > 0 → i < n / ψ →
    Option {route : StableSignalRoute ring referenceC leaderPos //
      route.target = i}
  assigned_payload : ∀ (i : Nat) (hi : i > 0) (hirange : i < n / ψ)
      (route : {route : StableSignalRoute ring referenceC leaderPos //
        route.target = i}),
    routeFor i hi hirange = some route →
      comparisonSignalIDAt ring signalC
        (stableGroupStart ring leaderPos ψ i) = route.val.payload
  terminal_uses_carrier : ∀ e : Fin n,
    let q := ppllAfterCheck hψ κ (referenceC e)
      (referenceC (ring.rightNeighbor e))
    q.2.label = ⟨ψ - 1, by omega⟩ ∧ q.2.state = .equal →
      let target := containingGroupIndex leaderPos (ring.rightNeighbor e) ψ
      ∃ (htpos : target > 0) (htrange : target < n / ψ)
        (route : {route : StableSignalRoute ring referenceC leaderPos //
          route.target = target}),
        routeFor target htpos htrange = some route ∧
        route.val.source < route.val.target ∧
        comparisonBitsMatchConfigAt ring signalC referenceC
          (stableGroupStart ring leaderPos ψ target)

namespace AssignedComparisonProvenance

/-- Assigned, strictly advanced runtime carriers rule out every terminal CHECK
match. The proof uses no stored `CheckBoundarySafe` proposition. -/
theorem toCheckBoundarySafe
    {ψ n : Nat} {hψ : ψ > 0} {κ : Nat}
    {ring : DirectedRing n} {signalC referenceC : Fin n → AgentState ψ}
    (h : AssignedComparisonProvenance hψ κ ring signalC referenceC) :
    CheckBoundarySafe hψ κ ring referenceC := by
  intro e
  dsimp only
  intro hterminal
  obtain ⟨htpos, htrange, route, hassigned, hstrict, hbits⟩ :=
    h.terminal_uses_carrier e hterminal
  let target := containingGroupIndex h.leaderPos (ring.rightNeighbor e) ψ
  have hpayload := h.assigned_payload target htpos htrange route hassigned
  have hne := route.val.payload_ne_target ring referenceC h.leaderPos
    h.groupIDs hstrict
  apply hne
  calc
    route.val.payload = comparisonSignalIDAt ring signalC
        (stableGroupStart ring h.leaderPos ψ target) := hpayload.symm
    _ = groupID ring.hn referenceC
        (stableGroupStart ring h.leaderPos ψ target) :=
      comparisonSignalID_eq_groupID_of_bits_match_config
        ring signalC referenceC
          (stableGroupStart ring h.leaderPos ψ target) hbits
    _ = groupID ring.hn referenceC
        (stableGroupStart ring h.leaderPos ψ route.val.target) := by
      rw [route.property]

end AssignedComparisonProvenance

/-- Configuration at the exact intermediate boundary after CHECK on edge `e`. -/
def afterCheckStep {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (e : Fin n) :
    Fin n → AgentState ψ :=
  updatePair C e (ring.rightNeighbor e)
    (ppllAfterCheck hψ κ (C e) (C (ring.rightNeighbor e)))

/-- A nontrivial directed ring has distinct interaction endpoints. -/
theorem rightNeighbor_ne_self_of_one_lt {n : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  apply Fin.ne_of_val_ne
  unfold DirectedRing.rightNeighbor
  change (e.val + 1) % n ≠ e.val
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self]
    omega

/-- Nonterminal configuration invariant: every runtime `.equal` state is the
endpoint of a strict source-tagged equal prefix. This predicate does not refer
to CHECK boundaries. -/
structure EqualStateProvenance {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) where
  leaderPos : Fin n
  groupIDs : ∀ i : Nat, i > 0 → i < n / ψ →
    groupID ring.hn referenceC (stableGroupStart ring leaderPos ψ i) =
      trailingZeros i
  prefix_for_equal : ∀ pos : Fin n, (signalC pos).state = .equal →
    ∃ carrier : EqualPrefixCarrier ring signalC referenceC leaderPos,
      groupOffset ring
          (stableGroupStart ring leaderPos ψ carrier.route.target)
          carrier.upto = pos ∧
      carrier.upto = (signalC pos).label.val ∧
      carrier.route.source < carrier.route.target

namespace EqualStateProvenance

/-- If the post-CHECK intermediate configuration has equal-state provenance,
then that concrete CHECK interaction cannot finish equal at its terminal
responder. -/
theorem checkEdgeSafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : EqualStateProvenance ring (afterCheckStep hψ κ ring C e) C) :
    let q := ppllAfterCheck hψ κ (C e) (C (ring.rightNeighbor e))
    ¬(q.2.label = ⟨ψ - 1, by omega⟩ ∧ q.2.state = .equal) := by
  dsimp only
  intro hterminal
  let j := ring.rightNeighbor e
  have hne : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hstate : (afterCheckStep hψ κ ring C e j).state = .equal := by
    rw [afterCheckStep, updatePair_responder _ _ _ _ hne]
    exact hterminal.2
  obtain ⟨carrier, _, huptoLabel, hstrict⟩ :=
    h.prefix_for_equal j hstate
  have hlabel : (afterCheckStep hψ κ ring C e j).label =
      ⟨ψ - 1, by omega⟩ := by
    rw [afterCheckStep, updatePair_responder _ _ _ _ hne]
    exact hterminal.1
  have hupto : carrier.upto = ψ - 1 := by
    rw [huptoLabel, hlabel]
  exact carrier.not_terminal_of_strict_route ring
    (afterCheckStep hψ κ ring C e) C h.leaderPos h.groupIDs
    hupto hstrict

/-- Equal-state provenance after every possible CHECK prefix implies the exact
boundary predicate. -/
theorem toCheckBoundarySafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AgentState ψ)
    (h : ∀ e, EqualStateProvenance ring
      (afterCheckStep hψ κ ring C e) C) :
    CheckBoundarySafe hψ κ ring C := by
  intro e
  exact (h e).checkEdgeSafe hψ κ ring hn C e

end EqualStateProvenance

/-- Stronger, field-facing refinement interface for CHECK. A terminal result
must expose an aligned concrete path payload matching the pre-step target bits
and carry a stable traversal history for the target group inferred from the
responder's ring position. -/
structure FieldCheckHistoryCertified {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) where
  leaderPos : Fin n
  groupIDs : ∀ i : Nat, i > 0 → i < n / ψ →
    groupID ring.hn C (stableGroupStart ring leaderPos ψ i) = trailingZeros i
  terminal_fields : ∀ e : Fin n,
    let q := ppllAfterCheck hψ κ (C e) (C (ring.rightNeighbor e))
    q.2.label = ⟨ψ - 1, by omega⟩ ∧ q.2.state = .equal →
      let target := containingGroupIndex leaderPos (ring.rightNeighbor e) ψ
      let start := stableGroupStart ring leaderPos ψ target
      ∃ history : StableSignalHistory ring C leaderPos,
        history.target = target ∧
        history.payload =
          comparisonSignalIDAt ring (afterCheckStep hψ κ ring C e) start ∧
        comparisonBitsMatchConfigAt ring
          (afterCheckStep hψ κ ring C e) C start

/-- The field-facing certificate supplies the abstract history certificate. -/
def FieldCheckHistoryCertified.toCheckHistoryCertified
    {ψ n : Nat} {hψ : ψ > 0} {κ : Nat}
    {ring : DirectedRing n} {C : Fin n → AgentState ψ}
    (h : FieldCheckHistoryCertified hψ κ ring C) :
    CheckHistoryCertified hψ κ ring C where
  leaderPos := h.leaderPos
  groupIDs := h.groupIDs
  terminal_history e hterminal := by
    obtain ⟨history, htarget, hpayload, hbits⟩ :=
      h.terminal_fields e hterminal
    refine ⟨history, ?_⟩
    let target := containingGroupIndex h.leaderPos (ring.rightNeighbor e) ψ
    let start := stableGroupStart ring h.leaderPos ψ target
    have hid := comparisonSignalID_eq_groupID_of_bits_match_config
      ring (afterCheckStep hψ κ ring C e) C start hbits
    rw [htarget]
    exact hpayload.trans hid

/-- A concrete field/history certificate rules out terminal CHECK equality. -/
theorem FieldCheckHistoryCertified.toCheckBoundarySafe
    {ψ n : Nat} {hψ : ψ > 0} {κ : Nat}
    {ring : DirectedRing n} {C : Fin n → AgentState ψ}
    (h : FieldCheckHistoryCertified hψ κ ring C) :
    CheckBoundarySafe hψ κ ring C :=
  h.toCheckHistoryCertified.toCheckBoundarySafe

/-- Exact one-step obligation for the overwriting subsystem: every group ID
is unchanged by the complete interaction. A future path3/write-history
invariant must imply this for non-free signals. -/
def GroupIDBoundarySafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ e start : Fin n,
    groupID ring.hn (ppllStep hψ κ ring C e) start =
      groupID ring.hn C start

/-- Exact remaining condition-2 obligation at each interaction boundary. -/
def BulletBoundarySafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ e : Fin n,
    noNonPeacefulBullet hψ ring (ppllStep hψ κ ring C e)

/-- Exact remaining condition-4 obligation at each interaction boundary. -/
def OverwritingBoundarySafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ e : Fin n,
    noFreeOverwritingSignal hψ ring (ppllStep hψ κ ring C e)

/-- Every position keeps its label in a concrete step from a paper-safe
configuration. -/
theorem ppllStep_labels_preserved_of_paperSafe
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C) (e k : Fin n) :
    (ppllStep hψ κ ring C e k).label = (C k).label := by
  have hlocal := ppll_local_labels_preserved_of_paperSafe
    hψ κ ring C hSafe e
  by_cases hke : k = e
  · subst k
    rw [ppllStep, updatePair_initiator]
    exact hlocal.1
  · by_cases hkj : k = ring.rightNeighbor e
    · have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact hke (hkj.trans h)
      rw [ppllStep, hkj, updatePair_responder _ _ _ _ hne]
      exact hlocal.2
    · rw [ppllStep, updatePair_other _ _ _ _ _ hke hkj]

/-- The existing unique leader survives one concrete P_PLL interaction. The
initiator case uses peacefulness of any incoming live bullet; the responder
case uses its stable label zero. -/
theorem ppllStep_unique_leader_survives
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (lp : Fin n) (hlp : (C lp).isLeader)
    (huniq : ∀ k, (C k).isLeader → k = lp)
    (e : Fin n) :
    (ppllStep hψ κ ring C e lp).leader = true := by
  let j := ring.rightNeighbor e
  by_cases hle : lp = e
  · subst lp
    have hleft : (ppll hψ κ (C e) (C j)).1.leader = true := by
      rcases PPLLVerify.ppll_leader_initiator_stable hψ κ (C e) (C j)
          hlp with hkeep | ⟨hbullet, hnoShield⟩
      · exact hkeep
      · exfalso
        obtain ⟨_, _, _, hmLeader, hmShield, _, _⟩ :=
          hSafe.no_nonpeaceful_bullet j hbullet
        have hmEq : _ = e := huniq _ hmLeader
        rw [hmEq] at hmShield
        have hmShieldTrue : (C e).shield = true := by
          simpa using hmShield
        have himpossible : false = true := hnoShield.symm.trans hmShieldTrue
        exact Bool.noConfusion himpossible
    rw [ppllStep, updatePair_initiator]
    simpa only [j] using hleft
  · by_cases hlj : lp = j
    · have hright : (ppll hψ κ (C e) (C j)).2.leader = true := by
        apply PPLLVerify.ppll_leader_responder_stable hψ κ (C e) (C j)
        · simpa [hlj, AgentState.isLeader] using hlp
        · simpa [hlj] using
            paperSafe_unique_leader_label_zero hψ ring C hSafe lp hlp
      have hne : j ≠ e := by
        intro hje
        exact hle (hlj.trans hje)
      rw [hlj, ppllStep, updatePair_responder _ _ _ _ hne]
      simpa only [j] using hright
    · rw [ppllStep, updatePair_other _ _ _ _ _ hle hlj]
      simpa [AgentState.isLeader] using hlp

/-- **Concrete condition-3 preservation.** Paper-safe configurations preserve
`noFreeBarrier` in one P_PLL step. Labels do not change, and every pre-existing
barrier remains blocked by the surviving unique leader. This theorem does not
need the CHECK-boundary assumption. -/
theorem noFreeBarrier_preserved_of_paperSafe
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C) (e : Fin n) :
    noFreeBarrier hψ ring (ppllStep hψ κ ring C e) := by
  obtain ⟨lp, hlp, huniq⟩ := hSafe.unique_leader
  intro i
  dsimp only
  intro hbarrier
  have hli := ppllStep_labels_preserved_of_paperSafe
    hψ κ ring C hSafe e i
  have hlr := ppllStep_labels_preserved_of_paperSafe
    hψ κ ring C hSafe e (ring.rightNeighbor i)
  have hbarrierOld : isBarrier hψ (C i) (C (ring.rightNeighbor i)) := by
    unfold isBarrier at hbarrier ⊢
    simpa only [hli, hlr] using hbarrier
  have hrightLeader := hSafe.no_free_barrier i hbarrierOld
  have hrightEq : ring.rightNeighbor i = lp :=
    huniq _ hrightLeader
  have hsurvive := ppllStep_unique_leader_survives
    hψ κ ring C hSafe lp hlp huniq e
  rw [hrightEq]
  simpa [AgentState.isLeader] using hsurvive

/-- **Concrete condition-5 reduction.** If the overwriting subsystem satisfies
`GroupIDBoundarySafe`, then the paper's stable ID sequence is preserved by one
concrete P_PLL step. Label preservation and survival of the old leader are
already concrete theorems; only group-ID preservation remains as the explicit
write-signal refinement obligation. -/
theorem stableID_preserved_of_groupIDBoundary
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (hgroupsSafe : GroupIDBoundarySafe hψ κ ring C)
    (e : Fin n) :
    isStableIDSequence hψ ring (ppllStep hψ κ ring C e) := by
  obtain ⟨lp, hlp, hlpLabel, hlabels, hgroups⟩ :=
    hSafe.stable_id_sequence
  obtain ⟨uniqueLp, _, huniq0⟩ := hSafe.unique_leader
  have hlpEq : lp = uniqueLp := huniq0 lp hlp
  have huniq : ∀ k, (C k).isLeader → k = lp := by
    intro k hk
    exact (huniq0 k hk).trans hlpEq.symm
  refine ⟨lp, ?_, ?_, ?_, ?_⟩
  · have hsurvive := ppllStep_unique_leader_survives
      hψ κ ring C hSafe lp hlp huniq e
    simpa [AgentState.isLeader] using hsurvive
  · rw [ppllStep_labels_preserved_of_paperSafe hψ κ ring C hSafe e lp]
    exact hlpLabel
  · intro k hk
    dsimp only
    rw [ppllStep_labels_preserved_of_paperSafe hψ κ ring C hSafe e]
    exact hlabels k hk
  · intro i hi hbound
    dsimp only
    rw [hgroupsSafe e]
    exact hgroups i hi hbound

/-- No position other than the original unique leader can output leader under
the concrete CHECK-boundary obligation. The only apparent exception is
WRITE_SEQ migration, but the paper's stable leader has label zero and therefore
is not migrated. -/
theorem ppllStep_no_other_leader
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (lp : Fin n) (hlp : (C lp).isLeader)
    (huniq : ∀ k, (C k).isLeader → k = lp)
    (e k : Fin n) (hk : (ppllStep hψ κ ring C e k).isLeader) :
    k = lp := by
  let j := ring.rightNeighbor e
  have horigin := ppll_local_leaders_have_input_origin
    hψ κ ring C hSafe.no_free_barrier hcheck e
  by_cases hke : k = e
  · subst k
    have hleft : (ppll hψ κ (C e) (C j)).1.leader = true := by
      rw [ppllStep, updatePair_initiator] at hk
      simpa only [j, AgentState.isLeader] using hk
    rcases horigin.1 (by simpa only [j] using hleft) with
      heLeader | hjLeader
    · exact huniq e (by simpa [AgentState.isLeader] using heLeader)
    · have hjEq : j = lp :=
        huniq j (by simpa [AgentState.isLeader] using hjLeader)
      by_cases hej : e = j
      · exact hej.trans hjEq
      · have heFollower : (C e).leader = false := by
          cases heq : (C e).leader
          · rfl
          · have heEq : e = lp :=
              huniq e (by simpa [AgentState.isLeader] using heq)
            exact (hej (heEq.trans hjEq.symm)).elim
        have hjLabel : (C j).label = ⟨0, hψ⟩ := by
          rw [hjEq]
          exact paperSafe_unique_leader_label_zero hψ ring C hSafe lp hlp
        have himpossible :=
          PPLLVerify.ppll_initiator_not_created_of_responder_leader_zero
            hψ κ (C e) (C j) heFollower hjLeader hjLabel
        have hfalse : false = true := himpossible.symm.trans hleft
        exact Bool.noConfusion hfalse
  · by_cases hkj : k = j
    · subst k
      have hne : j ≠ e := by
        intro hje
        exact hke hje
      have hright : (ppll hψ κ (C e) (C j)).2.leader = true := by
        rw [ppllStep, updatePair_responder _ _ _ _ hne] at hk
        simpa only [j, AgentState.isLeader] using hk
      have hjLeader := horigin.2 (by simpa only [j] using hright)
      exact huniq j (by simpa [AgentState.isLeader] using hjLeader)
    · have hkOld : (C k).isLeader := by
        rw [ppllStep, updatePair_other _ _ _ _ _ hke] at hk
        · exact hk
        · exact hkj
      exact huniq k hkOld

/-- **Concrete condition-1 preservation.** `PaperSafeConfig` plus the exact
CHECK-boundary obligation preserves the unique leader in one concrete P_PLL
step. This discharges Wu's condition-1 argument without a
`ProtocolProperties` instance.

It does not yet prove full closedness: preservation of the CHECK obligation and
conditions 2–5 remains open. -/
theorem uniqueLeader_preserved_of_checkBoundary
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (e : Fin n) :
    hasUniqueLeader n (ppllStep hψ κ ring C e) := by
  obtain ⟨lp, hlp, huniq⟩ := hSafe.unique_leader
  refine ⟨lp, ?_, ?_⟩
  · have hsurvive := ppllStep_unique_leader_survives
      hψ κ ring C hSafe lp hlp huniq e
    simpa [AgentState.isLeader] using hsurvive
  · intro k hk
    exact ppllStep_no_other_leader hψ κ ring C hSafe hcheck
      lp hlp huniq e k hk

/-- Packaged-protocol form of `uniqueLeader_preserved_of_checkBoundary`. -/
theorem protocol_uniqueLeader_preserved_of_checkBoundary
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (e : Fin n) :
    hasUniqueLeader n ((PPLL.protocol hψ κ).step ring C e) := by
  rw [← ppllStep_eq_protocol_step hψ κ ring C e]
  exact uniqueLeader_preserved_of_checkBoundary
    hψ κ ring C hSafe hcheck e

/-- Full one-step preservation of Wu's five-field schema, factored into the
three unresolved semantic boundary obligations. Conditions 1 and 3 are concrete
consequences; condition 5 uses group-ID preservation; conditions 2 and 4 are
named exactly rather than hidden as axioms or metadata. -/
theorem paperSafe_step_of_boundary_obligations
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (hgroupIDs : GroupIDBoundarySafe hψ κ ring C)
    (hbullets : BulletBoundarySafe hψ κ ring C)
    (hoverwriting : OverwritingBoundarySafe hψ κ ring C)
    (e : Fin n) :
    PaperSafeConfig hψ ring (ppllStep hψ κ ring C e) where
  unique_leader := uniqueLeader_preserved_of_checkBoundary
    hψ κ ring C hSafe hcheck e
  no_nonpeaceful_bullet := hbullets e
  no_free_barrier := noFreeBarrier_preserved_of_paperSafe
    hψ κ ring C hSafe e
  no_free_overwriting_signal := hoverwriting e
  stable_id_sequence := stableID_preserved_of_groupIDBoundary
    hψ κ ring C hSafe hgroupIDs e

/-- Packaged-protocol form of the boundary-factored paper-safe step theorem. -/
theorem protocol_paperSafe_step_of_boundary_obligations
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : PaperSafeConfig hψ ring C)
    (hcheck : CheckBoundarySafe hψ κ ring C)
    (hgroupIDs : GroupIDBoundarySafe hψ κ ring C)
    (hbullets : BulletBoundarySafe hψ κ ring C)
    (hoverwriting : OverwritingBoundarySafe hψ κ ring C)
    (e : Fin n) :
    PaperSafeConfig hψ ring ((PPLL.protocol hψ κ).step ring C e) := by
  rw [← ppllStep_eq_protocol_step hψ κ ring C e]
  exact paperSafe_step_of_boundary_obligations hψ κ ring C hSafe
    hcheck hgroupIDs hbullets hoverwriting e
