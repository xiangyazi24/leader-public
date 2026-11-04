import Leader.Wu.ShortGap.CyclicIncidenceChoice
import Leader.Core.FiniteUniformStoppingTree

/-!
# Joined-restricted incidence balance

This file adds one pipelining guard to the abstract incidence quotient of
`PeriodHIncidenceChoice`.  In a literal pipelined protocol a root can be
resolved during round `k` only after it has *joined* round `k`, that is, only
after both round-`(k-1)` denials have arrived.  A ghost word for round `k`
therefore evolves by a *restricted* step: the bare incidence update is applied
to joined roots only, while an unjoined `Race` root is untouched.

The single mathematical point proved here is that the local good-versus-bad
edge balance survives the restriction exactly, with no loss factor.  An
unjoined `Race` root can never be resolved by any physical edge, so a
restricted step out of such a word is never frozen and therefore never a
uniform failure; the restricted bad-edge count is then literally `0`.  In the
remaining case every unresolved root is joined, the restricted step coincides
with `incidenceStep` on that configuration, and the sequential theorem
`goodEdgeCount_ge_badEdgeCount` applies verbatim.

The reserve section records the matching progress statement.  The restricted
child-sum inequality needs a *joined* `Race` root: the outgoing physical port
of such a root still strictly lowers the reserve.  Without one the restricted
step is a literal stutter and the child sum is exactly `n *` the reserve, which
is precisely the phase whose cost the separate service/rearm debt must pay.

Scope.  This file defines no rounds, no denial tokens, and no service layer;
`joined` is an opaque Boolean predicate supplied by the caller.  Nothing here
claims stabilization, termination, or any final complexity bound.
-/

namespace ShortGapJoinedIncidenceBalance

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice

set_option autoImplicit false

/-! ## Finite uniform sums -/

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-! ## The joined-restricted incidence step -/

/-- One physical interaction seen by the round-`k` ghost word.  Only roots
that have already joined round `k` may be resolved; an unjoined root keeps its
current choice whatever the scheduler does. -/
def joinedIncidenceStep {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n) :
    Configuration m := fun i =>
  if joined i then incidenceStep P C edge i else C i

/-- A joined root is updated exactly as in the bare quotient. -/
theorem joinedIncidenceStep_of_joined {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (i : Fin m) (hj : joined i = true) :
    joinedIncidenceStep P joined C edge i = incidenceStep P C edge i := by
  simp [joinedIncidenceStep, hj]

/-- An unjoined root is frozen at its current choice. -/
theorem joinedIncidenceStep_of_unjoined {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (i : Fin m) (hj : joined i = false) :
    joinedIncidenceStep P joined C edge i = C i := by
  simp [joinedIncidenceStep, hj]

/-- Every already-resolved root keeps its value, joined or not. -/
theorem joinedIncidenceStep_of_ne_race {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (i : Fin m) (hi : C i ≠ .race) :
    joinedIncidenceStep P joined C edge i = C i := by
  by_cases hj : joined i = true
  · simp [joinedIncidenceStep, hj, incidenceStep, hi]
  · have hj' : joined i = false := by
      cases h : joined i with
      | false => rfl
      | true => exact absurd h hj
    simp [joinedIncidenceStep, hj']

/-- An unjoined `Race` root stays `Race` under every physical edge. -/
theorem joinedIncidenceStep_race_of_unjoined {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (i : Fin m) (hi : C i = .race) (hj : joined i = false) :
    joinedIncidenceStep P joined C edge i = .race := by
  rw [joinedIncidenceStep_of_unjoined P joined C edge i hj, hi]

/-- Hence no physical edge can freeze a word carrying an unjoined `Race`
root. -/
theorem not_frozen_of_unjoined_race {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (i : Fin m) (hi : C i = .race) (hj : joined i = false) :
    ¬ Frozen (joinedIncidenceStep P joined C edge) := by
  intro hfrozen
  exact hfrozen i (joinedIncidenceStep_race_of_unjoined P joined C edge i hi hj)

/-- Conversely, a frozen restricted step certifies that every unresolved root
had already joined. -/
theorem all_joined_of_frozen {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (hfrozen : Frozen (joinedIncidenceStep P joined C edge)) :
    ∀ i, C i = .race → joined i = true := by
  intro i hi
  cases hj : joined i with
  | true => rfl
  | false =>
      exact absurd
        (joinedIncidenceStep_race_of_unjoined P joined C edge i hi hj)
        (hfrozen i)

/-- With all unresolved roots joined, the restricted step is literally the bare
incidence step on that configuration. -/
theorem joinedIncidenceStep_eq_of_all_joined {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (hall : ∀ i, C i = .race → joined i = true) :
    joinedIncidenceStep P joined C edge = incidenceStep P C edge := by
  funext i
  by_cases hj : joined i = true
  · exact joinedIncidenceStep_of_joined P joined C edge i hj
  · have hi : C i ≠ .race := fun h => hj (hall i h)
    rw [joinedIncidenceStep_of_ne_race P joined C edge i hi]
    simp [incidenceStep, hi]

/-- With no unresolved root joined, the restricted step is a literal stutter. -/
theorem joinedIncidenceStep_eq_self_of_no_joined_race {n m : Nat}
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) (hnone : ∀ i, C i = .race → joined i = false) :
    joinedIncidenceStep P joined C edge = C := by
  funext i
  by_cases hi : C i = .race
  · exact joinedIncidenceStep_of_unjoined P joined C edge i (hnone i hi)
  · exact joinedIncidenceStep_of_ne_race P joined C edge i hi

/-- The restricted step preserves an existing oriented candidate: both of its
endpoints are already resolved. -/
theorem candidate10_joinedIncidenceStep {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (candidate : Fin m) (edge : Fin n)
    (h : Candidate10 ring C candidate) :
    Candidate10 ring (joinedIncidenceStep P joined C edge) candidate := by
  refine ⟨?_, ?_⟩
  · rw [joinedIncidenceStep_of_ne_race P joined C edge candidate
      (by rw [h.1]; exact fun hcon => Choice.noConfusion hcon)]
    exact h.1
  · rw [joinedIncidenceStep_of_ne_race P joined C edge
      (ring.rightNeighbor candidate)
      (by rw [h.2]; exact fun hcon => Choice.noConfusion hcon)]
    exact h.2

/-- The restricted step preserves existence of a resolved root. -/
theorem joinedIncidenceStep_hasNonRace {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n)
    (h : HasNonRace C) : HasNonRace (joinedIncidenceStep P joined C edge) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [joinedIncidenceStep_of_ne_race P joined C edge i hi]; exact hi⟩

/-! ## Restricted good and bad physical edges -/

/-- A physical edge whose restricted step creates an oriented candidate. -/
def JoinedCreatesCandidate {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) : Prop :=
  ∃ i, Candidate10 ring (joinedIncidenceStep P joined C edge) i

/-- A physical edge whose restricted step resolves the whole word back to its
previous all-equal base: the uniform-failure event of the stopped tree. -/
def JoinedRestoresBase {n m : Nat} (b : FrozenValue) (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m) (edge : Fin n) : Prop :=
  ∀ i, joinedIncidenceStep P joined C edge i = b.toChoice

/-- A restored base is in particular frozen. -/
theorem JoinedRestoresBase.frozen {n m : Nat} {b : FrozenValue}
    {P : Placement n m} {joined : Fin m → Bool} {C : Configuration m}
    {edge : Fin n} (h : JoinedRestoresBase b P joined C edge) :
    Frozen (joinedIncidenceStep P joined C edge) := by
  intro i hi
  have hval := h i
  rw [hi] at hval
  cases b <;> simp [FrozenValue.toChoice] at hval

/-- Uniform failure of a restricted step certifies that every unresolved root
had joined.  This is the exact statement that lets the sequential balance be
reused with no loss. -/
theorem all_joined_of_joinedRestoresBase {n m : Nat} (b : FrozenValue)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) (h : JoinedRestoresBase b P joined C edge) :
    ∀ i, C i = .race → joined i = true :=
  all_joined_of_frozen P joined C edge h.frozen

noncomputable def joinedGoodEdge {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) : Bool := by
  classical
  exact decide (JoinedCreatesCandidate ring P joined C edge)

noncomputable def joinedBadEdge {n m : Nat} (b : FrozenValue)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) : Bool := by
  classical
  exact decide (JoinedRestoresBase b P joined C edge)

noncomputable def joinedGoodEdgeCount {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m) : Nat :=
  (List.ofFn (fun edge : Fin n =>
    if joinedGoodEdge ring P joined C edge then 1 else 0)).sum

noncomputable def joinedBadEdgeCount {n m : Nat} (b : FrozenValue)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m) : Nat :=
  (List.ofFn (fun edge : Fin n =>
    if joinedBadEdge b P joined C edge then 1 else 0)).sum

/-- When the restriction is inactive the restricted bad count is the bare bad
count. -/
private theorem joinedBadEdgeCount_eq {n m : Nat} (b : FrozenValue)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (hstep : ∀ edge : Fin n,
      joinedIncidenceStep P joined C edge = incidenceStep P C edge) :
    joinedBadEdgeCount b P joined C = badEdgeCount b P C := by
  classical
  unfold joinedBadEdgeCount badEdgeCount
  apply ofFn_sum_eq
  intro edge
  by_cases hb : RestoresBase b P C edge
  · have hjb : JoinedRestoresBase b P joined C edge := by
      intro i
      rw [hstep edge]
      exact hb i
    simp [joinedBadEdge, badEdge, hb, hjb]
  · have hjb : ¬ JoinedRestoresBase b P joined C edge := by
      intro h
      refine hb ?_
      intro i
      rw [← hstep edge]
      exact h i
    simp [joinedBadEdge, badEdge, hb, hjb]

/-- When the restriction is inactive the restricted good count is the bare good
count. -/
private theorem joinedGoodEdgeCount_eq {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (hstep : ∀ edge : Fin n,
      joinedIncidenceStep P joined C edge = incidenceStep P C edge) :
    joinedGoodEdgeCount ring P joined C = goodEdgeCount ring P C := by
  classical
  unfold joinedGoodEdgeCount goodEdgeCount
  apply ofFn_sum_eq
  intro edge
  by_cases hg : CreatesCandidate ring P C edge
  · have hjg : JoinedCreatesCandidate ring P joined C edge := by
      obtain ⟨i, hi⟩ := hg
      exact ⟨i, by rw [hstep edge]; exact hi⟩
    simp [joinedGoodEdge, goodEdge, hg, hjg]
  · have hjg : ¬ JoinedCreatesCandidate ring P joined C edge := by
      intro h
      obtain ⟨i, hi⟩ := h
      exact hg ⟨i, by rw [← hstep edge]; exact hi⟩
    simp [joinedGoodEdge, goodEdge, hg, hjg]

/-- Sanity anchor: with every root joined the restricted counts are literally
the bare ones, so the restricted balance below is a genuine extension of
`goodEdgeCount_ge_badEdgeCount` rather than a vacuous statement. -/
theorem joinedEdgeCount_all_joined {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (b : FrozenValue) (C : Configuration m) :
    joinedBadEdgeCount b P (fun _ => true) C = badEdgeCount b P C ∧
      joinedGoodEdgeCount ring P (fun _ => true) C =
        goodEdgeCount ring P C := by
  have hstep : ∀ edge : Fin n,
      joinedIncidenceStep P (fun _ => true) C edge = incidenceStep P C edge :=
    fun edge =>
      joinedIncidenceStep_eq_of_all_joined P (fun _ => true) C edge
        (fun _ _ => rfl)
  exact ⟨joinedBadEdgeCount_eq b P (fun _ => true) C hstep,
    joinedGoodEdgeCount_eq ring P (fun _ => true) C hstep⟩

/-- With an unjoined unresolved root present, no physical edge can produce a
uniform failure at all. -/
private theorem joinedBadEdgeCount_eq_zero {n m : Nat} (b : FrozenValue)
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (hall : ¬ ∀ i, C i = .race → joined i = true) :
    joinedBadEdgeCount b P joined C = 0 := by
  classical
  have hzero : ∀ edge : Fin n,
      (if joinedBadEdge b P joined C edge then 1 else 0) = 0 := by
    intro edge
    have hjb : ¬ JoinedRestoresBase b P joined C edge := by
      intro h
      exact hall (all_joined_of_joinedRestoresBase b P joined C edge h)
    simp [joinedBadEdge, hjb]
  calc joinedBadEdgeCount b P joined C
      = (List.ofFn (fun _ : Fin n => (0 : Nat))).sum := by
        unfold joinedBadEdgeCount
        exact ofFn_sum_eq _ _ hzero
    _ = 0 := by rw [ofFn_sum_const, Nat.mul_zero]

/-- **Restricted local balance.**  For an all-equal base with at least one
unresolved root, the joined-restricted uniform-failure mass is no larger than
the joined-restricted candidate-creation mass, for *every* join predicate.

Either every unresolved root has joined, in which case the restricted step is
the bare incidence step and the sequential theorem applies verbatim; or some
unresolved root has not joined, in which case no edge freezes the word and the
restricted failure mass is `0`.  Pipelining therefore costs nothing in this
balance. -/
theorem joinedGoodEdgeCount_ge_joinedBadEdgeCount {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (b : FrozenValue) (joined : Fin m → Bool) (C : Configuration m)
    (hbase : BaseOrRace b C) (hrace : HasRace C) :
    joinedBadEdgeCount b P joined C ≤ joinedGoodEdgeCount ring P joined C := by
  classical
  by_cases hall : ∀ i, C i = .race → joined i = true
  · have hstep : ∀ edge : Fin n,
        joinedIncidenceStep P joined C edge = incidenceStep P C edge :=
      fun edge => joinedIncidenceStep_eq_of_all_joined P joined C edge hall
    rw [joinedBadEdgeCount_eq b P joined C hstep,
      joinedGoodEdgeCount_eq ring P joined C hstep]
    exact goodEdgeCount_ge_badEdgeCount ring hm P hn b C hbase hrace
  · rw [joinedBadEdgeCount_eq_zero b P joined C hall]
    exact Nat.zero_le _

/-! ## Restricted race reserve -/

private theorem joinedIncidenceStep_raceWeight_le {n m : Nat}
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) (i : Fin m) :
    (if joinedIncidenceStep P joined C edge i = .race then 1 else 0) ≤
      (if C i = .race then 1 else 0) := by
  by_cases hi : C i = .race
  · have hone : (if C i = Choice.race then (1 : Nat) else 0) = 1 := if_pos hi
    rw [hone]
    split <;> omega
  · rw [joinedIncidenceStep_of_ne_race P joined C edge i hi]
    exact Nat.le_refl _

/-- No restricted physical interaction increases the Race reserve. -/
theorem choiceRaceReserve_joinedIncidenceStep_le {n m : Nat}
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (edge : Fin n) :
    choiceRaceReserve (joinedIncidenceStep P joined C edge) ≤
      choiceRaceReserve C := by
  unfold choiceRaceReserve
  exact ofFn_sum_le _ _ (joinedIncidenceStep_raceWeight_le P joined C edge)

/-- The outgoing physical port of a *joined* Race root strictly lowers the
reserve.  Joining is exactly what the restriction requires here. -/
theorem choiceRaceReserve_joinedIncidenceStep_outgoing_lt {n m : Nat}
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (i : Fin m) (hi : C i = .race) (hj : joined i = true) :
    choiceRaceReserve (joinedIncidenceStep P joined C (P.root i)) <
      choiceRaceReserve C := by
  unfold choiceRaceReserve
  apply ofFn_sum_lt_of_single_lt _ _ i
  · exact joinedIncidenceStep_raceWeight_le P joined C (P.root i)
  · simp [joinedIncidenceStep, hj, incidenceStep, hi]

/-- **Restricted child-sum reserve inequality.**  One unit of strict progress
is exposed among the `n` scheduler children provided some unresolved root has
already joined.  This hypothesis is not removable: see
`joinedReserve_childSum_eq_of_no_joined_race`. -/
theorem joinedReserve_childSum {n m : Nat} (P : Placement n m)
    (joined : Fin m → Bool) (C : Configuration m)
    (hrace : ∃ i, C i = .race ∧ joined i = true) :
    1 + (List.ofFn (fun edge : Fin n =>
      choiceRaceReserve (joinedIncidenceStep P joined C edge))).sum ≤
        n * choiceRaceReserve C := by
  obtain ⟨i, hi, hj⟩ := hrace
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n =>
      choiceRaceReserve (joinedIncidenceStep P joined C edge))
    (fun _ : Fin n => choiceRaceReserve C) (P.root i)
    (fun edge => choiceRaceReserve_joinedIncidenceStep_le P joined C edge)
    (choiceRaceReserve_joinedIncidenceStep_outgoing_lt P joined C i hi hj)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- Without a joined unresolved root the restricted round makes no reserve
progress whatsoever: the child sum saturates at `n *` the current reserve.
Whatever pays for such a round must come from a separate service or rearm
debt, not from this potential. -/
theorem joinedReserve_childSum_eq_of_no_joined_race {n m : Nat}
    (P : Placement n m) (joined : Fin m → Bool) (C : Configuration m)
    (hnone : ∀ i, C i = .race → joined i = false) :
    (List.ofFn (fun edge : Fin n =>
      choiceRaceReserve (joinedIncidenceStep P joined C edge))).sum =
        n * choiceRaceReserve C := by
  rw [ofFn_sum_eq
    (fun edge : Fin n =>
      choiceRaceReserve (joinedIncidenceStep P joined C edge))
    (fun _ : Fin n => choiceRaceReserve C)
    (fun edge => by
      rw [joinedIncidenceStep_eq_self_of_no_joined_race P joined C edge hnone]),
    ofFn_sum_const]

#print axioms joinedGoodEdgeCount_ge_joinedBadEdgeCount
#print axioms joinedReserve_childSum

end ShortGapJoinedIncidenceBalance
