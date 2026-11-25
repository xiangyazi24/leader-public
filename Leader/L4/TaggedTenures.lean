import Leader.L4.BarrierLedger
import Leader.L4.Statement
import Leader.L4.TaggedTrace
import Init.Data.List.FinRange

namespace L4
namespace TaggedTenures

/-- The terminal reason for a living first-barrier tenure in an observed
surviving prefix. An open tenure is counted once even though it has not ended. -/
inductive Ending (n : Nat) where
  | kill (original : Fin n)
  | preemption
  | openAtCut
  deriving DecidableEq, Repr

/-- Accepted chronological charging certificates. The list of unused original
killers is proof-side state. A charged kill consumes its original identity
exactly once. A co-located preemption and an unfinished tenure are alternative
last events, not two separately chargeable events.

The interface to the literal trace must prove that the observed chronological
list has this certificate: in particular, that each nonfinal ending has an
original killer and that preemption can only be the final non-kill ending.
This inductive predicate does not assert that physical traces permit it. -/
inductive Chronology {n : Nat} : List (Fin n) → List (Ending n) → Prop where
  | done (unused : List (Fin n)) : Chronology unused []
  | preemption (unused : List (Fin n)) : Chronology unused [.preemption]
  | openAtCut (unused : List (Fin n)) : Chronology unused [.openAtCut]
  | kill {unused : List (Fin n)} {rest : List (Ending n)} (id : Fin n)
      (fresh : id ∈ unused) (tail : Chronology (unused.erase id) rest) :
      Chronology unused (.kill id :: rest)

/-- The number of charged living tenures following the cut is bounded by
the available original killers plus a single final exceptional tenure. -/
theorem length_le_unused_add_one {n : Nat} {unused : List (Fin n)}
    {endings : List (Ending n)} (h : Chronology unused endings) :
    endings.length ≤ unused.length + 1 := by
  induction h with
  | done => simp
  | preemption => simp
  | openAtCut => simp
  | @kill unused rest id fresh _ ih =>
      have hlen : (unused.erase id).length = unused.length - 1 := by
        rw [List.length_erase]
        simp [fresh]
      have hpos := List.length_pos_of_mem fresh
      simp only [List.length_cons]
      omega

/-- Count using the actual initial subset of sites carrying a tag, if it is
supplied, rather than allocating a killer at every ring site. -/
theorem tenure_bound_of_original_subset {n : Nat} {initial : List (Fin n)}
    {endings : List (Ending n)} (h : Chronology initial endings)
    (hn : initial.length ≤ n) : endings.length ≤ n + 1 := by
  have hc := length_le_unused_add_one h
  omega

/-- The uniform chronological bound, using all initial sites as the largest
allowed allocation of original killer identities. -/
theorem tenure_bound {n : Nat} {endings : List (Ending n)}
    (h : Chronology (List.finRange n) endings) : endings.length ≤ n + 1 := by
  exact tenure_bound_of_original_subset h (by simp)

/-- A certified concrete chronology, once extracted from a literal trace,
discharges the tenure-count input. -/
theorem ledger_tenureCount {n : Nat} {t : BarrierLedger.Totals}
    {initial : List (Fin n)} {endings : List (Ending n)}
    (h : Chronology initial endings) (hinitial : initial.length ≤ n)
    (halign : t.tenures = endings.length) : BarrierLedger.TenureCount n t := by
  unfold BarrierLedger.TenureCount
  rw [halign]
  exact tenure_bound_of_original_subset h hinitial

private theorem native_side_fields {p c1 : Nat} (u v : Site p c1) :
    (native u v).1.leader = u.leader ∧ (native u v).2.mark = v.mark := by
  have hi : (fireInitiator u).leader = u.leader := by
    unfold fireInitiator
    split <;> rfl
  have hr : (fireResponder v).mark = v.mark := by
    unfold fireResponder
    split
    · cases v.signal <;> rfl
    · rfl
  have hid (a b : Site p c1) :
      (impact a b).1.leader = a.leader ∧ (impact a b).2.mark = b.mark := by
    unfold impact
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have hfb (g : Bool) (a b : Site p c1) :
      (followerBullet g a b).1.leader = a.leader ∧
        (followerBullet g a b).2.mark = b.mark := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  unfold native
  simp only
  exact ⟨(hfb _ _ _).1.trans ((hid _ _).1.trans hi),
    (hfb _ _ _).2.trans ((hid _ _).2.trans hr)⟩

private theorem payment_side_fields {p c1 : Nat} (u v : Site p c1) :
    (payment u v).1.leader = u.leader ∧
      (v.mark = true → (payment u v).2.mark = true) := by
  unfold payment
  split
  · exact ⟨rfl, fun h => h⟩
  split
  · exact ⟨rfl, fun h => h⟩
  split
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun h => h⟩

private theorem pair_side_fields {p c1 : Nat} (u v : Site p c1) :
    (pairStep u v).1.leader = u.leader ∧
      (v.mark = true → (pairStep u v).2.mark = true) := by
  have hmat : (materialize u v).leader = u.leader := by
    unfold materialize
    split <;> rfl
  have hnat := native_side_fields (materialize u v) v
  have hpay := payment_side_fields (native (materialize u v) v).1
    (native (materialize u v) v).2
  have hprefix : (stepPrefix u v).1.leader = u.leader ∧
      (v.mark = true → (stepPrefix u v).2.mark = true) :=
    ⟨hpay.1.trans (hnat.1.trans hmat), fun h => hpay.2 (hnat.2.trans h)⟩
  unfold pairStep finishBirth
  simp only
  split <;> exact hprefix

/-- A pinned ghost immediately after a prospective tag site. -/
def AdjacentGhost {p c1 n : Nat} (x : Config p c1 n) (tag : Fin n) : Prop :=
  (x tag).mark = true ∧ (x (rightNeighbor tag)).leader = false

private theorem rightNeighbor_inj {n : Nat} {i j : Fin n}
    (h : rightNeighbor i = rightNeighbor j) : i = j := by
  have hh := congrArg Fin.val h
  change (i.val + 1) % n = (j.val + 1) % n at hh
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hil : i.val + 1 < n <;> by_cases hjl : j.val + 1 < n
  · rw [Nat.mod_eq_of_lt hil, Nat.mod_eq_of_lt hjl] at hh
    omega
  · have hje : j.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt hil, hje, Nat.mod_self] at hh
    omega
  · have hie : i.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt hjl, hie, Nat.mod_self] at hh
    omega
  · omega

/-- On any mark other than the tag's outgoing edge, the adjacent ghost
witness stays where it is. Its incoming mark can only be preserved/set when
the tag site is a responder, and the ghost's initiator leader bit cannot
change when the ghost site is an initiator. This treats the persistence
side of the final-preemption premise, not the geometry producing it. -/
theorem adjacentGhost_step_of_ne {p c1 n : Nat} {x : Config p c1 n}
    {tag e : Fin n} (hne : e ≠ tag) (hg : AdjacentGhost x tag) :
    AdjacentGhost (step x e) tag := by
  obtain ⟨hm, hl⟩ := hg
  constructor
  · by_cases hr : tag = rightNeighbor e
    · simp only [step, if_neg (Ne.symm hne), if_pos hr]
      exact (pair_side_fields _ _).2 (hr ▸ hm)
    · simp [step, Ne.symm hne, hr, hm]
  · have hr : rightNeighbor tag ≠ rightNeighbor e :=
      fun h => hne (rightNeighbor_inj h).symm
    by_cases he : rightNeighbor tag = e
    · simp [step, he, (pair_side_fields (x e) (x (rightNeighbor e))).1]
      exact he ▸ hl
    · simp [step, he, hr, hl]

/-- The same ghost remains pinned through an entire scheduler word that
does not service the tag's outgoing bond. -/
theorem adjacentGhost_run_of_not_mem {p c1 n : Nat} {x : Config p c1 n}
    {tag : Fin n} {w : List (Fin n)} (hw : tag ∉ w)
    (hg : AdjacentGhost x tag) : AdjacentGhost (run x w) tag := by
  induction w generalizing x with
  | nil => exact hg
  | cons e w ih =>
    have hn : e ≠ tag := fun he => hw (he ▸ List.mem_cons_self)
    have ht : tag ∉ w := fun ht => hw (List.mem_cons_of_mem e ht)
    exact ih ht (adjacentGhost_step_of_ne hn hg)

/-- On that outgoing service, the tag cannot leave into the pinned ghost:
it is either absorbed or its old identity was overwritten during firing. -/
theorem adjacentGhost_outgoing_ends_tag {p c1 n : Nat} {x : Config p c1 n}
    {tag : Fin n} (hg : AdjacentGhost x tag) :
    tagStep (x tag) (x (rightNeighbor tag)) true false = (false, false) := by
  rw [tagStep_outgoing]
  simp [tagTransfer, hg.1]

/-- Literal pinned-ghost suffix rule: it persists while the edge is unselected,
and the old tag ends on that edge if it is still there. -/
theorem adjacentGhost_suffix_ends_tag {p c1 n : Nat} {x : Config p c1 n}
    {tag : Fin n} {w : List (Fin n)} (hw : tag ∉ w) (hg : AdjacentGhost x tag) :
    tagStep (run x w tag) (run x w (rightNeighbor tag)) true false = (false, false) :=
  adjacentGhost_outgoing_ends_tag (adjacentGhost_run_of_not_mem hw hg)

/-- The literal front observer sees no living barrier after preemption by
an adjacent pinned ghost. -/
theorem adjacentGhost_firstLeader {p c1 n : Nat} {x : Config p c1 n}
    {tag : Fin n} (hg : AdjacentGhost x tag) :
    TaggedFront.firstLeader x tag = none := by
  have hat : TaggedFront.plusOffset tag 0 = tag := by
    apply Fin.ext
    simpa [TaggedFront.plusOffset] using Nat.mod_eq_of_lt tag.isLt
  cases n with
  | zero => exact Fin.elim0 tag
  | succ n =>
    simp [TaggedFront.firstLeader, TaggedFront.firstRoot, TaggedFront.firstMarkedEdge,
      List.ofFn_succ, hat, hg.1, hg.2]

/-- Once a surviving observer sees this adjacent ghost, it can never record
another living first-barrier tenure. No claim is made here that all
non-kill tenure endings produce the adjacent-ghost certificate. -/
theorem adjacentGhost_no_more_tenures {p c1 n : Nat}
    {s : TaggedTrace.Obs p c1 n} {tag : Fin n}
    (hc : s.carrier = some tag) (hg : AdjacentGhost s.config tag)
    (w : List (Fin n)) : (TaggedTrace.track s w).tenureCount = s.tenureCount := by
  have he (s : TaggedTrace.Obs p c1 n) (h : s.carrier = none)
      (w : List (Fin n)) : (TaggedTrace.track s w).tenureCount = s.tenureCount := by
    induction w generalizing s with
    | nil => rfl
    | cons e w ih =>
      simpa [TaggedTrace.track, TaggedTrace.advance, h] using
        ih (TaggedTrace.advance s e) (TaggedTrace.ended_step h e)
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    have hn : TaggedTrace.leaderNow s = none := by
      simp [TaggedTrace.leaderNow, hc, adjacentGhost_firstLeader hg]
    have hcount : (TaggedTrace.advance s e).tenureCount = s.tenureCount := by
      simp [TaggedTrace.advance, hc, hn]
    show (TaggedTrace.track (TaggedTrace.advance s e) w).tenureCount = s.tenureCount
    rw [← hcount]
    by_cases htag : e = tag
    · subst e
      have ht : tagTransfer (s.config tag) (s.config (rightNeighbor tag)) = false := by
        simp [tagTransfer, hg.1]
      apply he
      simp [TaggedTrace.advance, hc, TaggedTrace.carrierStep, ht]
    · cases hpost : (TaggedTrace.advance s e).carrier with
      | none => exact he _ hpost w
      | some j =>
        have hj := TaggedTrace.carrierStep_not_selected_stays s.config e tag j
          (Ne.symm htag) (by simpa [TaggedTrace.advance, hc] using hpost)
        subst j
        exact ih hpost (by
          rw [TaggedTrace.projection_step]
          exact adjacentGhost_step_of_ne htag hg)

#print axioms adjacentGhost_firstLeader
#print axioms adjacentGhost_no_more_tenures

#print axioms adjacentGhost_outgoing_ends_tag
#print axioms adjacentGhost_suffix_ends_tag

#print axioms adjacentGhost_step_of_ne
#print axioms adjacentGhost_run_of_not_mem

#print axioms length_le_unused_add_one
#print axioms tenure_bound_of_original_subset
#print axioms tenure_bound
#print axioms ledger_tenureCount

end TaggedTenures
end L4
