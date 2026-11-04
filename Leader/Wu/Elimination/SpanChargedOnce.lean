import Leader.Wu.Elimination.NonrenewableCredits


set_option autoImplicit false


namespace SpanChargedOnceAudit


open NonrenewableCredits


/-!
# Fresh credits, fixed spans, and absorption cuts

A marked MOVE pays one unit only when its destination credit changes from
true to false and no site is refilled. Clearing a destination that was already
false pays nothing. `MoveCreditRows` records this edge-local obligation for
the supplied transition, credit observation, destination selector, and allowed
states. `routeRows` supplies a nonempty, invariant-preserving proof-ghost
instance on a single route of distinct fresh destinations. It is not an
instantiation for all physical retry histories.

Keep geometric span separate from accumulated transport work. The explicit
route [2, 1] has weights 4 -> 2 -> 2 on two passes. The first span three is
paid; restarting the charge at the second pass fails. With the original start
ledger and the same span, however, `fixed_span_survives_retries` preserves the
charge under every later spend. The whole two-pass episode still pays span
three, although it does not pay four accumulated MOVEs. These examples do not
refute an expected renewal bound already expressed at fixed geometric span.

An absorption cut must satisfy a drop between its actual consecutive cut
states, including intervening re-arming. A local drop followed by a return to
the old phase does not supply that condition, and cutting never refills the
credit ledger. `cut_hstep_from_fresh_moves` carries the remaining trace-domain,
span, local-cost, and global-phase obligations explicitly.

Checked against `NonrenewableCredits` and the current
`PPLLRepair.eliminateLeadersNoCollisionMove` / `Signal` definitions in
`Leader/Wu/Protocol/Repairs.lean`. The aligned transport branch clears `signal_B` without
a pre-value-one guard; the signal stage can later restore it on a bulletless
responder. The small `Cell` projection below records only the transport
assignment. No full K2 refinement, restart closure, physical freshness
invariant, or new global complexity bound is claimed by these accounting
lemmas.
-/


/-- One genuine true-to-false change, with no refill elsewhere, loses a unit. -/
theorem fresh_spend_weight {n : Nat} :
    ∀ (x y : Credits n) (i : Fin n),
      OnlySpends x y → x i = true → y i = false → w y + 1 ≤ w x := by
  induction n with
  | zero =>
      intro x y i _hmono _hx _hy
      rcases i with ⟨j, hj⟩
      omega
  | succ n ih =>
      intro x y i hmono hx hy
      rcases i with ⟨j, hj⟩
      cases j with
      | zero =>
          change x (0 : Fin (n + 1)) = true at hx
          change y (0 : Fin (n + 1)) = false at hy
          have ht := spend_monotone
            (fun k : Fin n => x k.succ) (fun k : Fin n => y k.succ)
            (fun k hk => hmono k.succ hk)
          change (bit (y 0) + w (fun k : Fin n => y k.succ)) + 1 ≤
            bit (x 0) + w (fun k : Fin n => x k.succ)
          rw [hx, hy]
          change (0 + w (fun k : Fin n => y k.succ)) + 1 ≤
            1 + w (fun k : Fin n => x k.succ)
          omega
      | succ j =>
          have hjn : j < n := by omega
          have ht := ih
            (fun k : Fin n => x k.succ) (fun k : Fin n => y k.succ)
            (⟨j, hjn⟩ : Fin n) (fun k hk => hmono k.succ hk) hx hy
          have hh := bit_monotone (x 0) (y 0) (hmono 0)
          change (bit (y 0) + w (fun k : Fin n => y k.succ)) + 1 ≤
            bit (x 0) + w (fun k : Fin n => x k.succ)
          omega


/-- The one remaining physical/ghost row obligation. `some i` must mark an
actual transported destination; `none` marks other rows. Freshness is an
explicit precondition asserted on Allowed states, not inferred from clearing. -/
structure MoveCreditRows {S : Type} {n : Nat}
    (step : S → Fin n → S) (credits : S → Credits n)
    (destination : S → Fin n → Option (Fin n)) (Allowed : S → Prop) : Prop where
  move_spends_fresh_destination : ∀ s e, Allowed s →
    OnlySpends (credits s) (credits (step s e)) ∧
    ∀ i : Fin n, destination s e = some i →
      credits s i = true ∧ credits (step s e) i = false


def marked {n : Nat} : Option (Fin n) → Nat
  | none => 0
  | some _ => 1


def moveCount {n : Nat} (destination : Nat → Option (Fin n)) : Nat → Nat
  | 0 => 0
  | t + 1 => moveCount destination t + marked (destination t)


theorem move_row_budget {S : Type} {n : Nat}
    {step : S → Fin n → S} {credits : S → Credits n}
    {destination : S → Fin n → Option (Fin n)} {Allowed : S → Prop}
    (H : MoveCreditRows step credits destination Allowed)
    (s : S) (e : Fin n) (hs : Allowed s) :
    marked (destination s e) + w (credits (step s e)) ≤ w (credits s) := by
  have hr := H.move_spends_fresh_destination s e hs
  cases hd : destination s e with
  | none =>
      change 0 + w (credits (step s e)) ≤ w (credits s)
      rw [Nat.zero_add]
      exact spend_monotone (credits s) (credits (step s e)) hr.1
  | some i =>
      have hf := hr.2 i hd
      have hw := fresh_spend_weight (credits s) (credits (step s e)) i
        hr.1 hf.1 hf.2
      change 1 + w (credits (step s e)) ≤ w (credits s)
      omega


/-- A single allowed MOVE onto an exhausted destination defeats the fresh law. -/
theorem no_fresh_row_at_spent_destination {S : Type} {n : Nat}
    (step : S → Fin n → S) (credits : S → Credits n)
    (destination : S → Fin n → Option (Fin n)) (Allowed : S → Prop)
    (s : S) (e i : Fin n) (hs : Allowed s)
    (hd : destination s e = some i) (hspent : credits s i = false) :
    ¬ MoveCreditRows step credits destination Allowed := by
  intro H
  have hf := (H.move_spends_fresh_destination s e hs).2 i hd
  have he : false = true := hspent.symm.trans hf.1
  cases he


/-- Arithmetic lifting only; the protocol obligation remains the edge law. -/
theorem row_telescope {n : Nat} (credit : Nat → Credits n)
    (destination : Nat → Option (Fin n)) :
    ∀ T : Nat,
      (∀ t, t < T →
        marked (destination t) + w (credit (t + 1)) ≤ w (credit t)) →
      moveCount destination T + w (credit T) ≤ w (credit 0) := by
  intro T
  induction T with
  | zero =>
      intro _hrow
      change 0 + w (credit 0) ≤ w (credit 0)
      rw [Nat.zero_add]
      exact Nat.le_refl _
  | succ T ih =>
      intro hrow
      have hp := ih (fun t ht => hrow t (by omega))
      have hl := hrow T (by omega)
      change (moveCount destination T + marked (destination T)) +
        w (credit (T + 1)) ≤ w (credit 0)
      omega


theorem fresh_trace_budget {S : Type} {n : Nat}
    {step : S → Fin n → S} {credits : S → Credits n}
    {destination : S → Fin n → Option (Fin n)} {Allowed : S → Prop}
    (H : MoveCreditRows step credits destination Allowed)
    (trace : Nat → S) (edge : Nat → Fin n) (T : Nat)
    (hnext : ∀ t, t < T → trace (t + 1) = step (trace t) (edge t))
    (hsafe : ∀ t, t < T → Allowed (trace t)) :
    moveCount (fun t => destination (trace t) (edge t)) T +
      w (credits (trace T)) ≤ w (credits (trace 0)) := by
  apply row_telescope (fun t => credits (trace t))
    (fun t => destination (trace t) (edge t)) T
  intro t ht
  rw [hnext t ht]
  exact move_row_budget H (trace t) (edge t) (hsafe t ht)


/-- B = 1. Use d = moveCount for transported cells, or d = moveCount + 1
when the terminal collision/absorption contact is included in the span. -/
theorem single_traversal_span {S : Type} {n : Nat}
    {step : S → Fin n → S} {credits : S → Credits n}
    {destination : S → Fin n → Option (Fin n)} {Allowed : S → Prop}
    (H : MoveCreditRows step credits destination Allowed)
    (trace : Nat → S) (edge : Nat → Fin n) (T d : Nat)
    (hnext : ∀ t, t < T → trace (t + 1) = step (trace t) (edge t))
    (hsafe : ∀ t, t < T → Allowed (trace t))
    (hd : d ≤ moveCount (fun t => destination (trace t) (edge t)) T + 1) :
    SpanChargedOnce 1 d (credits (trace 0)) (credits (trace T)) := by
  have hb := fresh_trace_budget H trace edge T hnext hsafe
  change d ≤ 1 * (w (credits (trace 0)) - w (credits (trace T)) + 1)
  omega


/-- Retries cannot destroy an already-valid charge for the original fixed span. -/
theorem fixed_span_survives_retries {n : Nat} (B d : Nat)
    (x y z : Credits n) (hspan : SpanChargedOnce B d x y)
    (hyz : OnlySpends y z) : SpanChargedOnce B d x z := by
  have hw := spend_monotone y z hyz
  have hd : w x - w y + 1 ≤ w x - w z + 1 := by omega
  change d ≤ B * (w x - w z + 1)
  exact Nat.le_trans hspan (Nat.mul_le_mul_left B hd)


/-- A necessary capacity bound, useful when d is accumulated work instead. -/
theorem span_capacity {n : Nat} (B d : Nat) (x y : Credits n)
    (hspan : SpanChargedOnce B d x y) : d ≤ B * (n + 1) := by
  have hw := w_start_le x
  have hd : w x - w y + 1 ≤ n + 1 := by omega
  exact Nat.le_trans hspan (Nat.mul_le_mul_left B hd)


/-! Actual first-visit ghost updates. Re-clearing is executable but costs zero
new credits. These functions do not modify or prescribe physical K2 state. -/


def clearAt {n : Nat} (c : Credits n) (destination : Fin n) : Credits n :=
  spend c (fun i => decide (i = destination))


theorem clearAt_only {n : Nat} (c : Credits n) (i : Fin n) :
    OnlySpends c (clearAt c i) :=
  spend_only c (fun j => decide (j = i))


theorem clearAt_destination {n : Nat} (c : Credits n) (i : Fin n) :
    clearAt c i i = false := by
  simp [clearAt, spend]


theorem clearAt_of_spent {n : Nat} (c : Credits n) (i : Fin n)
    (hc : c i = false) : clearAt c i = c := by
  funext j
  by_cases hj : j = i
  · subst j
    exact (clearAt_destination c i).trans hc.symm
  · simp [clearAt, spend, hj]

/-- Clearing a single destination loses a credit exactly when it was fresh.
The reverse direction uses idempotence at an already-spent destination. -/
theorem clearAt_loses_credit_iff {n : Nat} (c : Credits n) (i : Fin n) :
    w (clearAt c i) + 1 ≤ w c ↔ c i = true := by
  constructor
  · intro h
    cases hi : c i with
    | false =>
        rw [clearAt_of_spent c i hi] at h
        omega
    | true => rfl
  · intro hi
    exact fresh_spend_weight c (clearAt c i) i (clearAt_only c i) hi
      (clearAt_destination c i)


def clearWord {n : Nat} (c : Credits n) : List (Fin n) → Credits n
  | [] => c
  | i :: sites => clearWord (clearAt c i) sites


theorem clearWord_only {n : Nat} (c : Credits n) (sites : List (Fin n)) :
    OnlySpends c (clearWord c sites) := by
  induction sites generalizing c with
  | nil =>
      intro j hj
      exact hj
  | cons i sites ih =>
      intro j hj
      exact (clearAt_only c i) j ((ih (clearAt c i)) j hj)

/-! A finite first-traversal producer. The remaining route contains distinct,
fresh destinations. Its invariant is preserved by each clear-and-pop row.
This proof ghost witnesses the row interface and is not the physical K2. -/

/-- A credit map together with the still-unvisited suffix of one route. -/
abbrev RouteState (n : Nat) := Credits n × List (Fin n)

/-- Clear the next destination and remove it from the pending route. -/
def routeStep {n : Nat} (s : RouteState n) (_e : Fin n) : RouteState n :=
  match s.2 with
  | [] => s
  | i :: sites => (clearAt s.1 i, sites)

/-- Mark exactly the destination of the next clear-and-pop row. -/
def routeDestination {n : Nat} (s : RouteState n) (_e : Fin n) : Option (Fin n) :=
  s.2.head?

/-- No pending destination repeats, and every pending credit is still fresh. -/
def RouteAllowed {n : Nat} (s : RouteState n) : Prop :=
  s.2.Nodup ∧ ∀ i, i ∈ s.2 → s.1 i = true

/-- The route invariant produces the edge-local fresh-credit requirement. -/
theorem routeRows {n : Nat} :
    MoveCreditRows (routeStep (n := n)) Prod.fst routeDestination RouteAllowed := by
  constructor
  rintro ⟨c, sites⟩ e hs
  cases sites with
  | nil =>
      refine ⟨fun _ h => h, ?_⟩
      intro i hi
      cases hi
  | cons j sites =>
      refine ⟨clearAt_only c j, ?_⟩
      intro i hi
      change some j = some i at hi
      have hji : j = i := Option.some.inj hi
      subst i
      exact ⟨hs.2 j (List.mem_cons_self), clearAt_destination c j⟩

/-- Distinct pending destinations stay fresh after the current head is spent. -/
theorem routeAllowed_step {n : Nat} (s : RouteState n) (e : Fin n)
    (hs : RouteAllowed s) : RouteAllowed (routeStep s e) := by
  rcases s with ⟨c, sites⟩
  cases sites with
  | nil => exact hs
  | cons i sites =>
      have hnd := List.nodup_cons.mp hs.1
      refine ⟨hnd.2, ?_⟩
      intro j hj
      have hji : j ≠ i := by
        intro he
        subst j
        exact hnd.1 hj
      have hf := hs.2 j (List.mem_cons_of_mem i hj)
      change clearAt c i j = true
      simpa [clearAt, spend, hji] using hf


def exhausted (n : Nat) : Credits n := fun _ => false


theorem clearWord_exhausted {n : Nat} (sites : List (Fin n)) :
    clearWord (exhausted n) sites = exhausted n := by
  induction sites with
  | nil => rfl
  | cons i sites ih =>
      change clearWord (clearAt (exhausted n) i) sites = exhausted n
      rw [clearAt_of_spent (exhausted n) i rfl]
      exact ih


theorem exhausted_traversal_refutes {n : Nat} (B : Nat)
    (sites : List (Fin n)) (hlen : B < sites.length) :
    ¬ SpanChargedOnce B sites.length (exhausted n)
      (clearWord (exhausted n) sites) := by
  rw [clearWord_exhausted]
  intro h
  have hs := no_spend_requires_short_span B sites.length
    (exhausted n) (exhausted n) rfl h
  omega


/-- Every fixed B fails on exhausted credit maps at a proper candidate span.
This proves an accounting obstruction, not physical reachability of the span. -/
theorem no_uniform_B_exhausted (B : Nat) :
    2 ≤ B + 2 ∧ B + 2 < B + 3 ∧
      ¬ SpanChargedOnce B (B + 2)
        (exhausted (B + 3)) (exhausted (B + 3)) := by
  refine ⟨by omega, by omega, ?_⟩
  intro h
  have hs := no_spend_requires_short_span B (B + 2)
    (exhausted (B + 3)) (exhausted (B + 3)) rfl h
  omega


/-- Repeating the same hit mask never pays for another span greater than B. -/
theorem repeated_mask_refutes {n : Nat} (B d : Nat) (c hit : Credits n)
    (hd : B < d) :
    ¬ SpanChargedOnce B d (spend c hit) (spend (spend c hit) hit) := by
  rw [revisit_spends_nothing]
  intro h
  have hs := no_spend_requires_short_span B d
    (spend c hit) (spend c hit) rfl h
  omega


/-! Four sites, two distinct transported destinations. Sites 3 and 0 may be
viewed as shooter and victim coordinates, but only the credit trace is proved.
Each pass has two follower transports; counting terminal contact gives span 3.
The putative absorption/re-arm interval leaves this proof ghost unchanged. -/


def tinyStart : Credits 4 := fun _ => true


def tinyRoute : List (Fin 4) := [2, 1]


def tinyFirst : Credits 4 := clearWord tinyStart tinyRoute


def tinyRepeat : Credits 4 := clearWord tinyFirst tinyRoute

/-- Execute the explicit two-destination route, then remain at the empty suffix. -/
def tinyRouteTrace : Nat → RouteState 4
  | 0 => (tinyStart, tinyRoute)
  | t + 1 => routeStep (tinyRouteTrace t) 0

/-- The fresh-route domain has a concrete initial state with two pending MOVEs. -/
theorem tiny_route_initial_allowed : RouteAllowed (tinyRouteTrace 0) := by
  constructor
  · decide
  · intro _ _
    rfl

/-- The row invariant holds along the whole concrete route execution. -/
theorem tiny_route_allowed (t : Nat) : RouteAllowed (tinyRouteTrace t) := by
  induction t with
  | zero => exact tiny_route_initial_allowed
  | succ t ih => exact routeAllowed_step (tinyRouteTrace t) 0 ih

/-- This producer executes two marked rows and reaches the same first-pass ledger. -/
theorem tiny_route_two_moves :
    moveCount (fun t => routeDestination (tinyRouteTrace t) 0) 2 = 2 ∧
      (tinyRouteTrace 2).1 = tinyFirst := by
  exact ⟨by decide, rfl⟩

/-- Apply the general fresh-row theorem to the nonempty route producer. -/
theorem tiny_route_span_from_rows :
    SpanChargedOnce 1 3 tinyStart tinyFirst := by
  have h := single_traversal_span routeRows tinyRouteTrace (fun _ => 0) 2 3
    (fun _ _ => rfl) (fun t _ => tiny_route_allowed t)
    (by rw [tiny_route_two_moves.1]; exact Nat.le_refl _)
  exact h


theorem tiny_weights :
    w tinyStart = 4 ∧ w tinyFirst = 2 ∧ w tinyRepeat = 2 := by
  decide


theorem tiny_no_refill :
    OnlySpends tinyStart tinyFirst ∧ OnlySpends tinyFirst tinyRepeat := by
  exact ⟨clearWord_only tinyStart tinyRoute,
    clearWord_only tinyFirst tinyRoute⟩


theorem tiny_fresh_traversal : SpanChargedOnce 1 3 tinyStart tinyFirst := by
  change 3 ≤ 1 * (w tinyStart - w tinyFirst + 1)
  rw [tiny_weights.1, tiny_weights.2.1]
  exact Nat.le_refl _


theorem tiny_replay_refutes : ¬ SpanChargedOnce 1 3 tinyFirst tinyRepeat := by
  intro h
  change 3 ≤ 1 * (w tinyFirst - w tinyRepeat + 1) at h
  rw [tiny_weights.2.1, tiny_weights.2.2] at h
  omega


theorem tiny_replay_two_moves_refutes :
    ¬ SpanChargedOnce 1 2 tinyFirst tinyRepeat := by
  intro h
  change 2 ≤ 1 * (w tinyFirst - w tinyRepeat + 1) at h
  rw [tiny_weights.2.1, tiny_weights.2.2] at h
  omega


/-- The fixed geometric span of the whole episode is STILL paid. -/
theorem tiny_whole_span : SpanChargedOnce 1 3 tinyStart tinyRepeat := by
  exact fixed_span_survives_retries 1 3 tinyStart tinyFirst tinyRepeat
    tiny_fresh_traversal tiny_no_refill.2


/-- Four transported MOVEs, not the unchanged geometric distance three. -/
theorem tiny_accumulated_span_refutes :
    ¬ SpanChargedOnce 1 4 tinyStart tinyRepeat := by
  intro h
  change 4 ≤ 1 * (w tinyStart - w tinyRepeat + 1) at h
  rw [tiny_weights.1, tiny_weights.2.2] at h
  omega


theorem tiny_refill_forbidden : ¬ OnlySpends tinyFirst tinyStart := by
  intro h
  have hi := h (2 : Fin 4) rfl
  change false = true at hi
  cases hi


/-! Literal projection of the successful aligned follower-MOVE assignments.
No full dispatcher equality or physical execution is asserted by this model. -/


def idleFollower : Cell 1 where
  leader := false
  shield := false
  signal_B := 0
  bullet := 0
  label := 0


def incomingFollower : Cell 1 := { idleFollower with bullet := 2 }


def alignedMoveProjection (l r : Cell 1) : Cell 1 × Cell 1 :=
  ({ l with bullet := r.bullet, signal_B := 0 }, { r with bullet := 0 })


theorem aligned_move_can_clear_zero :
    idleFollower.leader = false ∧
    0 < incomingFollower.bullet.val ∧
    incomingFollower.label = (0 : Fin 1) ∧
    idleFollower.signal_B = (0 : Fin 2) ∧
    (alignedMoveProjection idleFollower incomingFollower).1.signal_B = 0 ∧
    (alignedMoveProjection idleFollower incomingFollower).1.bullet = 2 ∧
    (alignedMoveProjection idleFollower incomingFollower).2.bullet = 0 := by
  decide


/-! Correct cut criterion. A local absorption drop and a globally reusable
cut phase are different statements. No fresh phase or credit reset occurs here. -/


theorem phase_prefix_le (phase : Nat → Nat) :
    ∀ T : Nat, (∀ t, t < T → phase (t + 1) ≤ phase t) →
      phase T ≤ phase 0 := by
  intro T
  induction T with
  | zero =>
      intro _hrow
      exact Nat.le_refl _
  | succ T ih =>
      intro hrow
      exact Nat.le_trans (hrow T (by omega))
        (ih (fun t ht => hrow t (by omega)))


theorem cut_phase_drop (phase : Nat → Nat) (T : Nat)
    (hprefix : ∀ t, t < T → phase (t + 1) ≤ phase t)
    (hlast : phase (T + 1) < phase T) : phase (T + 1) < phase 0 := by
  have hp := phase_prefix_le phase T hprefix
  omega


/-- Applies in particular to any leader-count phase on a leader-preserving loss. -/
theorem unchanged_phase_not_drop (beforePhase afterPhase : Nat)
    (h : afterPhase = beforePhase) : ¬ afterPhase < beforePhase := by
  rw [h]
  exact Nat.lt_irrefl _


/-- Returning to the old phase after a strict drop must violate nonincrease. -/
theorem absorption_return_obstruction (beforePhase absorbedPhase : Nat)
    (hdrop : absorbedPhase < beforePhase) :
    ¬ beforePhase ≤ absorbedPhase := by
  omega


theorem local_drop_not_global_drop : (0 : Nat) < 1 ∧ ¬ ((1 : Nat) < 1) := by
  decide


/-- Even supplying a genuine strict cut-phase drop would not refill credits. -/
theorem phase_drop_does_not_repair_credits :
    (0 : Nat) < 1 ∧ ¬ SpanChargedOnce 1 3 tinyFirst tinyRepeat := by
  exact ⟨by decide, tiny_replay_refutes⟩


/-- Conditional episode-boundary statement, not a new K2 instantiation.
Instantiate phase t with ONE global phase evaluated at trace t. The prefix
includes every re-arm row assigned to this episode. Allowed must hold on the
actual trace, not merely at an independently reinitialized attempt seed. -/
theorem cut_hstep_from_fresh_moves {S : Type} {n : Nat}
    {step : S → Fin n → S} {credits : S → Credits n}
    {destination : S → Fin n → Option (Fin n)} {Allowed : S → Prop}
    (H : MoveCreditRows step credits destination Allowed)
    (trace : Nat → S) (edge : Nat → Fin n) (T d tariff cost : Nat)
    (hnext : ∀ t, t < T + 1 → trace (t + 1) = step (trace t) (edge t))
    (hsafe : ∀ t, t < T + 1 → Allowed (trace t))
    (hd : d ≤ moveCount (fun t => destination (trace t) (edge t)) (T + 1) + 1)
    (hlocal : cost ≤ tariff * n * (2 * d)) (phase : Nat → Nat)
    (hprefix : ∀ t, t < T → phase (t + 1) ≤ phase t)
    (hlast : phase (T + 1) < phase T) :
    w (credits (trace (T + 1))) ≤ w (credits (trace 0)) ∧
    phase (T + 1) < phase 0 ∧
    cost ≤ ((2 * tariff) * n) *
      ((w (credits (trace 0)) - w (credits (trace (T + 1)))) + 1) := by
  have hb := fresh_trace_budget H trace edge (T + 1) hnext hsafe
  have hs := single_traversal_span H trace edge (T + 1) d hnext hsafe hd
  have hc := episode_cost_adapter tariff 1 d cost
    (credits (trace 0)) (credits (trace (T + 1))) hlocal hs
  refine ⟨by omega, cut_phase_drop phase T hprefix hlast, ?_⟩
  simpa only [Nat.mul_one] using hc


end SpanChargedOnceAudit


#print axioms SpanChargedOnceAudit.fresh_spend_weight
#print axioms SpanChargedOnceAudit.move_row_budget
#print axioms SpanChargedOnceAudit.no_fresh_row_at_spent_destination
#print axioms SpanChargedOnceAudit.row_telescope
#print axioms SpanChargedOnceAudit.fresh_trace_budget
#print axioms SpanChargedOnceAudit.single_traversal_span
#print axioms SpanChargedOnceAudit.fixed_span_survives_retries
#print axioms SpanChargedOnceAudit.span_capacity
#print axioms SpanChargedOnceAudit.clearAt_only
#print axioms SpanChargedOnceAudit.clearAt_destination
#print axioms SpanChargedOnceAudit.clearAt_of_spent
#print axioms SpanChargedOnceAudit.clearAt_loses_credit_iff
#print axioms SpanChargedOnceAudit.clearWord_only
#print axioms SpanChargedOnceAudit.routeRows
#print axioms SpanChargedOnceAudit.routeAllowed_step
#print axioms SpanChargedOnceAudit.tiny_route_initial_allowed
#print axioms SpanChargedOnceAudit.tiny_route_allowed
#print axioms SpanChargedOnceAudit.tiny_route_two_moves
#print axioms SpanChargedOnceAudit.tiny_route_span_from_rows
#print axioms SpanChargedOnceAudit.clearWord_exhausted
#print axioms SpanChargedOnceAudit.exhausted_traversal_refutes
#print axioms SpanChargedOnceAudit.no_uniform_B_exhausted
#print axioms SpanChargedOnceAudit.repeated_mask_refutes
#print axioms SpanChargedOnceAudit.tiny_weights
#print axioms SpanChargedOnceAudit.tiny_no_refill
#print axioms SpanChargedOnceAudit.tiny_fresh_traversal
#print axioms SpanChargedOnceAudit.tiny_replay_refutes
#print axioms SpanChargedOnceAudit.tiny_replay_two_moves_refutes
#print axioms SpanChargedOnceAudit.tiny_whole_span
#print axioms SpanChargedOnceAudit.tiny_accumulated_span_refutes
#print axioms SpanChargedOnceAudit.tiny_refill_forbidden
#print axioms SpanChargedOnceAudit.aligned_move_can_clear_zero
#print axioms SpanChargedOnceAudit.phase_prefix_le
#print axioms SpanChargedOnceAudit.cut_phase_drop
#print axioms SpanChargedOnceAudit.unchanged_phase_not_drop
#print axioms SpanChargedOnceAudit.absorption_return_obstruction
#print axioms SpanChargedOnceAudit.local_drop_not_global_drop
#print axioms SpanChargedOnceAudit.phase_drop_does_not_repair_credits
#print axioms SpanChargedOnceAudit.cut_hstep_from_fresh_moves
