import Leader.L3.Grant.Drain

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Proof-only persistent grant labels for the exact no-new-grant reference.
No protocol field is modified.  The native zero-corridor tests are
observers of the source GrantDrainState, not replacement dynamics.

The syntactic quota bounds below are proved.  Their semantic adequacy
along every reachable execution is the named, UNPROVED obligation
GrantDrainLedgerNoExhaustion.
-/

/-- Ordered marks: unmarked < weak < strong < terminal.  Terminal
means either held/leader status or an already retired identity. -/
inductive GrantDrainMark
  | unmarked
  | weak
  | strong
  | terminal
  deriving BEq, DecidableEq, Repr

def grantDrainMarkRank : GrantDrainMark → Nat
  | .unmarked => 0
  | .weak => 1
  | .strong => 2
  | .terminal => 3

def grantDrainMarkJoin (a b : GrantDrainMark) : GrantDrainMark :=
  if grantDrainMarkRank a ≤ grantDrainMarkRank b then b else a

theorem grantDrainMarkRank_le_join (a b : GrantDrainMark) :
    grantDrainMarkRank a ≤
      grantDrainMarkRank (grantDrainMarkJoin a b) := by
  unfold grantDrainMarkJoin
  split
  · assumption
  · exact Nat.le_refl _

theorem grantDrainMarkJoin_terminal_right (m : GrantDrainMark) :
    grantDrainMarkJoin m .terminal = .terminal := by
  cases m <;> rfl

/-- One label is one initial identity; several labels may share a host.
None means retired, never a second physical grant. -/
structure GrantDrainLedgerLabel (n : Nat) where
  identity : Fin n
  host : Option (Fin n)
  mark : GrantDrainMark
  remaining : Nat

/-- The closed interval [p,g) in (D.1), enumerated backwards from g:
g-1, ..., p. The current host g is NOT tested for signal zero. -/
def grantDrainLedgerCorridor {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : Bool :=
  let d := grantDrainLeftLeaderDistance ring s.native g
  let p := PPL.shiftLeft ring g d
  (s.native p).l &&
    (List.range d).all (fun k =>
      !(s.native (PPL.shiftLeft ring g (k + 1))).sg)

/-- The protected (shielded) zero-corridor of D.1. -/
def grantDrainLedgerStrongLock {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : Bool :=
  grantDrainLedgerCorridor ring s g &&
    (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).sh

/-- The unshielded source with the same zero-corridor. -/
def grantDrainLedgerWeakLock {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : Bool :=
  grantDrainLedgerCorridor ring s g &&
    !(s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).sh

/-- Observe terminal first (OLD/POST HOLD, native leader), then locks.
For an absent host the retired label is terminal. -/
def grantDrainLedgerObservedMark {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (host : Option (Fin n)) : GrantDrainMark :=
  match host with
  | none => .terminal
  | some g =>
      if s.request g && s.grant g then .terminal
      else if (s.native g).l then .terminal
      else if grantDrainLedgerStrongLock ring s g then .strong
      else if grantDrainLedgerWeakLock ring s g then .weak
      else .unmarked

def grantDrainLedgerHeld {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch)
    (host : Option (Fin n)) : Bool :=
  match host with
  | none => false
  | some g => s.request g && s.grant g

/-- The literal token row of grantDrainStep, factored for observers. -/
def grantDrainLedgerRow {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    TokPair × TokPair :=
  grantDrainTokenRow
    (s.request e) (s.grant e)
    (s.request (ring.rightNeighbor e))
    (s.grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring s e e).l
    (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
    (freshRequest s e) (grantDrainSelect ring s e)

/-- Source Y = responder.  some true: old Y stayed at Y under HOLD;
some false: its grant moved Y to X.  The output row is authoritative.
F0 consumes/reserves X, so an unheld Y does NOT move into X on F0. -/
def grantDrainLedgerYSource
    (ry gy lx ly : Bool) (fire : GrantDrainFire)
    (row : TokPair × TokPair) : Option Bool :=
  if !gy then none
  else if row.2.grant then some true
  else if fire == .none && !lx && !ly && !ry && row.1.grant
    then some false
  else none

/-- If Y travels to X, it has disappeared at Y and exists at X:
no copy is made.  This does not assert that two labels cannot merge. -/
theorem grantDrainLedgerYSource_move_sound
    (ry gy lx ly : Bool) (fire : GrantDrainFire)
    (row : TokPair × TokPair)
    (h : grantDrainLedgerYSource ry gy lx ly fire row = some false) :
    row.1.grant = true ∧ row.2.grant = false := by
  cases hr : ry <;> cases hg : gy <;>
    cases hlx : lx <;> cases hly : ly <;>
    cases hf : fire <;>
    cases hx : row.1.grant <;> cases hy : row.2.grant <;>
    simp [grantDrainLedgerYSource, hr, hg, hlx, hly, hf, hx, hy] at h ⊢

/-- Per-identity host transport on the OLD state and revealed edge.
X survives only if its OLD grant survives.  Y can stay, move to X,
or retire.  Other sites are framed.  A host is never forked. -/
def grantDrainLedgerHost {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (oldHost : Option (Fin n)) : Option (Fin n) :=
  match oldHost with
  | none => none
  | some g =>
      if g = e then
        if s.grant e && (grantDrainLedgerRow ring freshRequest s e).1.grant
        then some e else none
      else if g = ring.rightNeighbor e then
        match grantDrainLedgerYSource
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          (grantDrainNativeNext ring s e e).l
          (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
          (grantDrainSelect ring s e)
          (grantDrainLedgerRow ring freshRequest s e) with
        | some true => some (ring.rightNeighbor e)
        | some false => some e
        | none => none
      else some g

/-- Extra promotion for a Y label that merges into a preexisting
locked/held X grant.  The old X lock is visible without accessing
any other label's proof-only mark. -/
def grantDrainLedgerCoalesceMark {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) (oldHost newHost : Option (Fin n)) :
    GrantDrainMark :=
  if oldHost = some (ring.rightNeighbor e) ∧
      newHost = some e ∧ s.grant e = true then
    grantDrainLedgerObservedMark ring s (some e)
  else .unmarked

/-- Persistent promotion: old mark, old host status, target host's
old lock on coalescence, and post-step host status are joined.
In particular a weak source's death can be observed as a NEW
strong corridor; HOLD is observed as terminal on the incoming edge. -/
def grantDrainLedgerMarkNext {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) : GrantDrainMark :=
  grantDrainMarkJoin label.mark
    (grantDrainMarkJoin
      (grantDrainLedgerObservedMark ring s label.host)
      (grantDrainMarkJoin
        (grantDrainLedgerCoalesceMark ring s e label.host
          (grantDrainLedgerHost ring freshRequest s e label.host))
        (grantDrainLedgerObservedMark ring
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerHost ring freshRequest s e label.host))))

/-- A request-bearing host nominates its outgoing edge; otherwise its
incoming edge.  This is computed BEFORE the scheduler step. -/
def grantDrainLedgerNominatedHit {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) (host : Option (Fin n)) : Bool :=
  match host with
  | none => false
  | some g =>
      if s.request g then decide (e = g)
      else decide (ring.rightNeighbor e = g)

/-- Caps for the remaining nominated hits.  Weak: 2n, strong: n.
Terminal HOLD: one hit (capped at n even for degenerate n);
terminal native leader / surviving formerly terminal: n.
Retired labels have zero quota, independently of this function. -/
def grantDrainLedgerQuotaCap
    (n : Nat) (mark : GrantDrainMark) (held : Bool) : Nat :=
  match mark with
  | .unmarked => 0
  | .weak => 2 * n
  | .strong => n
  | .terminal => if held then min 1 n else n

/-- Seed only on first marking.  Old marked labels spend one unit per
old-state nominated hit; min prevents a newly detected lock, HOLD or
coalescence from resetting a used budget.  This is ACCOUNTING, not
yet the geometric proof that the budget is sufficient. -/
def grantDrainLedgerRemainingNext (n : Nat)
    (old : GrantDrainLedgerLabel n)
    (newHost : Option (Fin n))
    (newMark : GrantDrainMark)
    (nominatedHit held : Bool) : Nat :=
  match newHost with
  | none => 0
  | some _ =>
      min
        (if old.mark = .unmarked then
          grantDrainLedgerQuotaCap n newMark held
         else old.remaining - (if nominatedHit then 1 else 0))
        (grantDrainLedgerQuotaCap n newMark held)

/-- Entire ghost step, on the same source grantDrainStep as BANK/SMALL
must refine.  No alteration to GrantDrainState or token semantics. -/
def grantDrainLedgerStep {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) : GrantDrainLedgerLabel n :=
  { label with
    host := grantDrainLedgerHost ring freshRequest s e label.host
    mark := grantDrainLedgerMarkNext ring freshRequest updateScratch s e label
    remaining :=
      grantDrainLedgerRemainingNext n label
        (grantDrainLedgerHost ring freshRequest s e label.host)
        (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label)
        (grantDrainLedgerNominatedHit ring s e label.host)
        (grantDrainLedgerHeld
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerHost ring freshRequest s e label.host)) }

/-- Exact, source-row HOLD regression:
old Y=(request=true,grant=true), X empty, no leader sink,
no FIRE, no fresh request.  The grant remains at Y. -/
theorem grantDrainLedgerHeldIncoming_row :
    (grantDrainTokenRow false false true true false false false .none).2.req =
        true ∧
    (grantDrainTokenRow false false true true false false false .none).2.grant =
        true ∧
    (grantDrainTokenRow false false true true false false false .none).1.grant =
        false := by
  unfold grantDrainTokenRow
  decide

theorem grantDrainLedgerMarkNext_of_post_held
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hHost : grantDrainLedgerHost ring freshRequest s e label.host = some g)
    (hReq : (grantDrainStep ring freshRequest updateScratch s e).request g = true)
    (hGrant : (grantDrainStep ring freshRequest updateScratch s e).grant g = true) :
    grantDrainLedgerMarkNext ring freshRequest updateScratch s e label =
      .terminal := by
  have hObs :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (some g) = .terminal := by
    simp [grantDrainLedgerObservedMark, hReq, hGrant]
  unfold grantDrainLedgerMarkNext
  rw [hHost, hObs]
  simp only [grantDrainMarkJoin_terminal_right]

/-- Full parameterized incoming-HOLD regression on grantDrainStep.
The post-E/canonical-birth leader bits and FIRE are explicitly fixed,
so the displayed old-token row is literally the row above. -/
theorem grantDrainLedgerHeldIncoming_promotes
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hne : e ≠ ring.rightNeighbor e)
    (hHost : label.host = some (ring.rightNeighbor e))
    (hRX : s.request e = false)
    (hGX : s.grant e = false)
    (hRY : s.request (ring.rightNeighbor e) = true)
    (hGY : s.grant (ring.rightNeighbor e) = true)
    (hLX : (grantDrainNativeNext ring s e e).l = false)
    (hLY : (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l = false)
    (hFresh : freshRequest s e = false)
    (hFire : grantDrainSelect ring s e = .none) :
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
      .terminal := by
  have hRaw :
      grantDrainLedgerRow ring freshRequest s e =
        grantDrainTokenRow false false true true false false false .none := by
    unfold grantDrainLedgerRow
    rw [hRX, hGX, hRY, hGY, hLX, hLY, hFresh, hFire]
  have hRowReq :
      (grantDrainLedgerRow ring freshRequest s e).2.req = true := by
    rw [hRaw]
    exact grantDrainLedgerHeldIncoming_row.1
  have hRowGrant :
      (grantDrainLedgerRow ring freshRequest s e).2.grant = true := by
    rw [hRaw]
    exact grantDrainLedgerHeldIncoming_row.2.1
  have hYStays :
      grantDrainLedgerYSource
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring s e e).l
        (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
        (grantDrainSelect ring s e)
        (grantDrainLedgerRow ring freshRequest s e) = some true := by
    simp [grantDrainLedgerYSource, hGY, hRowGrant]
  have hNewHost :
      grantDrainLedgerHost ring freshRequest s e label.host =
        some (ring.rightNeighbor e) := by
    simp [grantDrainLedgerHost, hHost, Ne.symm hne, hYStays]
  have hPostReq :
      (grantDrainStep ring freshRequest updateScratch s e).request
        (ring.rightNeighbor e) = true := by
    change (if ring.rightNeighbor e = e then
        (grantDrainLedgerRow ring freshRequest s e).1.req
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (grantDrainLedgerRow ring freshRequest s e).2.req
      else s.request (ring.rightNeighbor e)) = true
    simp [Ne.symm hne, hRowReq]
  have hPostGrant :
      (grantDrainStep ring freshRequest updateScratch s e).grant
        (ring.rightNeighbor e) = true := by
    change (if ring.rightNeighbor e = e then
        (grantDrainLedgerRow ring freshRequest s e).1.grant
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (grantDrainLedgerRow ring freshRequest s e).2.grant
      else s.grant (ring.rightNeighbor e)) = true
    simp [Ne.symm hne, hRowGrant]
  change grantDrainLedgerMarkNext ring freshRequest updateScratch s e label =
    .terminal
  exact grantDrainLedgerMarkNext_of_post_held
    ring freshRequest updateScratch s e (ring.rightNeighbor e)
    label hNewHost hPostReq hPostGrant

/-- The mark is never demoted, including after leader deletion. -/
theorem grantDrainLedgerStep_mark_monotone
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) :
    grantDrainMarkRank label.mark ≤
      grantDrainMarkRank
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark := by
  change grantDrainMarkRank label.mark ≤
    grantDrainMarkRank
      (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label)
  unfold grantDrainLedgerMarkNext
  exact grantDrainMarkRank_le_join label.mark _

/-- Retirement cannot regenerate a host. -/
theorem grantDrainLedgerStep_retired_absorbing
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (h : label.host = none) :
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
      none := by
  change grantDrainLedgerHost ring freshRequest s e label.host = none
  rw [h]
  rfl

/-- A marked quota cap is at most 2n even without geometric claims. -/
theorem grantDrainLedgerQuotaCap_le_double
    (n : Nat) (m : GrantDrainMark) (held : Bool) :
    grantDrainLedgerQuotaCap n m held ≤ 2 * n := by
  cases m <;> cases held <;>
    simp [grantDrainLedgerQuotaCap] <;> omega

/-- A strong or terminal cap is at most n. -/
theorem grantDrainLedgerQuotaCap_le_strong
    (n : Nat) (m : GrantDrainMark) (held : Bool)
    (h : 2 ≤ grantDrainMarkRank m) :
    grantDrainLedgerQuotaCap n m held ≤ n := by
  cases m <;> cases held <;>
    simp [grantDrainLedgerQuotaCap, grantDrainMarkRank] at * <;> omega

theorem grantDrainLedgerRemainingNext_le_cap
    (n : Nat) (label : GrantDrainLedgerLabel n)
    (host : Option (Fin n)) (m : GrantDrainMark)
    (hit held : Bool) :
    grantDrainLedgerRemainingNext n label host m hit held ≤
      grantDrainLedgerQuotaCap n m held := by
  cases host with
  | none =>
      simp [grantDrainLedgerRemainingNext]
  | some g =>
      change min
        (if label.mark = .unmarked then grantDrainLedgerQuotaCap n m held
         else label.remaining - (if hit then 1 else 0))
        (grantDrainLedgerQuotaCap n m held) ≤
          grantDrainLedgerQuotaCap n m held
      exact Nat.min_le_right _ _

theorem grantDrainLedgerRemainingNext_le_old_of_marked
    (n : Nat) (label : GrantDrainLedgerLabel n)
    (host : Option (Fin n)) (m : GrantDrainMark)
    (hit held : Bool) (h : label.mark ≠ .unmarked) :
    grantDrainLedgerRemainingNext n label host m hit held ≤
      label.remaining := by
  cases host with
  | none =>
      simp [grantDrainLedgerRemainingNext]
  | some g =>
      change min
        (if label.mark = .unmarked then grantDrainLedgerQuotaCap n m held
         else label.remaining - (if hit then 1 else 0))
        (grantDrainLedgerQuotaCap n m held) ≤ label.remaining
      rw [if_neg h]
      exact Nat.le_trans (Nat.min_le_left _ _)
        (Nat.sub_le label.remaining (if hit then 1 else 0))

/-- Syntactic invariant: every NEXT label has at most 2n quota. -/
theorem grantDrainLedgerStep_quota_le_double
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) :
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).remaining ≤
      2 * n := by
  change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring freshRequest s e label.host)
      (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerHost ring freshRequest s e label.host)) ≤ 2 * n
  exact
    Nat.le_trans (grantDrainLedgerRemainingNext_le_cap n label _ _ _ _)
      (grantDrainLedgerQuotaCap_le_double n _ _)

/-- Syntactic invariant: strong/terminal NEXT labels have <= n quota. -/
theorem grantDrainLedgerStep_quota_le_strong
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (h : 2 ≤ grantDrainMarkRank
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark) :
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).remaining ≤
      n := by
  change 2 ≤ grantDrainMarkRank
    (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label) at h
  change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring freshRequest s e label.host)
      (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerHost ring freshRequest s e label.host)) ≤ n
  exact
    Nat.le_trans (grantDrainLedgerRemainingNext_le_cap n label _ _ _ _)
      (grantDrainLedgerQuotaCap_le_strong n _ _ h)

/-- Already-marked remaining counters never increase. -/
theorem grantDrainLedgerStep_remaining_nonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (h : label.mark ≠ .unmarked) :
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).remaining ≤
      label.remaining := by
  change grantDrainLedgerRemainingNext n label
      (grantDrainLedgerHost ring freshRequest s e label.host)
      (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerHost ring freshRequest s e label.host)) ≤
    label.remaining
  exact grantDrainLedgerRemainingNext_le_old_of_marked n label _ _ _ _ h

/-- Distinct initially occupied physical sites receive distinct IDs. -/
def grantDrainLedgerInitial {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (i : Fin n) : GrantDrainLedgerLabel n :=
  let host := if s.grant i then some i else none
  let mark := grantDrainLedgerObservedMark ring s host
  { identity := i
    host := host
    mark := mark
    remaining :=
      if s.grant i then
        grantDrainLedgerQuotaCap n mark (grantDrainLedgerHeld s host)
      else 0 }

/-- A scheduler word run on the product of source state and ONE ghost.
The source does not depend on the ghost. -/
def grantDrainLedgerRun {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s0 : GrantDrainState n Scratch)
    (label0 : GrantDrainLedgerLabel n)
    (edges : List (Fin n)) :
    GrantDrainState n Scratch × GrantDrainLedgerLabel n :=
  edges.foldl
    (fun acc e =>
      (grantDrainStep ring freshRequest updateScratch acc.1 e,
       grantDrainLedgerStep ring freshRequest updateScratch acc.1 e acc.2))
    (s0, label0)

/-- FIRST MISSING SEMANTIC FACT, stated but NOT proved:
from a peaceful rooted cut, a live ever-marked label cannot exhaust
its numerical quota before retirement.  Establishing this needs the
D.1 protected-corridor preservation, the one-time weak-source death
to strong-corridor conversion, the native-leader death case, and the
coalescence lock inheritance.  Numeric min-caps alone prove none of it. -/
def GrantDrainLedgerNoExhaustion {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s0 : GrantDrainState n Scratch) : Prop :=
  PPlus ring s0.native →
    ∀ (i : Fin n) (edges : List (Fin n)),
      s0.grant i = true →
      (grantDrainLedgerRun ring freshRequest updateScratch s0
        (grantDrainLedgerInitial ring s0 i) edges).2.host ≠ none →
      (grantDrainLedgerRun ring freshRequest updateScratch s0
        (grantDrainLedgerInitial ring s0 i) edges).2.mark ≠ .unmarked →
      0 < (grantDrainLedgerRun ring freshRequest updateScratch s0
        (grantDrainLedgerInitial ring s0 i) edges).2.remaining

end L3
/-!
Strong-lock nominated-hit quota, APPEND ONLY.

The exact source potential is the counterclockwise nearest-leader
distance d from GrantDrain.lean.  The normalized version below is
always a positive natural number at a live host and is <= n.  It
agrees with d whenever 1 <= d <= n (as in a rooted ring).

This section proves arithmetic quota preservation, and lifts it to
arbitrary source runs CONDITIONALLY on a named physical corridor
step theorem.  It does NOT prove that theorem from nativeE, FIRE,
HOLD, and grantDrainStep; therefore it does not claim an unconditional
strong portion of GrantDrainLedgerNoExhaustion.

Important boundary semantics: on x=g-1 -> y=g, an OLD zero signal
at x may become one.  If Y's unheld grant survives, it moves to X
on that same service. X then becomes the new excluded endpoint of
the shortened corridor.  Static preservation of every OLD signal
inside [p,g) is false.  The dynamic [p,g') corridor is the invariant.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A bounded, positive version of the protected-source distance.
For a live host g and 1 <= d <= n this is EXACTLY
grantDrainLeftLeaderDistance ring s.native g.
The normalization prevents a zero potential at a live host and keeps
the inequality <= n independent of the unproved geometry lemma. -/
def grantDrainStrongProtectedDistance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (host : Option (Fin n)) : Nat :=
  match host with
  | none => 0
  | some g =>
      Nat.succ (min (n - 1)
        (grantDrainLeftLeaderDistance ring s.native g - 1))

theorem grantDrainStrongProtectedDistance_none
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) :
    grantDrainStrongProtectedDistance ring s none = 0 := by
  rfl

theorem grantDrainStrongProtectedDistance_some_pos
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (g : Fin n) :
    0 < grantDrainStrongProtectedDistance ring s (some g) := by
  change 0 < Nat.succ
    (min (n - 1) (grantDrainLeftLeaderDistance ring s.native g - 1))
  exact Nat.zero_lt_succ _

theorem grantDrainStrongProtectedDistance_le_n
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (host : Option (Fin n)) :
    grantDrainStrongProtectedDistance ring s host ≤ n := by
  cases host with
  | none =>
      exact Nat.zero_le n
  | some g =>
      change Nat.succ
        (min (n - 1) (grantDrainLeftLeaderDistance ring s.native g - 1)) ≤ n
      have hm :
          min (n - 1) (grantDrainLeftLeaderDistance ring s.native g - 1) ≤
            n - 1 := Nat.min_le_left _ _
      have hgn : g.val < n := g.isLt
      omega

/-- The exact distance identity, given its natural 1..n scan range.
The scan-range theorem for grantDrainLeftLeaderDistance can be proved
separately using List.find? membership. -/
theorem grantDrainStrongProtectedDistance_eq_raw
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (g : Fin n)
    (hpos : 0 < grantDrainLeftLeaderDistance ring s.native g)
    (hle : grantDrainLeftLeaderDistance ring s.native g ≤ n) :
    grantDrainStrongProtectedDistance ring s (some g) =
      grantDrainLeftLeaderDistance ring s.native g := by
  change Nat.succ
    (min (n - 1) (grantDrainLeftLeaderDistance ring s.native g - 1)) =
      grantDrainLeftLeaderDistance ring s.native g
  have hm :
      grantDrainLeftLeaderDistance ring s.native g - 1 ≤ n - 1 := by
    omega
  rw [Nat.min_eq_right hm]
  omega

/-- Exact live follower strong condition at the ACTUAL old physical
state, not merely a persistent ghost mark. -/
def GrantDrainStrongPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) : Prop :=
  ∃ g : Fin n,
    label.host = some g ∧
    label.mark = .strong ∧
    s.grant g = true ∧
    s.request g = false ∧
    (s.native g).l = false ∧
    grantDrainLedgerStrongLock ring s g = true

/-- FIRST MISSING NATIVE/ROW FACT.

For a presently strong-locked live grant, a surviving next label that
is still marked strong must have the NEW moving zero corridor.  Its
new protected-source distance is nonincreasing on all edges, and
drops by >= 1 on a nominated incoming hit.

The source theorem must be derived from:
  * no signal enters the moving corridor behind the grant;
  * shielded signal-zero source survives incoming LIVE;
  * intervening canonical birth supplies a CLOSER protected source;
  * Y-to-X transport or retirement on a nominated hit;
  * OLD HOLD and native leader sinks cause terminal marking;
  * coalescence inherits the surviving protected host.
This is a Prop, NOT a theorem or an additional axiom. -/
def GrantDrainStrongCorridorGeometry
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    Prop :=
  ∀ (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n),
    PPlus ring s.native →
    GrantDrainStrongPhysical ring s label →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠ none →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
      .strong →
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
    (if grantDrainLedgerNominatedHit ring s e label.host then
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host + 1 ≤
      grantDrainStrongProtectedDistance ring s label.host
    else
      grantDrainStrongProtectedDistance ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≤
      grantDrainStrongProtectedDistance ring s label.host)

/-- Numerically, a one-hit distance drop pays exactly the decrement
of a marked counter; on a non-hit, nonincrease pays zero. -/
theorem grantDrainStrongBudgetAlgebra
    (n oldDistance newDistance oldRemaining : Nat)
    (hit : Bool)
    (hBudget : oldDistance ≤ oldRemaining)
    (hCap : newDistance ≤ n)
    (hProgress :
      if hit then newDistance + 1 ≤ oldDistance
      else newDistance ≤ oldDistance) :
    newDistance ≤
      min (oldRemaining - (if hit then 1 else 0)) n := by
  cases hit with
  | false =>
      have hp : newDistance ≤ oldDistance := by
        simpa using hProgress
      exact Nat.le_min.mpr ⟨by
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at *
        omega, hCap⟩
  | true =>
      have hp : newDistance + 1 ≤ oldDistance := by
        simpa using hProgress
      exact Nat.le_min.mpr ⟨by
        simp only [↓reduceIte] at *
        omega, hCap⟩

/-- Unfold the already-defined remaining update in its
strong-to-strong, live-to-live branch. No fresh n-credit is allocated. -/
theorem grantDrainStrongRemainingFormula
    (n : Nat)
    (label : GrantDrainLedgerLabel n)
    (newHost : Option (Fin n))
    (hit held : Bool)
    (hMark : label.mark = .strong)
    (hLive : newHost ≠ none) :
    grantDrainLedgerRemainingNext n label newHost .strong hit held =
      min (label.remaining - (if hit then 1 else 0)) n := by
  cases hh : newHost with
  | none =>
      exact False.elim (hLive hh)
  | some g =>
      simp [grantDrainLedgerRemainingNext, hh, hMark,
        grantDrainLedgerQuotaCap]

/-- Conditional strong-to-strong quota step on the LITERAL source
grantDrainStep, not on an abstract invented Markov model.
The ONLY unproved input is the native/row geometry statement above. -/
theorem grantDrainStrongStepBudgetOfGeometry
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (hGeometry :
      GrantDrainStrongCorridorGeometry ring freshRequest updateScratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hBudget :
      grantDrainStrongProtectedDistance ring s label.host ≤
        label.remaining)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠
        none)
    (hMark :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
        .strong) :
    grantDrainStrongProtectedDistance ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≤
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).remaining := by
  have hDrift :=
    (hGeometry s e label hP hPhysical hLive hMark).2
  have hCap :=
    grantDrainStrongProtectedDistance_le_n ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host
  have hOldMark : label.mark = .strong := by
    rcases hPhysical with ⟨g, hg, hm, hGrant, hRequest, hLeader, hLock⟩
    exact hm
  have hNextMark :
      grantDrainLedgerMarkNext ring freshRequest updateScratch s e label =
        .strong := by
    exact hMark
  have hNextHost :
      grantDrainLedgerHost ring freshRequest s e label.host ≠ none := by
    exact hLive
  have hFormula :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).remaining =
        min (label.remaining -
          (if grantDrainLedgerNominatedHit ring s e label.host then 1 else 0))
          n := by
    change grantDrainLedgerRemainingNext n label
        (grantDrainLedgerHost ring freshRequest s e label.host)
        (grantDrainLedgerMarkNext ring freshRequest updateScratch s e label)
        (grantDrainLedgerNominatedHit ring s e label.host)
        (grantDrainLedgerHeld
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerHost ring freshRequest s e label.host)) =
        min (label.remaining -
          (if grantDrainLedgerNominatedHit ring s e label.host then 1 else 0))
          n
    rw [hNextMark]
    exact grantDrainStrongRemainingFormula n label
      (grantDrainLedgerHost ring freshRequest s e label.host)
      (grantDrainLedgerNominatedHit ring s e label.host)
      (grantDrainLedgerHeld
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerHost ring freshRequest s e label.host))
      hOldMark hNextHost
  have hNumerical :=
    grantDrainStrongBudgetAlgebra n
      (grantDrainStrongProtectedDistance ring s label.host)
      (grantDrainStrongProtectedDistance ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host)
      label.remaining
      (grantDrainLedgerNominatedHit ring s e label.host)
      hBudget hCap hDrift
  rw [← hFormula] at hNumerical
  exact hNumerical

/-- A purely local four-bit native example: the old x signal is zero
and the old y signal is one. E sets x's signal to one. If the
unheld old grant at y moves to x, the newly nonzero signal is at
the NEW excluded endpoint, not inside its NEW corridor. -/
private def grantDrainStrongBoundaryLeft : CertNative :=
  { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def grantDrainStrongBoundaryRight : CertNative :=
  { l := false, b := (0 : Fin 3), sh := false, sg := true }

/-- On this actual native E row, the OLD x corridor site becomes S=1.
This disproves the overly strong STATIC-corridor wording. -/
theorem grantDrainStrongBoundaryNativeRow :
    (certLiteralEPair
      grantDrainStrongBoundaryLeft grantDrainStrongBoundaryRight).1.sg =
        true ∧
    (certLiteralEPair
      grantDrainStrongBoundaryLeft grantDrainStrongBoundaryRight).2.sg =
        true := by
  unfold grantDrainStrongBoundaryLeft grantDrainStrongBoundaryRight
    certLiteralEPair certFinThree
  decide

/-- The matching exact no-new-grant token row moves the sole old Y
grant to X, removing it at Y. No FIRE, no old HOLD, no leader sink. -/
theorem grantDrainStrongBoundaryGrantRow :
    (grantDrainTokenRow false false false true false false false .none).1.grant =
      true ∧
    (grantDrainTokenRow false false false true false false false .none).2.grant =
      false := by
  unfold grantDrainTokenRow
  decide

/-- Helper: rank >= strong means exactly strong or terminal. -/
theorem grantDrainStrongHighMarkCases
    (m : GrantDrainMark)
    (h : 2 ≤ grantDrainMarkRank m) :
    m = .strong ∨ m = .terminal := by
  cases m <;> simp [grantDrainMarkRank] at h ⊢

/-- Closure invariant only for a cohort ALREADY strongly locked.
If still strongly marked and live, it must have a real dynamic lock
and the remaining counter must pay for its current source distance.
Terminal labels are allowed but their quota needs a separate proof. -/
def GrantDrainStrongCertified
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n) : Prop :=
  PPlus ring s.native ∧
  (label.mark = .strong ∨ label.mark = .terminal) ∧
  (label.mark = .strong →
    label.host ≠ none →
    GrantDrainStrongPhysical ring s label ∧
      grantDrainStrongProtectedDistance ring s label.host ≤ label.remaining)

/-- Strong certificate is initialized at any protected strong cut,
when the old label's remaining clock covers the actual distance. -/
theorem grantDrainStrongCertifiedSeed
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hBudget :
      grantDrainStrongProtectedDistance ring s label.host ≤
        label.remaining) :
    GrantDrainStrongCertified ring s label := by
  rcases hPhysical with
    ⟨g, hHost, hMark, hGrant, hRequest, hLeader, hLock⟩
  refine ⟨hP, Or.inl hMark, ?_⟩
  intro _ _
  exact
    ⟨⟨g, hHost, hMark, hGrant, hRequest, hLeader, hLock⟩,
      hBudget⟩

/-- A complete strong-to-strong/terminal ONE-EDGE invariant proof,
conditional precisely on GrantDrainStrongCorridorGeometry. -/
theorem grantDrainStrongCertifiedStep
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (hGeometry :
      GrantDrainStrongCorridorGeometry ring freshRequest updateScratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hCertified : GrantDrainStrongCertified ring s label) :
    GrantDrainStrongCertified ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) := by
  rcases hCertified with ⟨hP, hOldCases, hOldInvariant⟩
  have hOldRank : 2 ≤ grantDrainMarkRank label.mark := by
    rcases hOldCases with hs | ht
    · simp [hs, grantDrainMarkRank]
    · simp [ht, grantDrainMarkRank]
  have hNextRank :
      2 ≤ grantDrainMarkRank
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark :=
    Nat.le_trans hOldRank
      (grantDrainLedgerStep_mark_monotone
        ring freshRequest updateScratch s e label)
  refine
    ⟨grantDrainStep_preserves_PPlus hn ring freshRequest updateScratch s e hP,
      grantDrainStrongHighMarkCases _ hNextRank, ?_⟩
  intro hNextStrong hNextLive
  have hOldStrong : label.mark = .strong := by
    rcases hOldCases with hs | ht
    · exact hs
    · have hMonotone :=
        grantDrainLedgerStep_mark_monotone
          ring freshRequest updateScratch s e label
      rw [ht, hNextStrong] at hMonotone
      simp [grantDrainMarkRank] at hMonotone
  have hOldLive : label.host ≠ none := by
    intro hNo
    exact hNextLive
      (grantDrainLedgerStep_retired_absorbing
        ring freshRequest updateScratch s e label hNo)
  rcases hOldInvariant hOldStrong hOldLive with
    ⟨hPhysical, hBudget⟩
  have hNextPhysical :=
    (hGeometry s e label hP hPhysical hNextLive hNextStrong).1
  exact ⟨hNextPhysical,
    grantDrainStrongStepBudgetOfGeometry
      ring freshRequest updateScratch hGeometry
      s e label hP hPhysical hBudget hNextLive hNextStrong⟩

/-- The strong invariant survives EVERY finite scheduler word,
provided the still-open exact physical one-edge corridor theorem.
This is the induction needed for the strong label clock. -/
theorem grantDrainStrongCertifiedRun
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (hGeometry :
      GrantDrainStrongCorridorGeometry ring freshRequest updateScratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (edges : List (Fin n))
    (hCertified : GrantDrainStrongCertified ring s label) :
    GrantDrainStrongCertified ring
      (grantDrainLedgerRun ring freshRequest updateScratch s label edges).1
      (grantDrainLedgerRun ring freshRequest updateScratch s label edges).2 := by
  induction edges generalizing s label with
  | nil =>
      simpa [grantDrainLedgerRun] using hCertified
  | cons e tail ih =>
      have hStep :=
        grantDrainStrongCertifiedStep hn ring freshRequest updateScratch
          hGeometry s e label hCertified
      change GrantDrainStrongCertified ring
        (grantDrainLedgerRun ring freshRequest updateScratch
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerStep ring freshRequest updateScratch s e label)
          tail).1
        (grantDrainLedgerRun ring freshRequest updateScratch
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerStep ring freshRequest updateScratch s e label)
          tail).2
      exact ih
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerStep ring freshRequest updateScratch s e label)
        hStep

/-- The strong branch of the no-exhaustion statement:
a live, still-strong label has strictly positive remaining.
DEPENDENCY: GrantDrainStrongCorridorGeometry is an explicit Prop input.
For terminal/weak histories or unconditional source NoExhaustion,
further geometric cases are necessary. -/
theorem grantDrainStrongNoExhaustionOfGeometry
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (hGeometry :
      GrantDrainStrongCorridorGeometry ring freshRequest updateScratch)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hBudget :
      grantDrainStrongProtectedDistance ring s label.host ≤ label.remaining)
    (edges : List (Fin n))
    (hStrong :
      (grantDrainLedgerRun ring freshRequest updateScratch s label edges).2.mark =
        .strong)
    (hLive :
      (grantDrainLedgerRun ring freshRequest updateScratch s label edges).2.host ≠
        none) :
    0 <
      (grantDrainLedgerRun ring freshRequest updateScratch s label edges).2.remaining := by
  have hStart :=
    grantDrainStrongCertifiedSeed ring s label hP hPhysical hBudget
  have hRun :=
    grantDrainStrongCertifiedRun hn ring freshRequest updateScratch
      hGeometry s label edges hStart
  have hBudgetAtRun := (hRun.2.2 hStrong hLive).2
  cases hHost :
      (grantDrainLedgerRun ring freshRequest updateScratch s label edges).2.host with
  | none =>
      exact False.elim (hLive hHost)
  | some g =>
      have hPositive :
          0 < grantDrainStrongProtectedDistance ring
            (grantDrainLedgerRun ring freshRequest updateScratch s label edges).1
            (grantDrainLedgerRun ring freshRequest updateScratch s label edges).2.host := by
        rw [hHost]
        exact grantDrainStrongProtectedDistance_some_pos ring
          (grantDrainLedgerRun ring freshRequest updateScratch s label edges).1 g
      exact Nat.lt_of_lt_of_le hPositive hBudgetAtRun

end L3

/-!
Local finite-row audit of D.1 strong corridors.

These are literal CertNative / GrantDrain token-owner facts, not an
assertion that the global PPL.scan-distance corridor theorem has
been discharged.  Source strong geometry remains a named open Prop
GrantDrainStrongCorridorGeometry.

For a moving host g the zero corridor is [p,g), excluding g.
If the edge (g-1)->g propagates S_g to g-1, a surviving unheld grant
moves to g-1 on that same edge. Thus the NEW endpoint is excluded.
The static "OLD interior signals never change" statement is FALSE.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Exhaust the three literal values of the native bullet field.
Only small, closed row goals are decided below. -/
private theorem grantDrainMarksBulletCases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- (a) For an interior edge with both endpoints FOLLOWERS and both
OLD signals zero, E leaves BOTH signals zero.  The bullet fields and
shield fields are completely arbitrary.  This is the local E row
needed when both endpoints lie strictly behind the current host. -/
theorem grantDrainMarksInteriorZeroRow
    (bulletX bulletY : Fin 3) (shieldX shieldY : Bool) :
    (certLiteralEPair
      { l := false, b := bulletX, sh := shieldX, sg := false }
      { l := false, b := bulletY, sh := shieldY, sg := false }).1.sg =
        false ∧
    (certLiteralEPair
      { l := false, b := bulletX, sh := shieldX, sg := false }
      { l := false, b := bulletY, sh := shieldY, sg := false }).2.sg =
        false := by
  rcases grantDrainMarksBulletCases bulletX with hbX | hbX | hbX <;>
    rcases grantDrainMarksBulletCases bulletY with hbY | hbY | hbY <;>
    cases shieldX <;> cases shieldY <;>
    simp [hbX, hbY, certLiteralEPair, certFinThree] <;> decide

/-- (b) The EXACT incoming-native-E barrier: an OLD leader with
shield=1, signal=0 is unchanged as responder, no matter what the
incoming initiator's FOUR native fields or the leader's bullet are.
In particular even an incoming LIVE bullet cannot kill this p. -/
theorem grantDrainMarksShieldedZeroResponderRow
    (incoming : CertNative) (bulletP : Fin 3) :
    (certLiteralEPair incoming
      { l := true, b := bulletP, sh := true, sg := false }).2 =
      { l := true, b := bulletP, sh := true, sg := false } := by
  rcases incoming with ⟨leaderX, bulletX, shieldX, signalX⟩
  rcases grantDrainMarksBulletCases bulletX with hbX | hbX | hbX <;>
    rcases grantDrainMarksBulletCases bulletP with hbP | hbP | hbP <;>
    cases leaderX <;> cases shieldX <;> cases signalX <;>
    simp [hbX, hbP, certLiteralEPair, certFinThree] <;> decide

/-- (a/b) On its outgoing edge, the shielded zero-signal source p
stays a shielded zero-signal leader if its responder is a zero-signal
FOLLOWER.  The source bullet, responder bullet, and responder shield
are unrestricted.  The case responder=g with S_g=1 is deliberately
NOT included: the grant's incoming edge must then move or retire it. -/
theorem grantDrainMarksShieldedZeroSourceOutgoingRow
    (bulletP bulletY : Fin 3) (shieldY : Bool) :
    (certLiteralEPair
      { l := true, b := bulletP, sh := true, sg := false }
      { l := false, b := bulletY, sh := shieldY, sg := false }).1.l =
        true ∧
    (certLiteralEPair
      { l := true, b := bulletP, sh := true, sg := false }
      { l := false, b := bulletY, sh := shieldY, sg := false }).1.sh =
        true ∧
    (certLiteralEPair
      { l := true, b := bulletP, sh := true, sg := false }
      { l := false, b := bulletY, sh := shieldY, sg := false }).1.sg =
        false := by
  rcases grantDrainMarksBulletCases bulletP with hbP | hbP | hbP <;>
    rcases grantDrainMarksBulletCases bulletY with hbY | hbY | hbY <;>
    cases shieldY <;>
    simp [hbP, hbY, certLiteralEPair, certFinThree] <;> decide

/-- Two precise endpoint native records for the incoming LIVE test. -/
private def grantDrainMarksIncomingLive : CertNative :=
  { l := false, b := (2 : Fin 3), sh := false, sg := false }

private def grantDrainMarksProtectedSource : CertNative :=
  { l := true, b := (0 : Fin 3), sh := true, sg := false }

private def grantDrainMarksReadyShieldedSource : CertNative :=
  { l := true, b := (0 : Fin 3), sh := true, sg := true }

/-- Protected source p=(L,0,H,0): the incoming LIVE is absorbed,
and p survives shielded with signal zero.  The initiator's signal
becomes true because the responding leader survives. -/
theorem grantDrainMarksIncomingLiveAbsorbed :
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksProtectedSource).1.b = (0 : Fin 3) ∧
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksProtectedSource).2.l = true ∧
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksProtectedSource).2.sh = true ∧
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksProtectedSource).2.sg = false := by
  unfold grantDrainMarksIncomingLive grantDrainMarksProtectedSource
    certLiteralEPair certFinThree
  decide

/-- Crucial sharpness witness outside D.1: H_p=1 ALONE does not
suffice. If OLD S_p=1, the responder first fires a DUMMY,
unshields to H_p=0, and the incoming LIVE then kills p on the
SAME native-E edge. The old D.1 source has S_p=0 and cannot do this.
The resulting responder is follower, DUMMY=1, shield=0, signal=0. -/
theorem grantDrainMarksReadyShieldedDies :
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksReadyShieldedSource).2.l = false ∧
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksReadyShieldedSource).2.b = (1 : Fin 3) ∧
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksReadyShieldedSource).2.sh = false ∧
    (certLiteralEPair grantDrainMarksIncomingLive
      grantDrainMarksReadyShieldedSource).2.sg = false := by
  unfold grantDrainMarksIncomingLive grantDrainMarksReadyShieldedSource
    certLiteralEPair certFinThree
  decide

/-- (c) A canonical birth is precisely a NEW protected leader with
signal zero (native b=0, H=1).  The global nearest-source-distance
comparison additionally needs a cyclic first-leader scan lemma. -/
theorem grantDrainMarksBirthIsProtected
    {n : Nat} (N : Fin n → CertNative) (z : Fin n) :
    (canonicalBirth N z z).l = true ∧
    (canonicalBirth N z z).b = (0 : Fin 3) ∧
    (canonicalBirth N z z).sh = true ∧
    (canonicalBirth N z z).sg = false := by
  simp [canonicalBirth, firedNative]

/-- A canonical birth cannot modify the other sites of the
suffix of a moving corridor; those sites are framed by overwrite. -/
theorem grantDrainMarksBirthOtherSite
    {n : Nat} (N : Fin n → CertNative)
    (z w : Fin n) (h : w ≠ z) :
    canonicalBirth N z w = N w := by
  simp [canonicalBirth, h]

/-- Arithmetic of the closer newborn source:
if the birth position is strictly between p and g, its clockwise
distance to g is smaller than the old p-to-g distance.
This is only the Nat part; ring-offset identification is still open. -/
theorem grantDrainMarksCloserBirthArithmetic
    (oldDistance birthOffset : Nat)
    (hPositive : 0 < birthOffset)
    (hInterior : birthOffset < oldDistance) :
    oldDistance - birthOffset < oldDistance := by
  omega

/-- (d) Exact token-owner row: for an unheld OLD Y grant,
the responder has NO grant after a service, irrespective of
X request/grant, leader sinks, fresh request, or FIRE selector.
Therefore the grant cannot STUTTER at Y on its incoming edge. -/
theorem grantDrainMarksUnheldResponderNoStutter
    (rx gx lx ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx false true lx ly fresh fire).2.grant =
      false := by
  cases rx <;> cases gx <;> cases lx <;> cases ly <;>
    cases fresh <;> cases fire <;>
    simp [grantDrainTokenRow] <;> decide

/-- If the unheld Y grant has no FIRE and neither final endpoint is
a leader, its physical survivor moves counterclockwise Y->X.
An old X grant may coalesce with it but cannot copy the old Y host. -/
theorem grantDrainMarksUnheldResponderMoves
    (rx gx fresh : Bool) :
    (grantDrainTokenRow rx gx false true false false fresh .none).1.grant =
        true ∧
    (grantDrainTokenRow rx gx false true false false fresh .none).2.grant =
        false := by
  cases rx <;> cases gx <;> cases fresh <;>
    simp [grantDrainTokenRow] <;> decide

/-- Stronger ancestry-facing version of the same local fact:
the OLD unheld responder grant is NEVER declared to STAY Y by
the proof-only host transport (regardless of FIRE/sink). -/
theorem grantDrainMarksUnheldResponderLabelNeverStays
    (rx gx lx ly fresh : Bool) (fire : GrantDrainFire) :
    grantDrainLedgerYSource false true lx ly fire
      (grantDrainTokenRow rx gx false true lx ly fresh fire) ≠
        some true := by
  have hNoY :
      (grantDrainTokenRow rx gx false true lx ly fresh fire).2.grant =
        false :=
    grantDrainMarksUnheldResponderNoStutter rx gx lx ly fresh fire
  simp [grantDrainLedgerYSource, hNoY]

/-- In the no-FIRE, no-sink row the proof-only Y identity
explicitly follows the physical old Y grant to X. -/
theorem grantDrainMarksUnheldResponderLabelMoves
    (rx gx fresh : Bool) :
    grantDrainLedgerYSource false true false false .none
      (grantDrainTokenRow rx gx false true false false fresh .none) =
        some false := by
  have hRow :=
    grantDrainMarksUnheldResponderMoves rx gx fresh
  simp [grantDrainLedgerYSource, hRow.1, hRow.2] <;> decide

/-- Pure Nat progress: if the protected distance is at least 2,
one counterclockwise movement decreases that distance by one;
a closer birth subtracts still more.  No global PPL geometry
has been substituted for these arithmetic premises. -/
theorem grantDrainMarksDistanceDropsWithMove
    (d dPrime : Nat)
    (hd : 0 < d)
    (hNew : dPrime ≤ d - 1) :
    dPrime + 1 ≤ d := by
  omega

/- Local rows proved here do NOT yet establish the global
GrantDrainStrongCorridorGeometry: need to connect 1) the finite E
rows to all ring offsets in the entire half-open arc, 2) every
F0/F1/F2 birth target to the exact FIRST preceding-leader
after state, 3) proof-only host transport to the full nominated
physical row, and 4) closure of the persistent strong mark.

The S_p=1 same-service death witness above is OUTSIDE the
strong-lock antecedent, so it does not refute the intended
shielded, zero-signal protected-source argument. -/

end L3

/-!
Cyclic-offset first-leader scan and protected-source arc lift.

grantDrainLeftLeaderDistance is the first hit among distances
1,...,n, NOT among 0,...,n-1.  Thus a canonical birth AT g does not
decrease the scan distance from g; it consumes/sinks the grant in the
actual FIRE model.  The closer-birth scan theorem excludes the host.

The first-hit, old-arc frame, closer-birth and host-left-move
identities are proved from the exact List.find? scan plus PPL.cyclicOffset.
The global physical six-way native/token case split is still named
as an obligation; no theorem below imports its truth.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The exact list enumerated by grantDrainLeftLeaderDistance. -/
private theorem grantDrainMarksDistanceRange (n : Nat) :
    (List.range n).map (fun k : Nat => k + 1) =
      List.range' 1 n := by
  have hfun : (fun k : Nat => k + 1) =
      (fun k : Nat => 1 + k) := by
    funext k
    omega
  rw [hfun]
  exact (List.range'_eq_map_range (s := 1) (n := n)).symm

/-- Generic first-success proof for a consecutive Nat range.
No classical choice, minimization, or Nat.find is used. -/
private theorem grantDrainMarksFirstHitRange
    (f : Nat → Bool) :
    ∀ length start d,
      start ≤ d →
      d < start + length →
      f d = true →
      (∀ k, start ≤ k → k < d → f k = false) →
      (List.range' start length).find? f = some d := by
  intro length
  induction length with
  | zero =>
      intro start d hlo hhi hhit hbefore
      omega
  | succ length ih =>
      intro start d hlo hhi hhit hbefore
      by_cases hstart : start = d
      · subst d
        change (start :: List.range' (start + 1) length).find? f =
          some start
        simp [List.find?, hhit]
      · have hfirst : f start = false :=
          hbefore start (Nat.le_refl _) (by omega)
        have htail :
            (List.range' (start + 1) length).find? f = some d :=
          ih (start + 1) d (by omega) (by omega) hhit
            (fun k hk hkd => hbefore k (by omega) hkd)
        change (start :: List.range' (start + 1) length).find? f =
          some d
        simp [List.find?, hfirst, htail]

/-- Exact FIRST LEADER lemma for the scan in GrantDrain.lean.
The candidate d is a positive distance no larger than n, it
hits a leader, and every smaller positive distance misses. -/
theorem grantDrainMarksScanFirstSource
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (g : Fin n) (d : Nat)
    (hpos : 1 ≤ d) (hbound : d ≤ n)
    (hsource : (N (PPL.shiftLeft ring g d)).l = true)
    (hbefore : ∀ k, 1 ≤ k → k < d →
      (N (PPL.shiftLeft ring g k)).l = false) :
    grantDrainLeftLeaderDistance ring N g = d := by
  change (((List.range n).map (fun k : Nat => k + 1)).find?
    (fun k => (N (PPL.shiftLeft ring g k)).l)).getD n = d
  rw [grantDrainMarksDistanceRange]
  have hfind :
      (List.range' 1 n).find?
        (fun k => (N (PPL.shiftLeft ring g k)).l) = some d :=
    grantDrainMarksFirstHitRange
      (fun k => (N (PPL.shiftLeft ring g k)).l)
      n 1 d (by omega) (by omega) hsource hbefore
  rw [hfind]
  rfl

/-- Local ring-coordinate arithmetic; copied as a private bridge to
avoid importing another Leader.L3 module or a possible cycle. -/
private theorem grantDrainMarksArcShiftRightZero
    {n : Nat} (ring : DirectedRing n) (p : Fin n) :
    PPL.shiftRight ring p 0 = p := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt p.isLt]

private theorem grantDrainMarksArcOffsetZero
    {n : Nat} (ring : DirectedRing n) (p : Fin n) :
    PPL.cyclicOffset ring p p = 0 := by
  unfold PPL.cyclicOffset
  have hs : p.val + n - p.val = n := by omega
  rw [hs, Nat.mod_self]

private theorem grantDrainMarksArcOffsetLt
    {n : Nat} (ring : DirectedRing n) (p g : Fin n) :
    PPL.cyclicOffset ring p g < n := by
  unfold PPL.cyclicOffset
  exact Nat.mod_lt _ ring.hn

private theorem grantDrainMarksArcShiftRightAdd
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring p a) b =
      PPL.shiftRight ring p (a + b) := by
  apply Fin.ext
  change (((p.val + a) % n + b) % n) =
    (p.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem grantDrainMarksArcOffsetShiftRight
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring p (PPL.shiftRight ring p d) = d := by
  change (((p.val + d) % n + n - p.val) % n) = d
  by_cases hs : p.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : p.val + d + n - p.val = n + d := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hge : n ≤ p.val + d := by omega
    have hlt : p.val + d - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : p.val + d - n + n - p.val = d := by omega
    rw [he, Nat.mod_eq_of_lt hd]

/-- Every ring site is obtained by shifting its root forward
by its cyclic offset, including the wraparound case. -/
theorem grantDrainMarksArcShiftRightOffset
    {n : Nat} (ring : DirectedRing n) (p g : Fin n) :
    PPL.shiftRight ring p (PPL.cyclicOffset ring p g) = g := by
  by_cases hle : p.val ≤ g.val
  · have hoff : PPL.cyclicOffset ring p g =
        g.val - p.val := by
      unfold PPL.cyclicOffset
      have hs : g.val + n - p.val = n + (g.val - p.val) := by
        omega
      rw [hs, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega : g.val - p.val < n)]
    apply Fin.ext
    change (p.val + PPL.cyclicOffset ring p g) % n = g.val
    rw [hoff]
    have hs : p.val + (g.val - p.val) = g.val := by omega
    rw [hs, Nat.mod_eq_of_lt g.isLt]
  · have hlt : g.val < p.val := by omega
    have hoff : PPL.cyclicOffset ring p g =
        g.val + n - p.val := by
      unfold PPL.cyclicOffset
      rw [Nat.mod_eq_of_lt (by omega :
        g.val + n - p.val < n)]
    apply Fin.ext
    change (p.val + PPL.cyclicOffset ring p g) % n = g.val
    rw [hoff]
    have hs : p.val + (g.val + n - p.val) = g.val + n := by
      omega
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt g.isLt]

/-- Exact inverse shift when 0 ≤ k ≤ d < n.
This is the cyclic-offset identity used to turn the clockwise
leader arc into the counterclockwise first-hit scan. -/
theorem grantDrainMarksArcShiftLeftRight
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n) (d k : Nat)
    (hk : k ≤ d) (hd : d < n) :
    PPL.shiftLeft ring (PPL.shiftRight ring p d) k =
      PPL.shiftRight ring p (d - k) := by
  apply Fin.ext
  change (((p.val + d) % n + n - k % n) % n) =
    (p.val + (d - k)) % n
  have hkl : k < n := Nat.lt_of_le_of_lt hk hd
  rw [Nat.mod_eq_of_lt hkl]
  by_cases hs : p.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : p.val + d + n - k =
        n + (p.val + (d - k)) := by omega
    rw [he, Nat.add_mod_left]
  · have hge : n ≤ p.val + d := by omega
    have hlt : p.val + d - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : p.val + d - n + n - k =
        p.val + (d - k) := by omega
    rw [he]

/-- p is the first preceding leader on the clockwise sector ending
at g. d=cyclicOffset p g is POSITIVE: g itself is excluded by
grantDrainLeftLeaderDistance. -/
def GrantDrainMarksNearestArc
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n) : Prop :=
  0 < PPL.cyclicOffset ring p g ∧
  (N p).l = true ∧
  ∀ k : Nat, 0 < k →
    k < PPL.cyclicOffset ring p g →
    (N (PPL.shiftRight ring p k)).l = false

/-- The scan is exactly the clockwise cyclic offset from the nearest
leader p to follower g.  No new search algorithm is introduced. -/
theorem grantDrainMarksScanOfNearestArc
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n)
    (hArc : GrantDrainMarksNearestArc ring N p g) :
    grantDrainLeftLeaderDistance ring N g =
      PPL.cyclicOffset ring p g := by
  rcases hArc with ⟨hpos, hp, hinner⟩
  have hdlt := grantDrainMarksArcOffsetLt ring p g
  have hg : g = PPL.shiftRight ring p (PPL.cyclicOffset ring p g) :=
    (grantDrainMarksArcShiftRightOffset ring p g).symm
  have hsource :
      (N (PPL.shiftLeft ring g (PPL.cyclicOffset ring p g))).l =
        true := by
    have hc := grantDrainMarksArcShiftLeftRight ring p
      (PPL.cyclicOffset ring p g) (PPL.cyclicOffset ring p g)
      (Nat.le_refl _) hdlt
    rw [← hg] at hc
    rw [hc]
    simpa [grantDrainMarksArcShiftRightZero] using hp
  have hbefore :
      ∀ k, 1 ≤ k → k < PPL.cyclicOffset ring p g →
        (N (PPL.shiftLeft ring g k)).l = false := by
    intro k hk hkd
    have hc := grantDrainMarksArcShiftLeftRight ring p
      (PPL.cyclicOffset ring p g) k (by omega) hdlt
    rw [← hg] at hc
    rw [hc]
    exact hinner (PPL.cyclicOffset ring p g - k)
      (by omega) (by omega)
  exact grantDrainMarksScanFirstSource ring N g
    (PPL.cyclicOffset ring p g) (by omega)
    (Nat.le_of_lt hdlt) hsource hbefore

/-- The positive bounded source distance agrees with the raw scan. -/
theorem grantDrainMarksProtectedDistanceOfArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hArc : GrantDrainMarksNearestArc ring s.native p g) :
    grantDrainStrongProtectedDistance ring s (some g) =
      PPL.cyclicOffset ring p g := by
  have hd := grantDrainMarksScanOfNearestArc ring s.native p g hArc
  have hpos : 0 < grantDrainLeftLeaderDistance ring s.native g := by
    rw [hd]
    exact hArc.1
  have hbound : grantDrainLeftLeaderDistance ring s.native g ≤ n := by
    rw [hd]
    exact Nat.le_of_lt (grantDrainMarksArcOffsetLt ring p g)
  rw [grantDrainStrongProtectedDistance_eq_raw ring s g hpos hbound, hd]

/-- (i) The whole leader-flag prefix from p through the site before g
is preserved (cyclic offsets 0,...,d-1).  Hence the actual
grantDrainLeftLeaderDistance at g is EXACTLY unchanged. -/
theorem grantDrainMarksArcLeaderFrame
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p g : Fin n)
    (hArc : GrantDrainMarksNearestArc ring N p g)
    (hFrame : ∀ k : Nat, k < PPL.cyclicOffset ring p g →
      (M (PPL.shiftRight ring p k)).l =
        (N (PPL.shiftRight ring p k)).l) :
    grantDrainLeftLeaderDistance ring M g =
      grantDrainLeftLeaderDistance ring N g := by
  rcases hArc with ⟨hpos, hp, hinner⟩
  have hpM : (M p).l = true := by
    have hzero := hFrame 0 (by omega)
    rw [grantDrainMarksArcShiftRightZero] at hzero
    rw [hzero]
    exact hp
  have hinnerM : ∀ k : Nat, 0 < k →
      k < PPL.cyclicOffset ring p g →
      (M (PPL.shiftRight ring p k)).l = false := by
    intro k hk hkd
    rw [hFrame k hkd]
    exact hinner k hk hkd
  have hOld := grantDrainMarksScanOfNearestArc ring N p g
    ⟨hpos, hp, hinner⟩
  have hNew := grantDrainMarksScanOfNearestArc ring M p g
    ⟨hpos, hpM, hinnerM⟩
  rw [hOld, hNew]

/-- Cyclic subtraction: from a source p to g, passing a prospective
new source at clockwise offset j shortens the remaining offset by j.
The proof uses rotation/cyclicOffset, not a new distance search. -/
theorem grantDrainMarksArcOffsetSubtract
    {n : Nat} (ring : DirectedRing n)
    (p g : Fin n) (j : Nat)
    (hj : j ≤ PPL.cyclicOffset ring p g) :
    PPL.cyclicOffset ring (PPL.shiftRight ring p j) g =
      PPL.cyclicOffset ring p g - j := by
  have hd := grantDrainMarksArcOffsetLt ring p g
  have hshift :
      PPL.shiftRight ring (PPL.shiftRight ring p j)
        (PPL.cyclicOffset ring p g - j) = g := by
    calc
      PPL.shiftRight ring (PPL.shiftRight ring p j)
          (PPL.cyclicOffset ring p g - j) =
        PPL.shiftRight ring p
          (j + (PPL.cyclicOffset ring p g - j)) :=
        grantDrainMarksArcShiftRightAdd ring p j
          (PPL.cyclicOffset ring p g - j)
      _ = PPL.shiftRight ring p (PPL.cyclicOffset ring p g) := by
        congr 1
        omega
      _ = g := grantDrainMarksArcShiftRightOffset ring p g
  have hOff := grantDrainMarksArcOffsetShiftRight ring
    (PPL.shiftRight ring p j)
    (PPL.cyclicOffset ring p g - j) (by omega)
  rw [hshift] at hOff
  exact hOff

/-- (ii) A new leader strictly inside (p,g), at clockwise offset j,
strictly decreases the FIRST predecessor distance, provided no
other leader remains between that newborn and g.  This is an
actual scan theorem for arbitrary old/new native functions. -/
theorem grantDrainMarksArcNewLeaderCloser
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p g : Fin n) (j : Nat)
    (hArc : GrantDrainMarksNearestArc ring N p g)
    (hjpos : 0 < j)
    (hjlt : j < PPL.cyclicOffset ring p g)
    (hNew : (M (PPL.shiftRight ring p j)).l = true)
    (hInterior : ∀ k : Nat, j < k →
      k < PPL.cyclicOffset ring p g →
      (M (PPL.shiftRight ring p k)).l = false) :
    grantDrainLeftLeaderDistance ring M g <
      grantDrainLeftLeaderDistance ring N g := by
  have hOff := grantDrainMarksArcOffsetSubtract ring p g j
    (Nat.le_of_lt hjlt)
  have hNewArc :
      GrantDrainMarksNearestArc ring M
        (PPL.shiftRight ring p j) g := by
    refine ⟨?_, hNew, ?_⟩
    · rw [hOff]
      omega
    · intro k hk hkd
      rw [hOff] at hkd
      have hs := grantDrainMarksArcShiftRightAdd ring p j k
      rw [hs]
      exact hInterior (j + k) (by omega) (by omega)
  have hOld := grantDrainMarksScanOfNearestArc ring N p g hArc
  have hNow := grantDrainMarksScanOfNearestArc ring M
    (PPL.shiftRight ring p j) g hNewArc
  rw [hNow, hOld, hOff]
  omega

/-- Canonical FIRE birth strictly INSIDE (p,g): it sets a NEW
leader and leaves all strictly later follower leader bits alone.
The exact first-leader distance strictly decreases.  A birth at
the host g is excluded; FIRE consumes that host's old grant. -/
theorem grantDrainMarksArcCanonicalBirthCloser
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n) (j : Nat)
    (hArc : GrantDrainMarksNearestArc ring N p g)
    (hjpos : 0 < j)
    (hjlt : j < PPL.cyclicOffset ring p g) :
    grantDrainLeftLeaderDistance ring
        (canonicalBirth N (PPL.shiftRight ring p j)) g <
      grantDrainLeftLeaderDistance ring N g := by
  apply grantDrainMarksArcNewLeaderCloser ring N
    (canonicalBirth N (PPL.shiftRight ring p j))
    p g j hArc hjpos hjlt
    (grantDrainMarksBirthIsProtected N
      (PPL.shiftRight ring p j)).1
  intro k hjk hkd
  have hklt : k < n :=
    Nat.lt_trans hkd (grantDrainMarksArcOffsetLt ring p g)
  have hjn : j < n :=
    Nat.lt_trans hjlt (grantDrainMarksArcOffsetLt ring p g)
  have hne :
      PPL.shiftRight ring p k ≠ PPL.shiftRight ring p j := by
    intro heq
    have ho := congrArg (PPL.cyclicOffset ring p) heq
    rw [grantDrainMarksArcOffsetShiftRight ring p k hklt,
      grantDrainMarksArcOffsetShiftRight ring p j hjn] at ho
    omega
  have hFrame := grantDrainMarksBirthOtherSite N
    (PPL.shiftRight ring p j) (PPL.shiftRight ring p k) hne
  have hLeaderFrame := congrArg CertNative.l hFrame
  rw [hLeaderFrame]
  exact hArc.2.2 k (by omega) hkd

/-- (iii) The ring left neighbor x of g is the site at offset d-1
from p.  If d>=2, p..x remains a nonempty clockwise arc. -/
theorem grantDrainMarksArcLeftHostSite
    {n : Nat} (ring : DirectedRing n)
    (p g : Fin n) (d : Nat)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hdpos : 1 ≤ d) :
    PPL.shiftLeft ring g 1 = PPL.shiftRight ring p (d - 1) := by
  have hdn : d < n := by
    rw [← hOff]
    exact grantDrainMarksArcOffsetLt ring p g
  have hg : PPL.shiftRight ring p d = g := by
    rw [← hOff]
    exact grantDrainMarksArcShiftRightOffset ring p g
  calc
    PPL.shiftLeft ring g 1 =
      PPL.shiftLeft ring (PPL.shiftRight ring p d) 1 := by
        rw [hg]
    _ = PPL.shiftRight ring p (d - 1) :=
      grantDrainMarksArcShiftLeftRight ring p d 1
        (by omega) hdn

/-- (iii) If the live host moves g -> g-1 and leader flags on
[p,g-1] do not change, the first-source distance drops EXACTLY one.
This is not a conditional arithmetic inequality: both sides are
the actual grantDrainLeftLeaderDistance scans. -/
theorem grantDrainMarksArcLeftHostDistance
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p g : Fin n) (d : Nat)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hdpos : 2 ≤ d)
    (hArc : GrantDrainMarksNearestArc ring N p g)
    (hFrame : ∀ k : Nat, k < d - 1 →
      (M (PPL.shiftRight ring p k)).l =
        (N (PPL.shiftRight ring p k)).l) :
    grantDrainLeftLeaderDistance ring M
        (PPL.shiftLeft ring g 1) + 1 =
      grantDrainLeftLeaderDistance ring N g := by
  have hx := grantDrainMarksArcLeftHostSite
    ring p g d hOff (by omega)
  have hOffX :
      PPL.cyclicOffset ring p (PPL.shiftLeft ring g 1) = d - 1 := by
    rw [hx]
    apply grantDrainMarksArcOffsetShiftRight ring p (d - 1)
    have hdlt : d < n := by
      rw [← hOff]
      exact grantDrainMarksArcOffsetLt ring p g
    omega
  have hOld := grantDrainMarksScanOfNearestArc ring N p g hArc
  rcases hArc with ⟨hpositive, hLeader, hInner⟩
  have hLeaderNew : (M p).l = true := by
    have hz := hFrame 0 (by omega)
    rw [grantDrainMarksArcShiftRightZero] at hz
    rw [hz]
    exact hLeader
  have hInnerNew : ∀ k : Nat, 0 < k →
      k < PPL.cyclicOffset ring p (PPL.shiftLeft ring g 1) →
      (M (PPL.shiftRight ring p k)).l = false := by
    intro k hk hkl
    rw [hOffX] at hkl
    rw [hFrame k hkl]
    exact hInner k hk (by omega)
  have hNewArc :
      GrantDrainMarksNearestArc ring M p
        (PPL.shiftLeft ring g 1) :=
    ⟨by rw [hOffX]; omega, hLeaderNew, hInnerNew⟩
  have hNew := grantDrainMarksScanOfNearestArc ring M p
    (PPL.shiftLeft ring g 1) hNewArc
  rw [hNew, hOld, hOffX, hOff]
  omega

/-- The literal source native update cannot touch a site outside
the selected pair, regardless of FIRE.  This is the source-level
bridge from the earlier pair rows to an entire unaffected ring arc. -/
theorem grantDrainMarksNativeOutsidePairFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e i : Fin n)
    (hX : i ≠ e) (hY : i ≠ ring.rightNeighbor e) :
    grantDrainNativeNext ring s e i = s.native i := by
  cases hf : grantDrainSelect ring s e <;>
    simp [grantDrainNativeNext, hf, canonicalBirth,
      nativeE, hX, hY]

/-- An edge wholly away from the old p..g arc leaves ALL its
leader flags unchanged, even if a canonical birth occurs on the
unrelated selected pair.  The exact scan distance at g is framed. -/
theorem grantDrainMarksAwayArcDistanceFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n)
    (hArc : GrantDrainMarksNearestArc ring s.native p g)
    (hAway : ∀ k : Nat,
      k < PPL.cyclicOffset ring p g →
        PPL.shiftRight ring p k ≠ e ∧
        PPL.shiftRight ring p k ≠ ring.rightNeighbor e) :
    grantDrainLeftLeaderDistance ring
        (grantDrainNativeNext ring s e) g =
      grantDrainLeftLeaderDistance ring s.native g := by
  apply grantDrainMarksArcLeaderFrame ring s.native
    (grantDrainNativeNext ring s e) p g hArc
  intro k hk
  have hOutside := hAway k hk
  exact congrArg CertNative.l
    (grantDrainMarksNativeOutsidePairFrame ring s e
      (PPL.shiftRight ring p k) hOutside.1 hOutside.2)

/-- Exact F0/F2 source spelling: the native successor is E then
canonical birth at X.  Thus the closer-birth scan theorem applies
whenever X lies strictly inside the post-E protected arc. -/
theorem grantDrainMarksBirthAtXSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e = .leftLocal ∨
      grantDrainSelect ring s e = .cross) :
    grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e) e := by
  rcases hFire with h | h
  · simp [grantDrainNativeNext, h]
  · simp [grantDrainNativeNext, h]

/-- Exact F1 source spelling: the native successor is E then
canonical birth at the responder Y. -/
theorem grantDrainMarksBirthAtYSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFire : grantDrainSelect ring s e = .rightLocal) :
    grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e)
        (ring.rightNeighbor e) := by
  simp [grantDrainNativeNext, hFire]

/-- Applied birth scan after the literal E step.  The post-E arc
premise is intentional: promoting OLD zero-corridor preservation
through E is a separate native-row obligation. -/
theorem grantDrainMarksSourceBirthCloser
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e p g b : Fin n) (j : Nat)
    (hBirth : grantDrainNativeNext ring s e =
      canonicalBirth (nativeE ring s.native e) b)
    (hArc : GrantDrainMarksNearestArc ring
      (nativeE ring s.native e) p g)
    (hSite : b = PPL.shiftRight ring p j)
    (hjpos : 0 < j)
    (hjlt : j < PPL.cyclicOffset ring p g) :
    grantDrainLeftLeaderDistance ring
        (grantDrainNativeNext ring s e) g <
      grantDrainLeftLeaderDistance ring
        (nativeE ring s.native e) g := by
  rw [hBirth, hSite]
  exact grantDrainMarksArcCanonicalBirthCloser ring
    (nativeE ring s.native e) p g j hArc hjpos hjlt

/-!
The requested "new leader in (p,g]" needs a qualification:
grantDrainLeftLeaderDistance starts at d=1, so birth AT g is
not visible in that scan.  In the physical F0/F1/F2 step such a birth
consumes/sinks the old grant label, so it is not a counterexample
to strong progress for a SURVIVING label.
-/

private def grantDrainMarksHostBirthRing : DirectedRing 4 := ⟨by decide⟩

private def grantDrainMarksHostBirthNative (i : Fin 4) : CertNative :=
  if i.val == 0 then firedNative
  else { l := false, b := (0 : Fin 3), sh := false, sg := false }

/-- Exact closed scan witness: adding a leader AT the observed host
does NOT reduce the positive-distance first-left-leader scan. -/
theorem grantDrainMarksHostBirthDistanceUnchanged :
    grantDrainLeftLeaderDistance grantDrainMarksHostBirthRing
      grantDrainMarksHostBirthNative (2 : Fin 4) = 2 ∧
    grantDrainLeftLeaderDistance grantDrainMarksHostBirthRing
      (canonicalBirth grantDrainMarksHostBirthNative (2 : Fin 4))
      (2 : Fin 4) = 2 ∧
    (canonicalBirth grantDrainMarksHostBirthNative
      (2 : Fin 4) (2 : Fin 4)).l = true := by
  unfold grantDrainMarksHostBirthRing grantDrainMarksHostBirthNative
    grantDrainLeftLeaderDistance canonicalBirth firedNative
  decide

/-- Precise remaining one-edge source obligation: the local native E
rows, FIRE birth target and token owner must place each still-live,
still-strong label in one of:
  * same host + unchanged leader prefix (non-nominated);
  * predecessor host + unchanged leader prefix to g-1;
  * same host + closer newborn protected source (non-nominated).
The exact first-leader / distance effects of these cases are now
provided by the three proved arc scan theorems above.

Cases NOT yet glued: the source p outgoing edge when the next
site coincides with the grant; the incoming edge at g carrying a
nonzero endpoint signal; F0/F1/F2 interaction with resident X grant
and coalescing Y labels; and proof that the post-step zero corridor
remains protected rather than merely preserving leader bits. -/
def GrantDrainMarksStrongArcCoverage
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) : Prop :=
  ∀ (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n),
    PPlus ring s.native →
    GrantDrainStrongPhysical ring s label →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠
      none →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
      .strong →
    ∃ (p g : Fin n),
      label.host = some g ∧
      GrantDrainMarksNearestArc ring s.native p g ∧
      (( (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some g ∧
          grantDrainLedgerNominatedHit ring s e label.host = false ∧
          (∀ k : Nat, k < PPL.cyclicOffset ring p g →
            ((grantDrainStep ring freshRequest updateScratch s e).native
               (PPL.shiftRight ring p k)).l =
            (s.native (PPL.shiftRight ring p k)).l)) ∨
        (∃ d : Nat,
          PPL.cyclicOffset ring p g = d ∧ 2 ≤ d ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some (PPL.shiftLeft ring g 1) ∧
          (∀ k : Nat, k < d - 1 →
            ((grantDrainStep ring freshRequest updateScratch s e).native
               (PPL.shiftRight ring p k)).l =
            (s.native (PPL.shiftRight ring p k)).l)) ∨
        (∃ j : Nat, 0 < j ∧
          j < PPL.cyclicOffset ring p g ∧
          grantDrainLedgerNominatedHit ring s e label.host = false ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some g ∧
          GrantDrainMarksNearestArc ring
            (grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring p j) g))

/-- A different, genuinely physical requirement: every continuing
strong label remains at a follower, unheld and shielded behind its
moving zero corridor.  ArcCoverage above only tracks leader distances,
so this cannot be omitted or inferred from the arithmetic. -/
def GrantDrainMarksStrongPhysicalClosure
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) : Prop :=
  ∀ (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n),
    PPlus ring s.native →
    GrantDrainStrongPhysical ring s label →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠
      none →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
      .strong →
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label)


/-- Stable-host branch of ArcCoverage pays zero distance increase.
The proof uses the actual source scan, not an abstract rank. -/
theorem grantDrainMarksArcStableProtectedDistance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s t : GrantDrainState n Scratch)
    (p g : Fin n)
    (hArc : GrantDrainMarksNearestArc ring s.native p g)
    (hFrame : ∀ k : Nat, k < PPL.cyclicOffset ring p g →
      (t.native (PPL.shiftRight ring p k)).l =
        (s.native (PPL.shiftRight ring p k)).l) :
    grantDrainStrongProtectedDistance ring t (some g) =
      grantDrainStrongProtectedDistance ring s (some g) := by
  have hOld := grantDrainMarksScanOfNearestArc ring s.native p g hArc
  have hFrameScan :=
    grantDrainMarksArcLeaderFrame ring s.native t.native p g
      hArc hFrame
  have hPositive : 0 < grantDrainLeftLeaderDistance ring s.native g := by
    rw [hOld]
    exact hArc.1
  have hBound : grantDrainLeftLeaderDistance ring s.native g ≤ n := by
    rw [hOld]
    exact Nat.le_of_lt (grantDrainMarksArcOffsetLt ring p g)
  have hPositiveNext :
      0 < grantDrainLeftLeaderDistance ring t.native g := by
    rw [hFrameScan]
    exact hPositive
  have hBoundNext :
      grantDrainLeftLeaderDistance ring t.native g ≤ n := by
    rw [hFrameScan]
    exact hBound
  calc
    grantDrainStrongProtectedDistance ring t (some g) =
        grantDrainLeftLeaderDistance ring t.native g :=
      grantDrainStrongProtectedDistance_eq_raw ring t g
        hPositiveNext hBoundNext
    _ = grantDrainLeftLeaderDistance ring s.native g := hFrameScan
    _ = grantDrainStrongProtectedDistance ring s (some g) :=
      (grantDrainStrongProtectedDistance_eq_raw ring s g
        hPositive hBound).symm

/-- Moving-host branch of ArcCoverage pays exactly one progress
hit in the bounded protected-distance potential, under the
actual leader-arc frame to g-1. -/
theorem grantDrainMarksArcLeftProtectedDistance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s t : GrantDrainState n Scratch)
    (p g : Fin n) (d : Nat)
    (hOff : PPL.cyclicOffset ring p g = d)
    (hdpos : 2 ≤ d)
    (hArc : GrantDrainMarksNearestArc ring s.native p g)
    (hFrame : ∀ k : Nat, k < d - 1 →
      (t.native (PPL.shiftRight ring p k)).l =
        (s.native (PPL.shiftRight ring p k)).l) :
    grantDrainStrongProtectedDistance ring t
        (some (PPL.shiftLeft ring g 1)) + 1 =
      grantDrainStrongProtectedDistance ring s (some g) := by
  have hOld := grantDrainMarksScanOfNearestArc ring s.native p g hArc
  have hStep :=
    grantDrainMarksArcLeftHostDistance ring s.native t.native p g d
      hOff hdpos hArc hFrame
  have hOldPositive :
      0 < grantDrainLeftLeaderDistance ring s.native g := by
    rw [hOld, hOff]
    omega
  have hOldBound :
      grantDrainLeftLeaderDistance ring s.native g ≤ n := by
    rw [hOld]
    exact Nat.le_of_lt (grantDrainMarksArcOffsetLt ring p g)
  have hNewPositive :
      0 < grantDrainLeftLeaderDistance ring t.native
        (PPL.shiftLeft ring g 1) := by
    rw [hOld, hOff] at hStep
    omega
  have hNewBound :
      grantDrainLeftLeaderDistance ring t.native
        (PPL.shiftLeft ring g 1) ≤ n := by
    omega
  calc
    grantDrainStrongProtectedDistance ring t
        (some (PPL.shiftLeft ring g 1)) + 1 =
        grantDrainLeftLeaderDistance ring t.native
          (PPL.shiftLeft ring g 1) + 1 := by
      rw [grantDrainStrongProtectedDistance_eq_raw ring t
        (PPL.shiftLeft ring g 1) hNewPositive hNewBound]
    _ = grantDrainLeftLeaderDistance ring s.native g := by
      exact grantDrainMarksArcLeftHostDistance ring s.native t.native
        p g d hOff hdpos hArc hFrame
    _ = grantDrainStrongProtectedDistance ring s (some g) :=
      (grantDrainStrongProtectedDistance_eq_raw ring s g
        hOldPositive hOldBound).symm

/-- This is the precise formal composition of the new distance
scan theorems with the six-position native/token case interface.
It does NOT prove the two source-level hypotheses; neither is an
axiom.  There is no unresolved distance arithmetic after them. -/
theorem grantDrainStrongCorridorGeometry_of_arc_coverage
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (hCoverage :
      GrantDrainMarksStrongArcCoverage ring freshRequest updateScratch)
    (hPhysical :
      GrantDrainMarksStrongPhysicalClosure ring freshRequest updateScratch) :
    GrantDrainStrongCorridorGeometry ring freshRequest updateScratch := by
  intro s e label hP hOldPhysical hLive hStrong
  have hNextPhysical :=
    hPhysical s e label hP hOldPhysical hLive hStrong
  refine ⟨hNextPhysical, ?_⟩
  rcases hCoverage s e label hP hOldPhysical hLive hStrong with
    ⟨p, g, hHost, hArc, hCases⟩
  have hOldDistance :
      grantDrainStrongProtectedDistance ring s label.host =
        PPL.cyclicOffset ring p g := by
    rw [hHost]
    exact grantDrainMarksProtectedDistanceOfArc ring s p g hArc
  rcases hCases with hStay | hMove | hBirth
  · rcases hStay with ⟨hNewHost, hNoHit, hFrame⟩
    have hStayDistance :=
      grantDrainMarksArcStableProtectedDistance ring s
        (grantDrainStep ring freshRequest updateScratch s e)
        p g hArc hFrame
    rw [hNoHit, hNewHost, hHost, hStayDistance]
    exact Nat.le_refl _
  · rcases hMove with ⟨d, hOff, hdpos, hNewHost, hFrame⟩
    have hMovingDistance :=
      grantDrainMarksArcLeftProtectedDistance ring s
        (grantDrainStep ring freshRequest updateScratch s e)
        p g d hOff hdpos hArc hFrame
    cases hHit : grantDrainLedgerNominatedHit ring s e label.host with
    | false =>
        rw [hHost] at hOldDistance
        rw [hNewHost, hHost]
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
    | true =>
        rw [hHost] at hOldDistance
        rw [hNewHost, hHost]
        simp only [↓reduceIte]
        omega
  · rcases hBirth with ⟨j, hjpos, hjlt, hNoHit, hNewHost, hNewArc⟩
    have hNewDistance :=
      grantDrainMarksProtectedDistanceOfArc ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (PPL.shiftRight ring p j) g hNewArc
    have hOffset :=
      grantDrainMarksArcOffsetSubtract ring p g j
        (Nat.le_of_lt hjlt)
    rw [hNoHit, hNewHost, hNewDistance,
      hOldDistance, hOffset]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

end L3

/-!
APPEND ONLY.  Stop at the first missing new geometric lemma.

First edge class only: x=e and y=rightNeighbor e are STRICTLY
interior to the OLD nearest protected leader-to-grant arc (p,g).
Native E then sees two zero-signal FOLLOWERS and creates no signal
on either endpoint; FIRE optionally overwrites its target with
the canonical shielded zero-signal leader.  All other old-zero
sites also remain zero.  The old host g and its physical token
coordinates are untouched.

To use this for the actual Boolean GrantDrainStrongPhysical predicate
requires one still-unproved observation-to-arc bridge:
the first-hit List.find? witness plus the List.all zero-corridor
must identify p and recover the clockwise offset-arc zero word.
That is the precise first missing structural lemma.  Nothing below
asserts GrantDrainMarksStrongArcCoverage or
GrantDrainMarksStrongPhysicalClosure unconditionally.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Exact two-follower, zero-signal pair result, for arbitrary old
bullet and shield fields: no native leader is created, and no
positive signal is generated, at either endpoint. -/
theorem grantDrainMarksInteriorPairFollowerZero
    (a b : CertNative)
    (haL : a.l = false) (hbL : b.l = false)
    (haS : a.sg = false) (hbS : b.sg = false) :
    ((certLiteralEPair a b).1.l = false ∧
     (certLiteralEPair a b).2.l = false) ∧
    ((certLiteralEPair a b).1.sg = false ∧
     (certLiteralEPair a b).2.sg = false) := by
  rcases a with ⟨al, ab, ah, asg⟩
  rcases b with ⟨bl, bb, bh, bsg⟩
  cases al with
  | true =>
      cases haL
  | false =>
      cases bl with
      | true =>
          cases hbL
      | false =>
          cases asg with
          | true =>
              cases haS
          | false =>
              cases bsg with
              | true =>
                  cases hbS
              | false =>
                  have hZero :=
                    grantDrainMarksInteriorZeroRow ab bb ah bh
                  have hLeaders :
                      (certLiteralEPair
                        { l := false, b := ab, sh := ah, sg := false }
                        { l := false, b := bb, sh := bh, sg := false }).1.l =
                          false ∧
                      (certLiteralEPair
                        { l := false, b := ab, sh := ah, sg := false }
                        { l := false, b := bb, sh := bh, sg := false }).2.l =
                          false := by
                    simp [certLiteralEPair]
                  exact ⟨hLeaders, hZero⟩

/-- Native E leaves the signal zero at ANY old zero-signal site
when the selected pair consists of zero-signal followers.
This covers both touched endpoints and all framed sites. -/
theorem grantDrainMarksInteriorNativeEZeroAt
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e i : Fin n)
    (hLX : (s.native e).l = false)
    (hLY : (s.native (ring.rightNeighbor e)).l = false)
    (hSX : (s.native e).sg = false)
    (hSY : (s.native (ring.rightNeighbor e)).sg = false)
    (hi : (s.native i).sg = false) :
    (nativeE ring s.native e i).sg = false := by
  have hPair :=
    grantDrainMarksInteriorPairFollowerZero
      (s.native e) (s.native (ring.rightNeighbor e))
      hLX hLY hSX hSY
  by_cases he : i = e
  · subst i
    simpa [nativeE] using hPair.2.1
  · by_cases hy : i = ring.rightNeighbor e
    · subst i
      simpa [nativeE, he] using hPair.2.2
    · simpa [nativeE, he, hy] using hi

/-- Native E also preserves the leader flag at EVERY ring site
when both selected OLD endpoints are followers. -/
theorem grantDrainMarksInteriorNativeELeaderAt
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e i : Fin n)
    (hLX : (s.native e).l = false)
    (hLY : (s.native (ring.rightNeighbor e)).l = false)
    (hSX : (s.native e).sg = false)
    (hSY : (s.native (ring.rightNeighbor e)).sg = false) :
    (nativeE ring s.native e i).l = (s.native i).l := by
  have hPair :=
    grantDrainMarksInteriorPairFollowerZero
      (s.native e) (s.native (ring.rightNeighbor e))
      hLX hLY hSX hSY
  by_cases he : i = e
  · subst i
    simpa [nativeE, hLX] using hPair.1.1
  · by_cases hy : i = ring.rightNeighbor e
    · subst i
      simpa [nativeE, he, hLY] using hPair.1.2
    · simp [nativeE, he, hy]

/-- Canonical-birth overwrite can never turn an old zero-signal
site into a positive-signal site.  This also works when the
overwrite is at the site itself. -/
theorem grantDrainMarksInteriorBirthPreservesZero
    {n : Nat}
    (N : Fin n → CertNative) (z i : Fin n)
    (h : (N i).sg = false) :
    (canonicalBirth N z i).sg = false := by
  by_cases hz : i = z
  · subst i
    simp [canonicalBirth, firedNative]
  · simp [canonicalBirth, hz, h]

/-- Full exact grantDrainNativeNext: irrespective of the F0/F1/F2
selector, all OLD zero-signal sites stay zero whenever native E
has two zero-signal followers.  This is the requested complete
local E-plus-birth signal-frame fact, without a ring arc assumption. -/
theorem grantDrainMarksInteriorNativeNextZeroAt
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e i : Fin n)
    (hLX : (s.native e).l = false)
    (hLY : (s.native (ring.rightNeighbor e)).l = false)
    (hSX : (s.native e).sg = false)
    (hSY : (s.native (ring.rightNeighbor e)).sg = false)
    (hi : (s.native i).sg = false) :
    (grantDrainNativeNext ring s e i).sg = false := by
  have hE :=
    grantDrainMarksInteriorNativeEZeroAt
      ring s e i hLX hLY hSX hSY hi
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      have hBirth :=
        grantDrainMarksInteriorBirthPreservesZero
          (nativeE ring s.native e) e i hE
      simpa [grantDrainNativeNext, hf] using hBirth
  | rightLocal =>
      have hBirth :=
        grantDrainMarksInteriorBirthPreservesZero
          (nativeE ring s.native e) (ring.rightNeighbor e) i hE
      simpa [grantDrainNativeNext, hf] using hBirth
  | cross =>
      have hBirth :=
        grantDrainMarksInteriorBirthPreservesZero
          (nativeE ring s.native e) e i hE
      simpa [grantDrainNativeNext, hf] using hBirth

/-- In the non-FIRE interior case, the actual native E successor
preserves the leader flag globally (not just at one endpoint). -/
theorem grantDrainMarksInteriorNoFireLeaderFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e i : Fin n)
    (hLX : (s.native e).l = false)
    (hLY : (s.native (ring.rightNeighbor e)).l = false)
    (hSX : (s.native e).sg = false)
    (hSY : (s.native (ring.rightNeighbor e)).sg = false)
    (hFire : grantDrainSelect ring s e = .none) :
    (grantDrainNativeNext ring s e i).l = (s.native i).l := by
  have hE :=
    grantDrainMarksInteriorNativeELeaderAt
      ring s e i hLX hLY hSX hSY
  simpa [grantDrainNativeNext, hFire] using hE

/-- Clockwise zero-signal prefix, expressed by the cyclicOffset
coordinates. The endpoint g itself is excluded. -/
def GrantDrainMarksZeroOffsetArc
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p g : Fin n) : Prop :=
  ∀ k : Nat, k < PPL.cyclicOffset ring p g →
    (N (PPL.shiftRight ring p k)).sg = false

/-- A selected edge is strictly inside the arc: BOTH selected
sites have offsets in (0, cyclicOffset p g). -/
def GrantDrainMarksStrictInteriorEdge
    {n : Nat}
    (ring : DirectedRing n)
    (p g e : Fin n) : Prop :=
  0 < PPL.cyclicOffset ring p e ∧
  PPL.cyclicOffset ring p e < PPL.cyclicOffset ring p g ∧
  0 < PPL.cyclicOffset ring p (ring.rightNeighbor e) ∧
  PPL.cyclicOffset ring p (ring.rightNeighbor e) <
    PPL.cyclicOffset ring p g

/-- A fully cyclic-offset version of the requested first edge class.
It proves the ENTIRE old protected corridor stays zero-signal
after E+canonical FIRE, not merely the two sites of the interaction.
The prerequisites are physical OLD arc certificates, not a
conclusion smuggled in through the new state. -/
theorem grantDrainMarksStrictInteriorZeroArcStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g e : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) p g := by
  rcases hInside with ⟨hXpos, hXlt, hYpos, hYlt⟩
  have hSiteX := grantDrainMarksArcShiftRightOffset ring p e
  have hSiteY :=
    grantDrainMarksArcShiftRightOffset ring p (ring.rightNeighbor e)
  have hLX : (s.native e).l = false := by
    have h := hNearest.2.2
      (PPL.cyclicOffset ring p e) hXpos hXlt
    rw [hSiteX] at h
    exact h
  have hLY : (s.native (ring.rightNeighbor e)).l = false := by
    have h := hNearest.2.2
      (PPL.cyclicOffset ring p (ring.rightNeighbor e)) hYpos hYlt
    rw [hSiteY] at h
    exact h
  have hSX : (s.native e).sg = false := by
    have h := hZero (PPL.cyclicOffset ring p e) hXlt
    rw [hSiteX] at h
    exact h
  have hSY : (s.native (ring.rightNeighbor e)).sg = false := by
    have h := hZero
      (PPL.cyclicOffset ring p (ring.rightNeighbor e)) hYlt
    rw [hSiteY] at h
    exact h
  intro k hk
  exact grantDrainMarksInteriorNativeNextZeroAt
    ring s e (PPL.shiftRight ring p k) hLX hLY hSX hSY
    (hZero k hk)

/-- A strict interior edge touches neither p nor the current
physical grant host g.  This converts cyclic-offset inequalities
to the inequalities used by the source host/physical-step frames. -/
theorem grantDrainMarksStrictInteriorAvoidEndpoints
    {n : Nat}
    (ring : DirectedRing n)
    (p g e : Fin n)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e) :
    e ≠ p ∧ ring.rightNeighbor e ≠ p ∧
      e ≠ g ∧ ring.rightNeighbor e ≠ g := by
  rcases hInside with ⟨hXpos, hXlt, hYpos, hYlt⟩
  have hXP : e ≠ p := by
    intro h
    rw [h, grantDrainMarksArcOffsetZero ring p] at hXpos
    omega
  have hYP : ring.rightNeighbor e ≠ p := by
    intro h
    rw [h, grantDrainMarksArcOffsetZero ring p] at hYpos
    omega
  have hXG : e ≠ g := by
    intro h
    rw [h] at hXlt
    omega
  have hYG : ring.rightNeighbor e ≠ g := by
    intro h
    rw [h] at hYlt
    omega
  exact ⟨hXP, hYP, hXG, hYG⟩

/-- When an edge is away from the label's old host, the proof-only
host stays at that site (no spontaneous Y-to-X ancestry). -/
theorem grantDrainMarksInteriorHostFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hHost : label.host = some g)
    (hX : g ≠ e) (hY : g ≠ ring.rightNeighbor e) :
    grantDrainLedgerHost ring freshRequest s e label.host =
      some g := by
  simp [grantDrainLedgerHost, hHost, hX, hY]

/-- The actual source step also frames both token coordinates at
an untouched host.  Hostile fresh responder requests cannot target
an unrelated site. -/
theorem grantDrainMarksInteriorTokenFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e g : Fin n)
    (hX : g ≠ e) (hY : g ≠ ring.rightNeighbor e) :
    (grantDrainStep ring freshRequest updateScratch s e).request g =
        s.request g ∧
    (grantDrainStep ring freshRequest updateScratch s e).grant g =
        s.grant g := by
  constructor
  · simp [grantDrainStep, hX, hY]
  · simp [grantDrainStep, hX, hY]

/-- The SOURCE-TO-CYCLIC-ARC CONVERSION is the first missing lemma
when instantiating the strict-interior result from
GrantDrainStrongPhysical rather than a manually nominated p.

The source grantDrainLedgerStrongLock is Boolean:
  d := grantDrainLeftLeaderDistance ...
  p := shiftLeft g d
  (N p).l && List.all (signals on g-1,...,p) && (N p).sh
The missing proof must show, on PPlus and follower g, that this
first-hit d is a genuine cyclicOffset(p,g) in 1,...,n-1 and that
the List.all order is exactly the clockwise signal-zero interval.
This is a named Prop, NOT a theorem, axiom or assumption globally. -/
def GrantDrainMarksStrongLockToOffsetArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (g : Fin n) : Prop :=
  PPlus ring s.native →
  (s.native g).l = false →
  grantDrainLedgerStrongLock ring s g = true →
  ∃ p : Fin n,
    GrantDrainMarksNearestArc ring s.native p g ∧
    GrantDrainMarksZeroOffsetArc ring s.native p g ∧
    (s.native p).sh = true

/-- Conditional use of the exact missing observation lemma:
it converts a strong proof-only label at g to the whole-arc zero
transition whenever the selected edge is STRICTLY interior. -/
theorem grantDrainMarksStrictInteriorZeroFromStrongOfBridge
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hBridge : ∀ g : Fin n,
      GrantDrainMarksStrongLockToOffsetArc ring s g)
    (hInterior : ∀ p g : Fin n,
      label.host = some g →
      GrantDrainMarksNearestArc ring s.native p g →
      GrantDrainMarksStrictInteriorEdge ring p g e) :
    ∃ p g : Fin n,
      label.host = some g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) p g := by
  rcases hPhysical with
    ⟨g, hHost, hMark, hGrant, hRequest, hLeader, hLock⟩
  rcases hBridge g hP hLeader hLock with
    ⟨p, hNearest, hZero, hShield⟩
  exact ⟨p, g, hHost,
    grantDrainMarksStrictInteriorZeroArcStep ring s p g e
      hNearest hZero (hInterior p g hHost hNearest)⟩

/-!
STOP at class (1), strictly interior to the D.1 arc.

The finite two-follower row, global old-zero-site preservation
under nativeE+canonicalBirth, full cyclic-offset zero-arc update,
untouched host and token fields are supplied above.

FIRST MISSING NEW IDEA:
  GrantDrainMarksStrongLockToOffsetArc
needs the REVERSE of the earlier nearest-arc -> List.find? scan theorem,
including (i) the first-hit witness of the existing List.find? and
(ii) the exact List.all signal word reindexing.  Without it, we
cannot instantiate the strong physical predicate's hidden p and
prove the requested unconditional
GrantDrainMarksStrongPhysicalClosure / GrantDrainMarksStrongArcCoverage.
The original target names are unchanged. Cases (2)-(4) are not
claimed to be discharged in this stop-at-first-gap round.
-/

end L3

/-!
Boolean strong-lock observer -> cyclic-offset D.1 arc.

This section establishes the reverse of the scan implication
by explicitly deriving a first hit of the one-through-n search,
then reindexing the reversed List.all zero corridor.

The next physical edge case is e=p, including p->g when g=p+1.
Only its local leader/sink rows are proved here.  The
complete six-position StrongArcCoverage/StrongPhysicalClosure
obligations are still not proved.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Converse of the first-hit lemma. The first successful
element of [start, start+length) has no earlier successes. -/
private theorem grantDrainMarksAndTrue {a b : Bool}
    (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem grantDrainMarksFindRangeConverse (f : Nat → Bool) :
    ∀ length start d,
      (List.range' start length).find? f = some d →
      start ≤ d ∧ d < start + length ∧ f d = true ∧
        (∀ k : Nat, start ≤ k → k < d → f k = false) := by
  intro length
  induction length with
  | zero =>
      intro start d h
      simp [List.range'] at h
  | succ length ih =>
      intro start d h
      cases hf : f start with
      | true =>
          have hd : d = start := by
            have hh : some start = some d := by
              simpa [List.range'_succ, List.find?_cons, hf] using h
            exact (Option.some.inj hh).symm
          subst d
          refine ⟨by omega, by omega, hf, ?_⟩
          intro k hk hkd
          omega
      | false =>
          have ht :
              (List.range' (start + 1) length).find? f =
                some d := by
            simpa [List.range'_succ, List.find?_cons, hf] using h
          rcases ih (start + 1) d ht with
            ⟨hlo, hhi, hval, hbefore⟩
          refine ⟨by omega, by omega, hval, ?_⟩
          intro k hk hkd
          by_cases heq : k = start
          · rw [heq]
            exact hf
          · exact hbefore k (by omega) hkd

/-- The reverse-direction List.all proof, by induction over the
same consecutive range. Each member passes the Boolean test. -/
private theorem grantDrainMarksAllRangeConverse (f : Nat → Bool) :
    ∀ length start,
      (List.range' start length).all f = true →
      ∀ k : Nat, start ≤ k → k < start + length →
        f k = true := by
  intro length
  induction length with
  | zero =>
      intro start h k hk hlt
      omega
  | succ length ih =>
      intro start h k hk hlt
      have hPair :
          f start = true ∧
          (List.range' (start + 1) length).all f = true := by
        have hRaw :
            (f start &&
              (List.range' (start + 1) length).all f) = true := by
          simpa [List.range'_succ, List.all_cons] using h
        exact grantDrainMarksAndTrue hRaw
      by_cases heq : k = start
      · rw [heq]
        exact hPair.1
      · exact ih (start + 1) hPair.2 k (by omega) (by omega)

/-- Shifting left by the entire ring size fixes a site. -/
private theorem grantDrainMarksShiftLeftFull
    {n : Nat} (ring : DirectedRing n) (g : Fin n) :
    PPL.shiftLeft ring g n = g := by
  apply Fin.ext
  change (g.val + n - n % n) % n = g.val
  rw [Nat.mod_self, Nat.sub_zero, Nat.add_mod_right,
    Nat.mod_eq_of_lt g.isLt]

/-- The inverse group law for the actual PPL.shiftLeft definition.
No imported cyclic group library or extra Leader.L3 import. -/
private theorem grantDrainMarksShiftLeftRightCancel
    {n : Nat} (ring : DirectedRing n) (g : Fin n)
    (d : Nat) (hd : d < n) :
    PPL.shiftRight ring (PPL.shiftLeft ring g d) d = g := by
  apply Fin.ext
  change (((g.val + n - d % n) % n + d) % n) = g.val
  rw [Nat.mod_eq_of_lt hd]
  by_cases hge : d ≤ g.val
  · have he : g.val + n - d = n + (g.val - d) := by omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : g.val - d < n)]
    have hs : g.val - d + d = g.val := by omega
    rw [hs, Nat.mod_eq_of_lt g.isLt]
  · have hlt : g.val + n - d < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hs : g.val + n - d + d = g.val + n := by omega
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt g.isLt]

/-- The clockwise offset from a first-hit predecessor back to g
is precisely the first-hit distance d, as long as d<n. -/
private theorem grantDrainMarksShiftLeftOffset
    {n : Nat} (ring : DirectedRing n) (g : Fin n)
    (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring (PPL.shiftLeft ring g d) g = d := by
  have ho :=
    grantDrainMarksArcOffsetShiftRight ring
      (PPL.shiftLeft ring g d) d hd
  rw [grantDrainMarksShiftLeftRightCancel ring g d hd] at ho
  exact ho

/-- Rootedness and an OLD follower g force a successful positive
leader scan. This rules out the getD n fallback; no choice axiom. -/
private theorem grantDrainMarksRootedScanHasHit
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (hRoot : ∃ p : Fin n, (N p).l = true)
    (hFollower : (N g).l = false) :
    ∃ d : Nat,
      (List.range' 1 n).find?
        (fun k => (N (PPL.shiftLeft ring g k)).l) = some d := by
  rcases hRoot with ⟨p, hp⟩
  have hDistancePositive :
      0 < PPL.cyclicOffset ring p g := by
    by_cases hz : PPL.cyclicOffset ring p g = 0
    · have hs := grantDrainMarksArcShiftRightOffset ring p g
      rw [hz, grantDrainMarksArcShiftRightZero ring p] at hs
      rw [hs, hFollower] at hp
      cases hp
    · omega
  have hdlt := grantDrainMarksArcOffsetLt ring p g
  have hSite :
      PPL.shiftLeft ring g (PPL.cyclicOffset ring p g) = p := by
    have hs :=
      grantDrainMarksArcShiftLeftRight ring p
        (PPL.cyclicOffset ring p g)
        (PPL.cyclicOffset ring p g) (Nat.le_refl _) hdlt
    rw [grantDrainMarksArcShiftRightOffset ring p g] at hs
    simpa [grantDrainMarksArcShiftRightZero] using hs
  have hAt :
      (N (PPL.shiftLeft ring g
        (PPL.cyclicOffset ring p g))).l = true := by
    rw [hSite]
    exact hp
  have hMem :
      PPL.cyclicOffset ring p g ∈ List.range' 1 n := by
    apply (List.mem_range').2
    refine ⟨PPL.cyclicOffset ring p g - 1, by omega, ?_⟩
    omega
  cases hf :
      (List.range' 1 n).find?
        (fun k => (N (PPL.shiftLeft ring g k)).l) with
  | none =>
      have hAbsent :=
        (List.find?_eq_none.mp hf)
          (PPL.cyclicOffset ring p g) hMem
      simp [hAt] at hAbsent
  | some d =>
      exact ⟨d, rfl⟩

/-- The actual grantDrainLeftLeaderDistance is a first successful
distance 1<=d<n for a follower in a rooted native state. -/
private theorem grantDrainMarksRootedScanFirst
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n)
    (hRoot : ∃ p : Fin n, (N p).l = true)
    (hFollower : (N g).l = false) :
    ∃ d : Nat,
      grantDrainLeftLeaderDistance ring N g = d ∧
      1 ≤ d ∧ d < n ∧
      (N (PPL.shiftLeft ring g d)).l = true ∧
      (∀ k : Nat, 1 ≤ k → k < d →
        (N (PPL.shiftLeft ring g k)).l = false) := by
  rcases grantDrainMarksRootedScanHasHit
      ring N g hRoot hFollower with ⟨d, hFound⟩
  rcases grantDrainMarksFindRangeConverse
      (fun k => (N (PPL.shiftLeft ring g k)).l)
      n 1 d hFound with ⟨hPositive, hBound, hAt, hBefore⟩
  have hdlt : d < n := by
    by_cases heq : d = n
    · have hBad := hAt
      rw [heq, grantDrainMarksShiftLeftFull ring g,
        hFollower] at hBad
      cases hBad
    · omega
  have hDistance :
      grantDrainLeftLeaderDistance ring N g = d := by
    change (((List.range n).map (fun k : Nat => k + 1)).find?
      (fun k => (N (PPL.shiftLeft ring g k)).l)).getD n = d
    rw [grantDrainMarksDistanceRange, hFound]
    rfl
  exact ⟨d, hDistance, hPositive, hdlt, hAt,
    fun k hk hkd => hBefore k hk hkd⟩

/-- First-hit scan -> cyclic-offset nearest-source certificate.
This is the logical converse of the earlier ScanOfNearestArc. -/
private theorem grantDrainMarksFirstHitToNearestArc
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d : Nat)
    (hPositive : 1 ≤ d) (hdlt : d < n)
    (hLeader : (N (PPL.shiftLeft ring g d)).l = true)
    (hEarlier : ∀ k : Nat, 1 ≤ k → k < d →
      (N (PPL.shiftLeft ring g k)).l = false) :
    GrantDrainMarksNearestArc ring N
      (PPL.shiftLeft ring g d) g := by
  have hCancel :=
    grantDrainMarksShiftLeftRightCancel ring g d hdlt
  have hOff :=
    grantDrainMarksShiftLeftOffset ring g d hdlt
  refine ⟨?_, hLeader, ?_⟩
  · rw [hOff]
    omega
  · intro k hk hkd
    rw [hOff] at hkd
    have hs :=
      grantDrainMarksArcShiftLeftRight ring
        (PPL.shiftLeft ring g d) d (d - k)
        (by omega) hdlt
    rw [hCancel] at hs
    have hSub : d - (d - k) = k := by omega
    rw [hSub] at hs
    have hOld := hEarlier (d - k) (by omega) (by omega)
    rw [hs] at hOld
    exact hOld

/-- Reverse-order List.all -> clockwise zero-signal prefix.
The k-th clockwise site p+k is g-(d-k), and the List.range
index supplying its zero signal is d-k-1. -/
private theorem grantDrainMarksAllToOffsetZeroArc
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (g : Fin n) (d : Nat)
    (hdlt : d < n)
    (hAll : (List.range d).all
      (fun k => !(N (PPL.shiftLeft ring g (k + 1))).sg) = true) :
    GrantDrainMarksZeroOffsetArc ring N
      (PPL.shiftLeft ring g d) g := by
  intro k hk
  have hCancel :=
    grantDrainMarksShiftLeftRightCancel ring g d hdlt
  have hOff :=
    grantDrainMarksShiftLeftOffset ring g d hdlt
  rw [hOff] at hk
  have hAllRange :
      (List.range' 0 d).all
        (fun j => !(N (PPL.shiftLeft ring g (j + 1))).sg) =
          true := by
    simpa [List.range_eq_range'] using hAll
  have hAt :=
    grantDrainMarksAllRangeConverse
      (fun j => !(N (PPL.shiftLeft ring g (j + 1))).sg)
      d 0 hAllRange (d - k - 1) (by omega) (by omega)
  have hIndex : d - k - 1 + 1 = d - k := by omega
  rw [hIndex] at hAt
  have hSig :
      (N (PPL.shiftLeft ring g (d - k))).sg = false := by
    cases hs : (N (PPL.shiftLeft ring g (d - k))).sg with
    | false => rfl
    | true => simp [hs] at hAt
  have hShift :=
    grantDrainMarksArcShiftLeftRight ring
      (PPL.shiftLeft ring g d) d (d - k) (by omega) hdlt
  rw [hCancel] at hShift
  have hSub : d - (d - k) = k := by omega
  rw [hSub] at hShift
  rw [hShift] at hSig
  exact hSig

/-- The earlier EXACT named target, now proved from its definitions.
Rooted PPlus rules out a missing leader; the host is a follower;
the Boolean lock gives both the zero word and shield at the
actual first-hit predecessor p. No extra invariant is assumed. -/
theorem grantDrainMarksStrongLockToOffsetArc_proved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (g : Fin n) :
    GrantDrainMarksStrongLockToOffsetArc ring s g := by
  intro hP hFollower hLock
  rcases grantDrainMarksRootedScanFirst
      ring s.native g hP.1 hFollower with
    ⟨d, hDistance, hPositive, hdlt, hLeader, hEarlier⟩
  have hLockPair :
      grantDrainLedgerCorridor ring s g = true ∧
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).sh =
          true := by
    change (grantDrainLedgerCorridor ring s g &&
      (s.native (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring s.native g))).sh) =
        true at hLock
    exact grantDrainMarksAndTrue hLock
  have hShield :
      (s.native (PPL.shiftLeft ring g d)).sh = true := by
    have hs := hLockPair.2
    rw [hDistance] at hs
    exact hs
  have hCorridor :
      ((s.native (PPL.shiftLeft ring g d)).l &&
        (List.range d).all (fun k =>
          !(s.native (PPL.shiftLeft ring g (k + 1))).sg)) =
        true := by
    have hc := hLockPair.1
    change ((s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g))).l &&
      (List.range
        (grantDrainLeftLeaderDistance ring s.native g)).all
          (fun k => !(s.native
            (PPL.shiftLeft ring g (k + 1))).sg)) = true at hc
    rw [hDistance] at hc
    exact hc
  have hAll :
      (List.range d).all
        (fun k => !(s.native
          (PPL.shiftLeft ring g (k + 1))).sg) = true :=
    (grantDrainMarksAndTrue hCorridor).2
  refine ⟨PPL.shiftLeft ring g d, ?_, ?_, hShield⟩
  · exact grantDrainMarksFirstHitToNearestArc
      ring s.native g d hPositive hdlt hLeader hEarlier
  · exact grantDrainMarksAllToOffsetZeroArc
      ring s.native g d hdlt hAll

/-- The newly proved bridge, applied directly to the exact
GrantDrainStrongPhysical observation of a tracked live label. -/
theorem grantDrainMarksStrongPhysicalHasOffsetArc
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label) :
    ∃ p g : Fin n,
      label.host = some g ∧
      GrantDrainMarksNearestArc ring s.native p g ∧
      GrantDrainMarksZeroOffsetArc ring s.native p g ∧
      (s.native p).sh = true := by
  rcases hPhysical with
    ⟨g, hHost, hMark, hGrant, hRequest, hFollower, hLock⟩
  rcases grantDrainMarksStrongLockToOffsetArc_proved
      ring s g hP hFollower hLock with
    ⟨p, hNearest, hZero, hShield⟩
  exact ⟨p, g, hHost, hNearest, hZero, hShield⟩

/-! The next edge class: source-outgoing e=p. If g is immediately
to its right, the responder grant is sunk by the final leader at p.
The native source p always retains its leader flag under E,
although it may receive S=1 from a signal-one responder. -/

/-- E never deletes the old initiator leader, for ANY endpoint
records. This is independent of the responder's bullet and signal. -/
theorem grantDrainMarksOutgoingSourceLeaderNative
    (a b : CertNative) :
    (certLiteralEPair a b).1.l = a.l := by
  rfl

/-- Token-owner cross-sink row: if the final initiator is a leader,
an OLD responder grant is sunk. This includes OLD HOLD, every FIRE
selector and any hostile fresh responder request. -/
theorem grantDrainMarksOutgoingSourceLeaderSinksY
    (rx gx ry ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx ry true true ly fresh fire).2.grant =
      false := by
  cases rx <;> cases gx <;> cases ry <;> cases ly <;>
    cases fresh <;> cases fire <;> decide

/-- Remaining precise row-to-source obligation at e=p:
when OLD p is a shielded, zero-signal protected leader and its
responder is a follower g (possibly signal-one), the actual
grantDrainNativeNext has p.l=true.  This requires excluding F0/F2
birth at p via the post-E FIRE eligibility and then framing p
through F1, rather than using just a standalone E row.

Once it is proved, the preceding token row immediately retires
the adjacent old responder grant.  The longer-source-outgoing
case then uses the earlier protected zero-signal outgoing native row
and the arc frame, with a possible F1 closer birth.

No assertion of the still-open universal StrongArcCoverage or
StrongPhysicalClosure is made here. -/
def GrantDrainMarksProtectedSourceOutgoingLeaderFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p : Fin n) : Prop :=
  (s.native p).l = true →
  (s.native p).sh = true →
  (s.native p).sg = false →
  (grantDrainNativeNext ring s p p).l = true

end L3

/-!
SOURCE-ROW REFINEMENT: the preceding named out-of-p
frame is actually elementary: native E preserves the initiator's
leader flag, and canonicalBirth writes a leader if it overwrites
that same site.  The FIRE selector need not be restricted.
This closes the adjacent e=p, y=g sink case physically.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Literal native E at its own initiator is the first component
of the literal pair. -/
theorem grantDrainMarksNativeESource {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative) (e : Fin n) :
    nativeE ring N e e =
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).1 := by
  unfold nativeE
  exact if_pos rfl

/-- Any native leader at the selected initiator survives E and
the optional canonical FIRE at either endpoint. In particular the
protected source p is a final leader on its outgoing service. -/
theorem grantDrainMarksOutgoingLeaderNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p : Fin n)
    (hLeader : (s.native p).l = true) :
    (grantDrainNativeNext ring s p p).l = true := by
  have hE : (nativeE ring s.native p p).l = true := by
    rw [grantDrainMarksNativeESource,
      grantDrainMarksOutgoingSourceLeaderNative]
    exact hLeader
  cases hf : grantDrainSelect ring s p with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | cross =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | rightLocal =>
      by_cases hy : p = ring.rightNeighbor p
      · simp [grantDrainNativeNext, hf, canonicalBirth, ← hy,
          firedNative]
      · simpa [grantDrainNativeNext, hf, canonicalBirth, hy]
          using hE

/-- The exact previously named source-outgoing leader-frame
obligation is proved, not merely stipulated. -/
theorem grantDrainMarksProtectedSourceOutgoingLeaderFrame_proved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p : Fin n) :
    GrantDrainMarksProtectedSourceOutgoingLeaderFrame ring s p := by
  intro hLeader hShield hZero
  exact grantDrainMarksOutgoingLeaderNext ring s p hLeader

/-- The final X native leader sinks both X and Y physical grants.
The Y half was already isolated above. -/
theorem grantDrainMarksOutgoingSourceLeaderSinksPair
    (rx gx ry ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx ry true true ly fresh fire).1.grant =
      false ∧
    (grantDrainTokenRow rx gx ry true true ly fresh fire).2.grant =
      false := by
  cases rx <;> cases gx <;> cases ry <;> cases ly <;>
    cases fresh <;> cases fire <;>
    simp [grantDrainTokenRow] <;> decide

/-- Complete adjacent p->g source-row sink on the ACTUAL source
grantDrainStep.  The host g is a follower carrying an OLD grant;
no condition on its signal, bullet, or request is required.
When p is its protected predecessor, this is precisely d=1. -/
theorem grantDrainMarksOutgoingLeaderAdjacentGrantSunk
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g : Fin n)
    (hNeighbor : ring.rightNeighbor p = g)
    (hLeader : (s.native p).l = true)
    (hFollower : (s.native g).l = false)
    (hGrant : s.grant g = true) :
    (grantDrainStep ring freshRequest updateScratch s p).grant g =
      false := by
  have hDistinct : g ≠ p := by
    intro h
    rw [h, hLeader] at hFollower
    cases hFollower
  have hFinal :=
    grantDrainMarksOutgoingLeaderNext ring s p hLeader
  have hRow :
      (grantDrainLedgerRow ring freshRequest s p).2.grant = false := by
    unfold grantDrainLedgerRow
    rw [hNeighbor, hGrant, hFinal]
    exact (grantDrainMarksOutgoingSourceLeaderSinksPair
      (s.request p) (s.grant p) (s.request g)
      (grantDrainNativeNext ring s p g).l
      (freshRequest s p) (grantDrainSelect ring s p)).2
  change (if g = p then
      (grantDrainLedgerRow ring freshRequest s p).1.grant
    else if g = ring.rightNeighbor p then
      (grantDrainLedgerRow ring freshRequest s p).2.grant
    else s.grant g) = false
  simp [hDistinct, hNeighbor, hRow]

/-!
NEXT FIRST UNSOLVED PHYSICAL CASE:
e=p, with old protected nearest predecessor p, host g farther
than its immediate right neighbor.  On this edge the responder
p+1 is an interior zero-signal follower.  Native E preserves p
and the zero corridor; if F1 fires at p+1, its newborn leader is
the closer source.  Closing the ORIGINAL
GrantDrainMarksStrongArcCoverage and
GrantDrainMarksStrongPhysicalClosure simultaneously needs the
post-E successor arc's nearest-leader/zero-word classification,
including the coalesced label's post-state request/mark.
This precise source-level arc/label stitching has not been
proved.  No claims are made for into-p or out-of-g.
-/

end L3

/-!
Source outgoing priority, then incoming-to-protected-p
native/arc geometry.

The theorem
grantDrainMarksProtectedSourceOutgoingLeaderFrame_proved
already proves the requested Prop.  The new selector lemma below
additionally rules out F0/F2 when the OLD initiator is a leader.

Stop at the next proof-only ownership seam, not at an invented
counterexample: an incoming-to-p service can have initiator e=g
when d=n-1.  The physical protected zero arc is preserved, but
turning that into the complete surviving-label mark/host/old-request
frame (required by the two original global Props) still needs
the full token-owner FIRE/no-sink case split.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- An old initiator leader is still a leader after literal native E.
The source leader bit is never deleted by the initiator branch. -/
theorem grantDrainMarksOutgoingOldLeaderPostE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native e).l = true) :
    (nativeE ring s.native e e).l = true := by
  rw [grantDrainMarksNativeESource,
    grantDrainMarksOutgoingSourceLeaderNative]
  exact hLeader

/-- F0 and F2 both require post-E initiator eligibility.
An OLD initiator leader makes that eligibility false. -/
theorem grantDrainMarksOutgoingLeaderIneligible
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native e).l = true) :
    grantDrainEligible (nativeE ring s.native e) e = false := by
  have hPost := grantDrainMarksOutgoingOldLeaderPostE
    ring s e hLeader
  simp [grantDrainEligible, hPost]

/-- Direct audit of the F0/F1/F2 priority: an OLD initiator leader
can select only F1 at the RESPONDER or no FIRE.
This strengthens the unconditional leader-next theorem. -/
theorem grantDrainMarksOutgoingLeaderSelector
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native e).l = true) :
    grantDrainSelect ring s e = .none ∨
      grantDrainSelect ring s e = .rightLocal := by
  have he := grantDrainMarksOutgoingLeaderIneligible
    ring s e hLeader
  unfold grantDrainSelect
  simp [he]
  cases grantDrainEligible (nativeE ring s.native e)
      (ring.rightNeighbor e) <;>
    cases s.request (ring.rightNeighbor e) <;>
    cases s.grant (ring.rightNeighbor e) <;> simp

/-- Restate the original outgoing-leader target through the
already-existing complete proof, with the priority restriction
available as a separate, stronger diagnostic. -/
theorem grantDrainMarksOutgoingLeaderFrameFromSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    GrantDrainMarksProtectedSourceOutgoingLeaderFrame ring s e := by
  intro hLeader hShield hSignal
  have hOnly := grantDrainMarksOutgoingLeaderSelector
    ring s e hLeader
  exact grantDrainMarksOutgoingLeaderNext ring s e hLeader

/-- Two sites on a ring of size at least three cannot coincide
across one directed edge. -/
theorem grantDrainMarksNeighborDistinct
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- A shielded zero-signal responder leader is entirely unchanged
by literal native E, regardless of the initiator bullet, shield
or signal (including a LIVE bullet). -/
theorem grantDrainMarksIncomingProtectedPairIdentity
    (a b : CertNative)
    (hLeader : b.l = true)
    (hShield : b.sh = true)
    (hSignal : b.sg = false) :
    (certLiteralEPair a b).2 = b := by
  cases b with
  | mk l bullet sh sg =>
      cases l with
      | false => cases hLeader
      | true =>
          cases sh with
          | false => cases hShield
          | true =>
              cases sg with
              | true => cases hSignal
              | false =>
                  exact grantDrainMarksShieldedZeroResponderRow
                    a bullet

/-- Lift the arbitrary-initiator pair identity to the actual nativeE
at the responder. -/
theorem grantDrainMarksIncomingProtectedNativeE
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hShield :
      (s.native (ring.rightNeighbor e)).sh = true)
    (hSignal :
      (s.native (ring.rightNeighbor e)).sg = false) :
    nativeE ring s.native e (ring.rightNeighbor e) =
      s.native (ring.rightNeighbor e) := by
  have hNe := grantDrainMarksNeighborDistinct hn ring e
  have hPair :=
    grantDrainMarksIncomingProtectedPairIdentity
      (s.native e) (s.native (ring.rightNeighbor e))
      hLeader hShield hSignal
  change
    (if ring.rightNeighbor e = e then
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).1
    else if ring.rightNeighbor e = ring.rightNeighbor e then
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2
    else s.native (ring.rightNeighbor e)) =
      s.native (ring.rightNeighbor e)
  simpa only [if_neg hNe, if_pos rfl, ↓reduceIte] using hPair

/-- Even a hypothetical F1 overwrite at the protected responder
would write firedNative, preserving (leader,shield,signal)=(1,1,0).
F0/F2 overwrite only the initiator.  Thus the actual source
grantDrainNativeNext retains a protected zero-signal leader. -/
theorem grantDrainMarksIncomingProtectedNativeNext
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hShield :
      (s.native (ring.rightNeighbor e)).sh = true)
    (hSignal :
      (s.native (ring.rightNeighbor e)).sg = false) :
    (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).l = true ∧
    (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).sh = true ∧
    (grantDrainNativeNext ring s e
      (ring.rightNeighbor e)).sg = false := by
  have hNe := grantDrainMarksNeighborDistinct hn ring e
  have hE :=
    grantDrainMarksIncomingProtectedNativeE
      hn ring s e hLeader hShield hSignal
  have hBefore :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = true ∧
      (nativeE ring s.native e
        (ring.rightNeighbor e)).sh = true ∧
      (nativeE ring s.native e
        (ring.rightNeighbor e)).sg = false := by
    rw [hE]
    exact ⟨hLeader, hShield, hSignal⟩
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hBefore
  | leftLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hNe]
        using hBefore
  | rightLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | cross =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hNe]
        using hBefore

/-- The incoming source site is the last clockwise position before
p.  This is the exact cyclicOffset geometry of an edge e -> p. -/
theorem grantDrainMarksIncomingSourceOffset
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n) (p e : Fin n)
    (hIncoming : ring.rightNeighbor e = p) :
    PPL.cyclicOffset ring p e = n - 1 := by
  have hVal := congrArg Fin.val hIncoming
  change (e.val + 1) % n = p.val at hVal
  unfold PPL.cyclicOffset
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hVal
    have hOffset : e.val + n - p.val = n - 1 := by omega
    rw [hOffset, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  · have hEq : e.val + 1 = n := by omega
    rw [hEq, Nat.mod_self] at hVal
    have hOffset : e.val + n - p.val = n + (n - 1) := by
      omega
    rw [hOffset, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : n - 1 < n)]

/-- An incoming edge e -> p never touches a site strictly INSIDE
the old clockwise arc [p,g), including its source p; the only
exceptional touched arc site is p itself (the responder), which
the protected native row handles separately. -/
theorem grantDrainMarksIncomingSourceArcExceptRoot
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (p g e : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (k : Nat)
    (hk : k < PPL.cyclicOffset ring p g) :
    PPL.shiftRight ring p k ≠ e := by
  have hlt : k < n :=
    Nat.lt_trans hk (grantDrainMarksArcOffsetLt ring p g)
  have hOffset :=
    grantDrainMarksIncomingSourceOffset hn ring p e hIncoming
  intro h
  have hEqual := congrArg (PPL.cyclicOffset ring p) h
  rw [grantDrainMarksArcOffsetShiftRight ring p k hlt,
    hOffset] at hEqual
  have hgLt := grantDrainMarksArcOffsetLt ring p g
  omega

/-- For positive k in the old arc, the selected incoming-to-p
edge touches neither site p+k; this is a complete per-site native
frame, including any canonical FIRE. -/
theorem grantDrainMarksIncomingSourceInteriorFrame
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g e : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (k : Nat)
    (hk : 0 < k)
    (hklt : k < PPL.cyclicOffset ring p g) :
    grantDrainNativeNext ring s e
        (PPL.shiftRight ring p k) =
      s.native (PPL.shiftRight ring p k) := by
  have hX :=
    grantDrainMarksIncomingSourceArcExceptRoot
      hn ring p g e hIncoming k hklt
  have hY : PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
    rw [hIncoming]
    intro h
    have hVal := congrArg (PPL.cyclicOffset ring p) h
    rw [grantDrainMarksArcOffsetShiftRight ring p k
      (Nat.lt_trans hklt (grantDrainMarksArcOffsetLt ring p g)),
      grantDrainMarksArcOffsetZero ring p] at hVal
    omega
  exact grantDrainMarksNativeOutsidePairFrame
    ring s e (PPL.shiftRight ring p k) hX hY

/-- Protected p survives the incoming service and the ENTIRE
clockwise zero corridor [p,g) remains signal zero.  This is not
yet a label-transport or StrongPhysicalClosure theorem. -/
theorem grantDrainMarksIncomingSourceZeroArc
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g e : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hLeader : (s.native p).l = true)
    (hShield : (s.native p).sh = true)
    (hSignal : (s.native p).sg = false)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g) :
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) p g := by
  have hP :=
    grantDrainMarksIncomingProtectedNativeNext
      hn ring s e (by simpa [hIncoming] using hLeader)
      (by simpa [hIncoming] using hShield)
      (by simpa [hIncoming] using hSignal)
  intro k hk
  by_cases hz : k = 0
  · subst k
    simpa [grantDrainMarksArcShiftRightZero, hIncoming]
      using hP.2.2
  · have hFrame :=
      grantDrainMarksIncomingSourceInteriorFrame
        hn ring s p g e hIncoming k (by omega) hk
    rw [hFrame]
    exact hZero k hk

/-- The same edge preserves the FIRST preceding leader p on [p,g).
All positive offsets stay follower, and protected p remains leader.
This is the cyclic entire-arc lift for incoming-to-p native E/FIRE. -/
theorem grantDrainMarksIncomingSourceNearestArc
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g e : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hSignal : (s.native p).sg = false) :
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s e) p g := by
  have hP :=
    grantDrainMarksIncomingProtectedNativeNext
      hn ring s e (by simpa [hIncoming] using hNearest.2.1)
      (by simpa [hIncoming] using hShield)
      (by simpa [hIncoming] using hSignal)
  refine ⟨hNearest.1, ?_, ?_⟩
  · simpa [hIncoming] using hP.1
  · intro k hk hklt
    have hFrame :=
      grantDrainMarksIncomingSourceInteriorFrame
        hn ring s p g e hIncoming k hk hklt
    rw [hFrame]
    exact hNearest.2.2 k hk hklt

/-!
FIRST REMAINING SOURCE-LEVEL SEAM AFTER THE TWO ARC LIFTS:

For e->p and a strong-marked live label hosted at follower g,
prove on the literal grantDrainTokenRow and GrantDrainLedgerHost
that the label remains at g and remains unheld, even when
e=g (i.e. the old source distance equals n-1).  In that boundary
case FIRE must not consume the old grant at e because Rx=false,
F1 cannot occur because the responder p is a surviving leader,
and finalLX=false, so the grant stays at e.  The same host at an
unrelated site is simply framed.  Then combine the two proved arc
theorems above with the Boolean-to-offset bridge to obtain
the original GrantDrainMarksStrongArcCoverage and
GrantDrainMarksStrongPhysicalClosure for this edge position.

These exact token/mark facts have NOT been proved here.  Therefore
the original two global targets remain unproved and the requested
edge out of g is not claimed in this stop-at-first-gap round.
-/

end L3

/-!
Supplementary incoming-to-p boundary row:
e=g, rightNeighbor e=p.  The old grant is unheld and lies at the
initiator.  An old leader at responder p is ineligible for F1,
and Rx=false excludes F0/F2. Hence FIRE=none.
The token row retains the old initiator grant and does not create
a new initiator request; the proof-only host stays g.

The next missing lemma is the forward conversion of a nearest-
leader cyclic-offset zero arc into the Boolean List.all observer.
The reverse direction was closed earlier.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- No F1 at a final responder leader and no F0/F2 when OLD Rx=0.
This is the exact source selector for e=g into protected p. -/
theorem grantDrainMarksIncomingUnheldHostSelectNone
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e : Fin n)
    (hRequest : s.request e = false)
    (hResponderLeader :
      (nativeE ring s.native e
        (ring.rightNeighbor e)).l = true) :
    grantDrainSelect ring s e = .none := by
  have hEligible :
      grantDrainEligible (nativeE ring s.native e)
        (ring.rightNeighbor e) = false := by
    simp [grantDrainEligible, hResponderLeader]
  simp [grantDrainSelect, hRequest, hEligible]

/-- In the resulting no-FIRE old-token row, X's OLD unheld
grant stays X; its request remains absent.  No OLD responder
request/grant or hostile fresh responder request can change it. -/
theorem grantDrainMarksIncomingUnheldHostToken
    (ry gy fresh : Bool) :
    (grantDrainTokenRow false true ry gy false true fresh .none).1.req =
        false ∧
    (grantDrainTokenRow false true ry gy false true fresh .none).1.grant =
        true := by
  cases ry <;> cases gy <;> cases fresh <;> decide

/-- Physical grant and request and proof-only host all stay at the
OLD initiator g=e on the boundary service e=g -> p, with p an
old shielded zero-signal leader and g an unheld follower grant.
No assumptions are imposed on either site's bullet fields. -/
theorem grantDrainMarksIncomingUnheldHostFrame
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n)
    (hFollower : (s.native e).l = false)
    (hRequest : s.request e = false)
    (hGrant : s.grant e = true)
    (hLeader :
      (s.native (ring.rightNeighbor e)).l = true)
    (hShield :
      (s.native (ring.rightNeighbor e)).sh = true)
    (hSignal :
      (s.native (ring.rightNeighbor e)).sg = false) :
    (grantDrainStep ring freshRequest updateScratch s e).request e = false ∧
    (grantDrainStep ring freshRequest updateScratch s e).grant e = true ∧
    grantDrainLedgerHost ring freshRequest s e (some e) = some e := by
  have hEY :=
    grantDrainMarksIncomingProtectedNativeE
      hn ring s e hLeader hShield hSignal
  have hYLeader :
      (nativeE ring s.native e (ring.rightNeighbor e)).l = true := by
    rw [hEY]
    exact hLeader
  have hFire :=
    grantDrainMarksIncomingUnheldHostSelectNone
      ring s e hRequest hYLeader
  have hNative :
      grantDrainNativeNext ring s e = nativeE ring s.native e := by
    simp [grantDrainNativeNext, hFire]
  have hFinalX :
      (grantDrainNativeNext ring s e e).l = false := by
    rw [hNative]
    rw [grantDrainMarksNativeESource]
    rw [grantDrainMarksOutgoingSourceLeaderNative]
    exact hFollower
  have hFinalY :
      (grantDrainNativeNext ring s e
        (ring.rightNeighbor e)).l = true := by
    rw [hNative]
    exact hYLeader
  have hRow :
      grantDrainLedgerRow ring freshRequest s e =
        grantDrainTokenRow false true
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          false true (freshRequest s e) .none := by
    unfold grantDrainLedgerRow
    rw [hRequest, hGrant, hFinalX, hFinalY, hFire]
  have hRX :
      (grantDrainLedgerRow ring freshRequest s e).1.req = false := by
    rw [hRow]
    exact
      (grantDrainMarksIncomingUnheldHostToken
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e)) (freshRequest s e)).1
  have hGX :
      (grantDrainLedgerRow ring freshRequest s e).1.grant = true := by
    rw [hRow]
    exact
      (grantDrainMarksIncomingUnheldHostToken
        (s.request (ring.rightNeighbor e))
        (s.grant (ring.rightNeighbor e)) (freshRequest s e)).2
  have hPostRequest :
      (grantDrainStep ring freshRequest updateScratch s e).request e =
        false := by
    change (if e = e then
      (grantDrainLedgerRow ring freshRequest s e).1.req
      else if e = ring.rightNeighbor e then
        (grantDrainLedgerRow ring freshRequest s e).2.req
      else s.request e) = false
    simp [hRX]
  have hPostGrant :
      (grantDrainStep ring freshRequest updateScratch s e).grant e =
        true := by
    change (if e = e then
      (grantDrainLedgerRow ring freshRequest s e).1.grant
      else if e = ring.rightNeighbor e then
        (grantDrainLedgerRow ring freshRequest s e).2.grant
      else s.grant e) = true
    simp [hGX]
  have hHost :
      grantDrainLedgerHost ring freshRequest s e (some e) =
        some e := by
    simp [grantDrainLedgerHost, hGrant, hGX]
  exact ⟨hPostRequest, hPostGrant, hHost⟩

/-- The NEXT proof obligation is precisely the converse
geometric observer direction: convert a clockwise nearest
protected source and full offset-zero arc back to the actual
Boolean strong-lock observer (whose List.all is reversed).
It is NOT asserted as a theorem or axiom. -/
def GrantDrainMarksOffsetArcToStrongLock
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) : Prop :=
  GrantDrainMarksNearestArc ring s.native p g →
  GrantDrainMarksZeroOffsetArc ring s.native p g →
  (s.native p).sh = true →
  grantDrainLedgerStrongLock ring s g = true

end L3

/-!
The reverse offset-arc observer and BOTH old-unheld
initiator-host cases. In the
e=g case the token cannot move left; its old request is false,
and its old grant survives the X row irrespective of F1 at Y.
The whole-ring-minus-one-site boundary is included.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Forward direction of the range-all Boolean observer, without
any non-core List.all iff lemma. -/
private theorem grantDrainMarksAllRangeForward (f : Nat → Bool) :
    ∀ length start,
      (∀ k : Nat, start ≤ k → k < start + length →
        f k = true) →
      (List.range' start length).all f = true := by
  intro length
  induction length with
  | zero =>
      intro start h
      simp [List.range']
  | succ length ih =>
      intro start h
      have hHead : f start = true :=
        h start (Nat.le_refl _) (by omega)
      have hTail :
          (List.range' (start + 1) length).all f = true := by
        apply ih (start + 1)
        intro k hk hlt
        exact h k (by omega) (by omega)
      simpa [List.range'_succ, List.all_cons, hHead] using hTail

/-- Clockwise zero arc gives the EXACT reverse-order List.all
tested by grantDrainLedgerCorridor, including source p itself. -/
theorem grantDrainMarksOffsetZeroAll
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (p g : Fin n)
    (hZero : GrantDrainMarksZeroOffsetArc ring N p g) :
    (List.range (PPL.cyclicOffset ring p g)).all
      (fun k => !(N (PPL.shiftLeft ring g (k + 1))).sg) = true := by
  have hRange :
      (List.range' 0 (PPL.cyclicOffset ring p g)).all
        (fun k => !(N (PPL.shiftLeft ring g (k + 1))).sg) =
          true := by
    apply grantDrainMarksAllRangeForward
    intro k hk hlt
    have hBound : k < PPL.cyclicOffset ring p g := by omega
    have hShift :=
      grantDrainMarksArcShiftLeftRight ring p
        (PPL.cyclicOffset ring p g) (k + 1)
        (by omega) (grantDrainMarksArcOffsetLt ring p g)
    rw [grantDrainMarksArcShiftRightOffset ring p g] at hShift
    have hSignal :
        (N (PPL.shiftLeft ring g (k + 1))).sg = false := by
      rw [hShift]
      exact hZero (PPL.cyclicOffset ring p g - (k + 1))
        (by omega)
    simp [hSignal]
  simpa [List.range_eq_range'] using hRange

/-- The missing converse of the strong-lock offset bridge. -/
theorem grantDrainMarksOffsetArcStrongLock
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) :
    GrantDrainMarksOffsetArcToStrongLock ring s p g := by
  intro hNearest hZero hShield
  have hDistance :=
    grantDrainMarksScanOfNearestArc ring s.native p g hNearest
  have hSource :
      PPL.shiftLeft ring g (PPL.cyclicOffset ring p g) = p := by
    have hShift :=
      grantDrainMarksArcShiftLeftRight ring p
        (PPL.cyclicOffset ring p g)
        (PPL.cyclicOffset ring p g)
        (Nat.le_refl _) (grantDrainMarksArcOffsetLt ring p g)
    rw [grantDrainMarksArcShiftRightOffset ring p g] at hShift
    simpa [grantDrainMarksArcShiftRightZero] using hShift
  have hAll :=
    grantDrainMarksOffsetZeroAll ring s.native p g hZero
  simp [grantDrainLedgerStrongLock, grantDrainLedgerCorridor,
    hDistance, hSource, hNearest.2.1, hShield, hAll]

/-- Two nearest-root arcs on the same p..g interval determine
identical leader bits at every position STRICTLY before g. -/
theorem grantDrainMarksLeaderFrameOfNearest
    {n : Nat} (ring : DirectedRing n)
    (N M : Fin n → CertNative) (p g : Fin n)
    (hOld : GrantDrainMarksNearestArc ring N p g)
    (hNew : GrantDrainMarksNearestArc ring M p g)
    (k : Nat) (hk : k < PPL.cyclicOffset ring p g) :
    (M (PPL.shiftRight ring p k)).l =
      (N (PPL.shiftRight ring p k)).l := by
  by_cases hz : k = 0
  · subst k
    rw [grantDrainMarksArcShiftRightZero,
      hNew.2.1, hOld.2.1]
  · rw [hNew.2.2 k (by omega) hk,
      hOld.2.2 k (by omega) hk]

/-- Rx=false excludes F0 and F2, so an old unheld initiator
can select only no FIRE or a responder-local F1. -/
theorem grantDrainMarksUnheldInitiatorSelector
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hRequest : s.request e = false) :
    grantDrainSelect ring s e = .none ∨
      grantDrainSelect ring s e = .rightLocal := by
  unfold grantDrainSelect
  simp [hRequest]
  cases grantDrainEligible (nativeE ring s.native e)
      (ring.rightNeighbor e) <;>
    cases s.request (ring.rightNeighbor e) <;>
    cases s.grant (ring.rightNeighbor e) <;> simp

/-- Native E never changes X's leader bit, and a possible
F1 writes the other endpoint only. -/
theorem grantDrainMarksUnheldInitiatorFollowerNext
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFollower : (s.native e).l = false)
    (hRequest : s.request e = false) :
    (grantDrainNativeNext ring s e e).l = false := by
  have hE : (nativeE ring s.native e e).l = false := by
    rw [grantDrainMarksNativeESource]
    rw [grantDrainMarksOutgoingSourceLeaderNative]
    exact hFollower
  rcases grantDrainMarksUnheldInitiatorSelector
      ring s e hRequest with hNone | hRight
  · simpa [grantDrainNativeNext, hNone] using hE
  · have hNe : e ≠ ring.rightNeighbor e :=
      (grantDrainMarksNeighborDistinct hn ring e).symm
    simpa [grantDrainNativeNext, hRight,
      canonicalBirth, hNe] using hE

/-- Literal final X token row: for all Y tokens, final Y
leader flag and hostile fresh responder requests, X keeps its
unheld grant under either permitted FIRE result. -/
theorem grantDrainMarksUnheldInitiatorToken
    (ry gy ly fresh : Bool) (fire : GrantDrainFire)
    (hFire : fire = .none ∨ fire = .rightLocal) :
    (grantDrainTokenRow false true ry gy false ly fresh fire).1.req =
      false ∧
    (grantDrainTokenRow false true ry gy false ly fresh fire).1.grant =
      true := by
  rcases hFire with hNone | hRight
  · rw [hNone]
    cases ry <;> cases gy <;> cases ly <;>
      cases fresh <;> decide
  · rw [hRight]
    cases ry <;> cases gy <;> cases ly <;>
      cases fresh <;> decide

/-- Native follower, retained physical X grant, absent X
request and proof-only identity host, for every selected edge
whose initiator is the old unheld grant. -/
theorem grantDrainMarksUnheldInitiatorFrame
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hFollower : (s.native e).l = false)
    (hRequest : s.request e = false)
    (hGrant : s.grant e = true) :
    (grantDrainStep ring freshRequest updateScratch s e).request e =
      false ∧
    (grantDrainStep ring freshRequest updateScratch s e).grant e =
      true ∧
    grantDrainLedgerHost ring freshRequest s e (some e) = some e := by
  have hOnly :=
    grantDrainMarksUnheldInitiatorSelector ring s e hRequest
  have hFinalX :=
    grantDrainMarksUnheldInitiatorFollowerNext
      hn ring s e hFollower hRequest
  have hRow :
      grantDrainLedgerRow ring freshRequest s e =
        grantDrainTokenRow false true
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          false
          (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
          (freshRequest s e) (grantDrainSelect ring s e) := by
    unfold grantDrainLedgerRow
    rw [hRequest, hGrant, hFinalX]
  have hX :
      (grantDrainLedgerRow ring freshRequest s e).1.req = false ∧
      (grantDrainLedgerRow ring freshRequest s e).1.grant = true := by
    rw [hRow]
    exact grantDrainMarksUnheldInitiatorToken
      (s.request (ring.rightNeighbor e))
      (s.grant (ring.rightNeighbor e))
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
      (freshRequest s e) (grantDrainSelect ring s e) hOnly
  have hReq :
      (grantDrainStep ring freshRequest updateScratch s e).request e =
        false := by
    change (if e = e then
      (grantDrainLedgerRow ring freshRequest s e).1.req
      else if e = ring.rightNeighbor e then
        (grantDrainLedgerRow ring freshRequest s e).2.req
      else s.request e) = false
    simp [hX.1]
  have hGrantNext :
      (grantDrainStep ring freshRequest updateScratch s e).grant e =
        true := by
    change (if e = e then
      (grantDrainLedgerRow ring freshRequest s e).1.grant
      else if e = ring.rightNeighbor e then
        (grantDrainLedgerRow ring freshRequest s e).2.grant
      else s.grant e) = true
    simp [hX.2]
  have hHost :
      grantDrainLedgerHost ring freshRequest s e (some e) = some e := by
    simp [grantDrainLedgerHost, hGrant, hX.2]
  exact ⟨hReq, hGrantNext, hHost⟩

/-- A site strictly before g cannot be g. Nor can it be g+1,
provided g+1 is not the protected source p (the only wraparound
case). This is cyclic-offset arithmetic, not a linear-order guess. -/
theorem grantDrainMarksOutgoingHostArcAway
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n) (p g : Fin n)
    (hNotRoot : ring.rightNeighbor g ≠ p) :
    ∀ k : Nat, k < PPL.cyclicOffset ring p g →
      PPL.shiftRight ring p k ≠ g ∧
      PPL.shiftRight ring p k ≠ ring.rightNeighbor g := by
  have hFull : PPL.shiftRight ring p n = p := by
    apply Fin.ext
    change (p.val + n) % n = p.val
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
  have hNext :
      ring.rightNeighbor g =
        PPL.shiftRight ring p (PPL.cyclicOffset ring p g + 1) := by
    calc
      ring.rightNeighbor g = PPL.shiftRight ring g 1 := by
        apply Fin.ext
        rfl
      _ = PPL.shiftRight ring
            (PPL.shiftRight ring p (PPL.cyclicOffset ring p g))
            1 := by rw [grantDrainMarksArcShiftRightOffset ring p g]
      _ = PPL.shiftRight ring p
            (PPL.cyclicOffset ring p g + 1) :=
          grantDrainMarksArcShiftRightAdd ring p
            (PPL.cyclicOffset ring p g) 1
  have hBound :
      PPL.cyclicOffset ring p g + 1 < n := by
    by_cases hlt : PPL.cyclicOffset ring p g + 1 < n
    · exact hlt
    · have heq : PPL.cyclicOffset ring p g + 1 = n := by
        have hdlt := grantDrainMarksArcOffsetLt ring p g
        omega
      have hContr : ring.rightNeighbor g = p := by
        rw [hNext, heq]
        exact hFull
      exact False.elim (hNotRoot hContr)
  intro k hk
  have hklt : k < n :=
    Nat.lt_trans hk (grantDrainMarksArcOffsetLt ring p g)
  constructor
  · intro h
    have ho := congrArg (PPL.cyclicOffset ring p) h
    rw [grantDrainMarksArcOffsetShiftRight ring p k hklt] at ho
    omega
  · intro h
    rw [hNext] at h
    have ho := congrArg (PPL.cyclicOffset ring p) h
    rw [grantDrainMarksArcOffsetShiftRight ring p k hklt,
      grantDrainMarksArcOffsetShiftRight ring p
        (PPL.cyclicOffset ring p g + 1) hBound] at ho
    omega

/-- Both outgoing-of-old-host cases: either g+1=p (the maximal
corridor boundary) or g+1 differs from p (pair lies outside
[p,g)). In BOTH cases the old X grant and its strong identity
remain at g and the protected distance is unchanged. -/
theorem grantDrainMarksOutgoingHostStrongGeometry
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hAt : label.host = some e) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
      some e ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
      .strong ∧
    grantDrainLedgerNominatedHit ring s e label.host = false ∧
    grantDrainStrongProtectedDistance ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
    grantDrainStrongProtectedDistance ring s label.host := by
  rcases hPhysical with
    ⟨g, hOldHost, hOldMark, hGrant, hRequest, hFollower, hLock⟩
  have hSame : g = e :=
    Option.some.inj (hOldHost.symm.trans hAt)
  subst g
  rcases grantDrainMarksStrongLockToOffsetArc_proved
      ring s e hP hFollower hLock with
    ⟨p, hNearest, hZero, hShield⟩
  have hSignal : (s.native p).sg = false := by
    have hz := hZero 0 hNearest.1
    simpa [grantDrainMarksArcShiftRightZero] using hz
  have hFrameToken :=
    grantDrainMarksUnheldInitiatorFrame
      hn ring freshRequest updateScratch s e
      hFollower hRequest hGrant
  have hNextFollower :
      ((grantDrainStep ring freshRequest updateScratch s e).native e).l =
        false := by
    change (grantDrainNativeNext ring s e e).l = false
    exact grantDrainMarksUnheldInitiatorFollowerNext
      hn ring s e hFollower hRequest
  have hGeometry :
      GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s e) p e ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) p e ∧
      (grantDrainNativeNext ring s e p).sh = true := by
    by_cases hIncoming : ring.rightNeighbor e = p
    · have hNearNext :=
        grantDrainMarksIncomingSourceNearestArc
          hn ring s p e e hIncoming hNearest hShield hSignal
      have hZeroNext :=
        grantDrainMarksIncomingSourceZeroArc
          hn ring s p e e hIncoming hNearest.2.1
          hShield hSignal hZero
      have hPNext :=
        grantDrainMarksIncomingProtectedNativeNext
          hn ring s e
          (by simpa [hIncoming] using hNearest.2.1)
          (by simpa [hIncoming] using hShield)
          (by simpa [hIncoming] using hSignal)
      have hShieldNext :
          (grantDrainNativeNext ring s e p).sh = true := by
        simpa [hIncoming] using hPNext.2.1
      exact ⟨hNearNext, hZeroNext, hShieldNext⟩
    · have hAway :=
        grantDrainMarksOutgoingHostArcAway hn ring p e hIncoming
      have hFrame :
          ∀ k : Nat, k < PPL.cyclicOffset ring p e →
            grantDrainNativeNext ring s e
                (PPL.shiftRight ring p k) =
              s.native (PPL.shiftRight ring p k) := by
        intro k hk
        have hOutside := hAway k hk
        exact grantDrainMarksNativeOutsidePairFrame
          ring s e (PPL.shiftRight ring p k)
          hOutside.1 hOutside.2
      have hPFrame :
          grantDrainNativeNext ring s e p = s.native p := by
        simpa [grantDrainMarksArcShiftRightZero] using
          hFrame 0 hNearest.1
      have hNearNext :
          GrantDrainMarksNearestArc ring
            (grantDrainNativeNext ring s e) p e := by
        refine ⟨hNearest.1, ?_, ?_⟩
        · rw [hPFrame]
          exact hNearest.2.1
        · intro k hk hklt
          rw [hFrame k hklt]
          exact hNearest.2.2 k hk hklt
      have hZeroNext :
          GrantDrainMarksZeroOffsetArc ring
            (grantDrainNativeNext ring s e) p e := by
        intro k hk
        rw [hFrame k hk]
        exact hZero k hk
      have hShieldNext :
          (grantDrainNativeNext ring s e p).sh = true := by
        rw [hPFrame]
        exact hShield
      exact ⟨hNearNext, hZeroNext, hShieldNext⟩
  have hPostLock :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring freshRequest updateScratch s e) e =
          true := by
    exact grantDrainMarksOffsetArcStrongLock
      ring (grantDrainStep ring freshRequest updateScratch s e)
      p e hGeometry.1 hGeometry.2.1 hGeometry.2.2
  have hHostRaw :
      grantDrainLedgerHost ring freshRequest s e label.host =
        some e := by
    rw [hAt]
    exact hFrameToken.2.2
  have hNextHost :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
        some e := by
    change grantDrainLedgerHost ring freshRequest s e label.host = some e
    exact hHostRaw
  have hOldObserved :
      grantDrainLedgerObservedMark ring s (some e) = .strong := by
    simp [grantDrainLedgerObservedMark, hRequest, hFollower, hLock]
  have hNextObserved :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (some e) = .strong := by
    simp [grantDrainLedgerObservedMark,
      hFrameToken.1, hNextFollower, hPostLock]
  have hNoCoalesce :
      grantDrainLedgerCoalesceMark ring s e (some e) (some e) =
        .unmarked := by
    have hNe : e ≠ ring.rightNeighbor e :=
      (grantDrainMarksNeighborDistinct hn ring e).symm
    simp [grantDrainLedgerCoalesceMark, hNe]
  have hNextMark :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
        .strong := by
    change grantDrainLedgerMarkNext ring freshRequest
      updateScratch s e label = .strong
    unfold grantDrainLedgerMarkNext
    rw [hOldMark, hHostRaw, hAt, hOldObserved,
      hNoCoalesce, hNextObserved]
    rfl
  have hLeaderFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p e →
        ((grantDrainStep ring freshRequest updateScratch s e).native
          (PPL.shiftRight ring p k)).l =
        (s.native (PPL.shiftRight ring p k)).l := by
    intro k hk
    exact grantDrainMarksLeaderFrameOfNearest
      ring s.native (grantDrainNativeNext ring s e)
      p e hNearest hGeometry.1 k hk
  have hDistance :=
    grantDrainMarksArcStableProtectedDistance ring s
      (grantDrainStep ring freshRequest updateScratch s e)
      p e hNearest hLeaderFrame
  have hNoHit :
      grantDrainLedgerNominatedHit ring s e label.host = false := by
    rw [hAt]
    simp [grantDrainLedgerNominatedHit, hRequest,
      grantDrainMarksNeighborDistinct hn ring e]
  refine ⟨⟨e, hNextHost, hNextMark, hFrameToken.2.1,
      hFrameToken.1, hNextFollower, hPostLock⟩,
    hNextHost, hNextMark, hNoHit, ?_⟩
  rw [hNextHost, hAt]
  exact hDistance

/-- Explicit maximal-corridor boundary e=g, rightNeighbor g=p.
The selector is no FIRE (protected responder is an old leader),
and the stronger outgoing-host theorem gives post strong physical
closure, unchanged distance and unchanged identity host. -/
theorem grantDrainMarksWholeRingBoundaryStrong
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hAt : label.host = some g)
    (hIncoming : ring.rightNeighbor g = p)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true) :
    grantDrainSelect ring s g = .none ∧
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s g)
      (grantDrainLedgerStep ring freshRequest updateScratch s g label) ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s g label).host =
      some g ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s g label).mark =
      .strong ∧
    grantDrainLedgerNominatedHit ring s g label.host = false ∧
    grantDrainStrongProtectedDistance ring
      (grantDrainStep ring freshRequest updateScratch s g)
      (grantDrainLedgerStep ring freshRequest updateScratch s g label).host =
    grantDrainStrongProtectedDistance ring s label.host := by
  rcases hPhysical with
    ⟨q, hOldHost, hMark, hGrant, hReq, hFollower, hLock⟩
  have hSame : q = g :=
    Option.some.inj (hOldHost.symm.trans hAt)
  subst q
  have hSignal : (s.native p).sg = false := by
    have hz := hZero 0 hNearest.1
    simpa [grantDrainMarksArcShiftRightZero] using hz
  have hE :=
    grantDrainMarksIncomingProtectedNativeE
      hn ring s g
      (by simpa [hIncoming] using hNearest.2.1)
      (by simpa [hIncoming] using hShield)
      (by simpa [hIncoming] using hSignal)
  have hYLeader :
      (nativeE ring s.native g (ring.rightNeighbor g)).l =
        true := by
    rw [hE]
    simpa [hIncoming] using hNearest.2.1
  have hSelect :=
    grantDrainMarksIncomingUnheldHostSelectNone
      ring s g hReq hYLeader
  have hResult :=
    grantDrainMarksOutgoingHostStrongGeometry
      hn ring freshRequest updateScratch s g label
      hP ⟨g, hOldHost, hMark, hGrant, hReq, hFollower, hLock⟩ hAt
  exact ⟨hSelect, hResult⟩

/-!
STOP: the e=g branch is now proved; it covers both y=p and y≠p.
The next unhandled edge class is e=p and y=p+1 strictly inside
the old corridor. The two native agents to distinguish are
  X=p: L=true, H=true, S=false (protected source);
  Y=p+1: L=false, S=false (interior follower).
Under a possible responder F1, Y becomes a closer leader and the
strong lock must be rebuilt relative to Y, not p. Existing source
lemmas give the leader-distance decrease but do not finish the
post-step label/zero-word/mark classification on that edge.
No proof of the global StrongArcCoverage, StrongPhysicalClosure,
or StrongCorridorGeometry Props is asserted here; also these global
definitions lack the explicit n>=3 hypothesis used by these
nondegenerate native-edge lemmas.
-/

end L3



/-!
Protected-source outgoing edge, y=p+1 strictly before g.

The new proofs treat
only the two native endpoints of the edge p -> y:
  X=p: leader=true, shield=true, signal=false
  Y=y: follower=false-leader, signal=false
and never replace the source step by headlinePhysicalNext.

With no FIRE, E preserves the leader flags and zero corridor [p,g).
With F1 at Y, Y becomes the nearest shielded source and [Y,g) is
the old zero corridor with its first site removed. The live grant at
g is outside both endpoints, so it stays unheld, physically present,
and hosted at g; its strong mark stays strong. Its remaining quota
cannot increase. A separate named next edge class is recorded below.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Literal protected-source E pair. Both endpoint bullet values
and the follower's shield are unrestricted. No full configuration
case split is performed. -/
private theorem grantDrainMarksProtectedSourcePair
    (a b : CertNative)
    (hal : a.l = true) (hah : a.sh = true)
    (has : a.sg = false)
    (hbl : b.l = false) (hbs : b.sg = false) :
    (certLiteralEPair a b).1.l = true ∧
    (certLiteralEPair a b).1.sh = true ∧
    (certLiteralEPair a b).1.sg = false ∧
    (certLiteralEPair a b).2.l = false ∧
    (certLiteralEPair a b).2.sg = false := by
  rcases a with ⟨al, ab, ah, asg⟩
  rcases b with ⟨bl, bb, bh, bsg⟩
  cases al <;> cases ah <;> cases asg <;>
    cases bl <;> cases bsg <;>
    simp [certLiteralEPair] at hal hah has hbl hbs ⊢

/-- In an outgoing protected E edge, the OLD leader bits
are equal at EVERY site. An OLD zero signal remains zero.
At X use grantDrainMarksNativeESource, not a change of
nativeE into an unproved pair projection. -/
theorem grantDrainMarksProtectedSourceEFrame
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p i : Fin n)
    (hPL : (s.native p).l = true)
    (hPH : (s.native p).sh = true)
    (hPS : (s.native p).sg = false)
    (hYL : (s.native (ring.rightNeighbor p)).l = false)
    (hYS : (s.native (ring.rightNeighbor p)).sg = false) :
    (nativeE ring s.native p i).l = (s.native i).l ∧
      ((s.native i).sg = false →
        (nativeE ring s.native p i).sg = false) := by
  have hPair := grantDrainMarksProtectedSourcePair
    (s.native p) (s.native (ring.rightNeighbor p))
    hPL hPH hPS hYL hYS
  have hYNeP := grantDrainMarksNeighborDistinct hn ring p
  have hResponder :
      nativeE ring s.native p (ring.rightNeighbor p) =
        (certLiteralEPair
          (s.native p) (s.native (ring.rightNeighbor p))).2 := by
    unfold nativeE
    simp only [if_neg hYNeP, if_pos rfl, ↓reduceIte]
  by_cases hi : i = p
  · subst i
    rw [grantDrainMarksNativeESource]
    refine ⟨?_, ?_⟩
    · rw [hPair.1, hPL]
    · intro _
      exact hPair.2.2.1
  · by_cases hy : i = ring.rightNeighbor p
    · subst i
      rw [hResponder]
      refine ⟨?_, ?_⟩
      · rw [hPair.2.2.2.1, hYL]
      · intro _
        exact hPair.2.2.2.2
    · have hFrame :
          nativeE ring s.native p i = s.native i := by
        simp [nativeE, hi, hy]
      rw [hFrame]
      exact ⟨rfl, fun h => h⟩

/-- The actual source X remains a shielded zero-signal leader
after either possible FIRE result (none or F1 at Y). -/
theorem grantDrainMarksProtectedSourceNextRoot
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p : Fin n)
    (hPL : (s.native p).l = true)
    (hPH : (s.native p).sh = true)
    (hPS : (s.native p).sg = false)
    (hYL : (s.native (ring.rightNeighbor p)).l = false)
    (hYS : (s.native (ring.rightNeighbor p)).sg = false) :
    (grantDrainNativeNext ring s p p).l = true ∧
    (grantDrainNativeNext ring s p p).sh = true ∧
    (grantDrainNativeNext ring s p p).sg = false := by
  have hPair := grantDrainMarksProtectedSourcePair
    (s.native p) (s.native (ring.rightNeighbor p))
    hPL hPH hPS hYL hYS
  have hE :
      (nativeE ring s.native p p).l = true ∧
      (nativeE ring s.native p p).sh = true ∧
      (nativeE ring s.native p p).sg = false := by
    rw [grantDrainMarksNativeESource]
    exact ⟨hPair.1, hPair.2.1, hPair.2.2.1⟩
  have hNe : p ≠ ring.rightNeighbor p :=
    (grantDrainMarksNeighborDistinct hn ring p).symm
  rcases grantDrainMarksOutgoingLeaderSelector
      ring s p hPL with hf | hf
  · simpa [grantDrainNativeNext, hf] using hE
  · simpa [grantDrainNativeNext, hf, canonicalBirth, hNe]
      using hE

/-- Independently of the actual selection (none or F1),
the entire OLD zero-signal word [p,g) stays zero. -/
theorem grantDrainMarksProtectedSourceZeroArcStep
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hPL : (s.native p).l = true)
    (hPH : (s.native p).sh = true)
    (hPS : (s.native p).sg = false)
    (hYL : (s.native (ring.rightNeighbor p)).l = false)
    (hYS : (s.native (ring.rightNeighbor p)).sg = false)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g) :
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s p) p g := by
  intro k hk
  have hOld := hZero k hk
  have hE :=
    (grantDrainMarksProtectedSourceEFrame
      hn ring s p (PPL.shiftRight ring p k)
      hPL hPH hPS hYL hYS).2 hOld
  rcases grantDrainMarksOutgoingLeaderSelector
      ring s p hPL with hf | hf
  · simpa [grantDrainNativeNext, hf] using hE
  · have hBirth :=
      grantDrainMarksInteriorBirthPreservesZero
        (nativeE ring s.native p) (ring.rightNeighbor p)
        (PPL.shiftRight ring p k) hE
    simpa [grantDrainNativeNext, hf] using hBirth

/-- When the protected source's selected FIRE is none, the
nearest leader p, every old leader bit, the zero word, and
the shield of p are physically preserved. -/
theorem grantDrainMarksProtectedSourceNoFireArc
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hYL : (s.native (ring.rightNeighbor p)).l = false)
    (hYS : (s.native (ring.rightNeighbor p)).sg = false)
    (hFire : grantDrainSelect ring s p = .none) :
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s p) p g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s p) p g ∧
    (grantDrainNativeNext ring s p p).sh = true := by
  have hPS : (s.native p).sg = false := by
    have hz := hZero 0 hNearest.1
    simpa [grantDrainMarksArcShiftRightZero] using hz
  have hRoot := grantDrainMarksProtectedSourceNextRoot
    hn ring s p hNearest.2.1 hShield hPS hYL hYS
  have hZeroNew := grantDrainMarksProtectedSourceZeroArcStep
    hn ring s p g hNearest.2.1 hShield hPS hYL hYS hZero
  refine ⟨?_, hZeroNew, hRoot.2.1⟩
  refine ⟨hNearest.1, hRoot.1, ?_⟩
  intro k hk hklt
  have hBit :=
    (grantDrainMarksProtectedSourceEFrame
      hn ring s p (PPL.shiftRight ring p k)
      hNearest.2.1 hShield hPS hYL hYS).1
  have hNextBit :
      (grantDrainNativeNext ring s p
        (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l := by
    simpa [grantDrainNativeNext, hFire] using hBit
  rw [hNextBit]
  exact hNearest.2.2 k hk hklt

/-- The immediate right neighbor is precisely offset one from p
on every ring with at least three agents. -/
private theorem grantDrainMarksProtectedRightOffset
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n) (p : Fin n) :
    PPL.cyclicOffset ring p (ring.rightNeighbor p) = 1 := by
  have hY :
      ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
    apply Fin.ext
    rfl
  rw [hY]
  exact grantDrainMarksArcOffsetShiftRight ring p 1 (by omega)

/-- Under F1, y is a NEW leader. Its entire [y,g) arc is
the suffix of [p,g) starting at old offset one. The new
distance is exactly old distance minus one, all its
strictly positive offsets are still followers, all its
signals are zero, and the newborn is shielded. -/
theorem grantDrainMarksProtectedSourceFiresSuffix
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (p g : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hLong : 1 < PPL.cyclicOffset ring p g)
    (hFire : grantDrainSelect ring s p = .rightLocal) :
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s p) (ring.rightNeighbor p) g ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s p) (ring.rightNeighbor p) g ∧
    (grantDrainNativeNext ring s p (ring.rightNeighbor p)).sh = true ∧
    PPL.cyclicOffset ring (ring.rightNeighbor p) g =
      PPL.cyclicOffset ring p g - 1 := by
  have hY :
      ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
    apply Fin.ext
    rfl
  have hYOffset :=
    grantDrainMarksProtectedRightOffset hn ring p
  have hYSite : (s.native (ring.rightNeighbor p)).l = false := by
    have h := hNearest.2.2 1 (by omega) hLong
    rw [hY] 
    exact h
  have hYZero : (s.native (ring.rightNeighbor p)).sg = false := by
    have h := hZero 1 hLong
    rw [hY]
    exact h
  have hPS : (s.native p).sg = false := by
    have h := hZero 0 hNearest.1
    simpa [grantDrainMarksArcShiftRightZero] using h
  have hOff :
      PPL.cyclicOffset ring (ring.rightNeighbor p) g =
        PPL.cyclicOffset ring p g - 1 := by
    rw [hY]
    exact grantDrainMarksArcOffsetSubtract
      ring p g 1 (by omega)
  have hZeroWhole := grantDrainMarksProtectedSourceZeroArcStep
    hn ring s p g hNearest.2.1 hShield hPS hYSite hYZero hZero
  have hZeroSuffix :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s p) (ring.rightNeighbor p) g := by
    intro k hk
    have hkWhole : 1 + k < PPL.cyclicOffset ring p g := by
      rw [hOff] at hk
      omega
    have hSite :
        PPL.shiftRight ring (ring.rightNeighbor p) k =
          PPL.shiftRight ring p (1 + k) := by
      rw [hY]
      exact grantDrainMarksArcShiftRightAdd ring p 1 k
    rw [hSite]
    exact hZeroWhole (1 + k) hkWhole
  have hNewRoot :
      (grantDrainNativeNext ring s p (ring.rightNeighbor p)).l =
        true ∧
      (grantDrainNativeNext ring s p (ring.rightNeighbor p)).sh =
        true := by
    simp [grantDrainNativeNext, hFire, canonicalBirth, firedNative]
  have hNewNearest :
      GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s p) (ring.rightNeighbor p) g := by
    refine ⟨?_, hNewRoot.1, ?_⟩
    · rw [hOff]
      omega
    · intro k hk hklt
      have hWithin : 1 + k < PPL.cyclicOffset ring p g := by
        rw [hOff] at hklt
        omega
      have hBound : 1 + k < n :=
        Nat.lt_trans hWithin (grantDrainMarksArcOffsetLt ring p g)
      have hSite :
          PPL.shiftRight ring (ring.rightNeighbor p) k =
            PPL.shiftRight ring p (1 + k) := by
        rw [hY]
        exact grantDrainMarksArcShiftRightAdd ring p 1 k
      have hNotSource :
          PPL.shiftRight ring p (1 + k) ≠ p := by
        intro heq
        have ho := congrArg (PPL.cyclicOffset ring p) heq
        rw [grantDrainMarksArcOffsetShiftRight ring p
          (1 + k) hBound,
          grantDrainMarksArcOffsetZero ring p] at ho
        omega
      have hNotResponder :
          PPL.shiftRight ring p (1 + k) ≠
            ring.rightNeighbor p := by
        intro heq
        have ho := congrArg (PPL.cyclicOffset ring p) heq
        rw [grantDrainMarksArcOffsetShiftRight ring p
          (1 + k) hBound, hYOffset] at ho
        omega
      have hFrame := grantDrainMarksNativeOutsidePairFrame
        ring s p (PPL.shiftRight ring p (1 + k))
        hNotSource hNotResponder
      rw [hSite, hFrame]
      exact hNearest.2.2 (1 + k) (by omega) hWithin
  exact ⟨hNewNearest, hZeroSuffix, hNewRoot.2, hOff⟩

/-- Complete physical and accounting result for protected outgoing
p -> y strictly inside the old corridor. Both FIRE choices are
resolved, the label stays at g, and the ghost quota never rises.
The last disjunction exports the exact ArcCoverage alternatives. -/
theorem grantDrainMarksProtectedSourceLongStrong
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hLong : 1 < PPL.cyclicOffset ring p g)
    (hHost : label.host = some g)
    (hMark : label.mark = .strong)
    (hGrant : s.grant g = true)
    (hRequest : s.request g = false)
    (hFollower : (s.native g).l = false) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s p)
      (grantDrainLedgerStep ring freshRequest updateScratch s p label) ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s p label).host =
      some g ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s p label).mark =
      .strong ∧
    grantDrainLedgerNominatedHit ring s p label.host = false ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s p label).remaining ≤
      label.remaining ∧
    ((grantDrainSelect ring s p = .none ∧
       ∀ k : Nat, k < PPL.cyclicOffset ring p g →
         ((grantDrainStep ring freshRequest updateScratch s p).native
           (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l) ∨
      (grantDrainSelect ring s p = .rightLocal ∧
       GrantDrainMarksNearestArc ring
         (grantDrainStep ring freshRequest updateScratch s p).native
         (ring.rightNeighbor p) g)) := by
  have hYOffset := grantDrainMarksProtectedRightOffset hn ring p
  have hYL : (s.native (ring.rightNeighbor p)).l = false := by
    have h := hNearest.2.2 1 (by omega) hLong
    have hY : ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
      apply Fin.ext
      rfl
    rw [hY]
    exact h
  have hYS : (s.native (ring.rightNeighbor p)).sg = false := by
    have h := hZero 1 hLong
    have hY : ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
      apply Fin.ext
      rfl
    rw [hY]
    exact h
  have hPS : (s.native p).sg = false := by
    have h := hZero 0 hNearest.1
    simpa [grantDrainMarksArcShiftRightZero] using h
  have hNeP : g ≠ p := by
    intro heq
    rw [heq, grantDrainMarksArcOffsetZero ring p] at hLong
    omega
  have hNeY : g ≠ ring.rightNeighbor p := by
    intro heq
    rw [← heq] at hYOffset
    omega
  have hNativeG : grantDrainNativeNext ring s p g = s.native g :=
    grantDrainMarksNativeOutsidePairFrame ring s p g hNeP hNeY
  have hTokenG := grantDrainMarksInteriorTokenFrame
    ring freshRequest updateScratch s p g hNeP hNeY
  have hReqPost :
      (grantDrainStep ring freshRequest updateScratch s p).request g =
        false := hTokenG.1.trans hRequest
  have hGrantPost :
      (grantDrainStep ring freshRequest updateScratch s p).grant g =
        true := hTokenG.2.trans hGrant
  have hFollowerPost :
      ((grantDrainStep ring freshRequest updateScratch s p).native g).l =
        false := by
    change (grantDrainNativeNext ring s p g).l = false
    rw [hNativeG]
    exact hFollower
  have hHostRaw := grantDrainMarksInteriorHostFrame
    ring freshRequest s p g label hHost hNeP hNeY
  have hHostSome :
      grantDrainLedgerHost ring freshRequest s p (some g) =
        some g := by
    simpa only [hHost] using hHostRaw
  have hHostPost :
      (grantDrainLedgerStep ring freshRequest updateScratch s p label).host =
        some g := by
    change grantDrainLedgerHost ring freshRequest s p label.host = some g
    exact hHostRaw
  have hZeroPost := grantDrainMarksProtectedSourceZeroArcStep
    hn ring s p g hNearest.2.1 hShield hPS hYL hYS hZero
  have hSelect := grantDrainMarksOutgoingLeaderSelector
    ring s p hNearest.2.1
  have hLockPost :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring freshRequest updateScratch s p) g = true := by
    rcases hSelect with hNone | hRight
    · have hArc := grantDrainMarksProtectedSourceNoFireArc
        hn ring s p g hNearest hZero hShield hYL hYS hNone
      exact grantDrainMarksOffsetArcStrongLock
        ring (grantDrainStep ring freshRequest updateScratch s p)
        p g hArc.1 hArc.2.1 hArc.2.2
    · have hArc := grantDrainMarksProtectedSourceFiresSuffix
        hn ring s p g hNearest hZero hShield hLong hRight
      exact grantDrainMarksOffsetArcStrongLock
        ring (grantDrainStep ring freshRequest updateScratch s p)
        (ring.rightNeighbor p) g hArc.1 hArc.2.1 hArc.2.2.1
  have hOldLock :
      grantDrainLedgerStrongLock ring s g = true :=
    grantDrainMarksOffsetArcStrongLock ring s p g hNearest hZero hShield
  have hObservedOld :
      grantDrainLedgerObservedMark ring s (some g) = .strong := by
    simp [grantDrainLedgerObservedMark, hRequest, hGrant, hFollower,
      hOldLock]
  have hObservedPost :
      grantDrainLedgerObservedMark ring
        (grantDrainStep ring freshRequest updateScratch s p)
        (some g) = .strong := by
    simp [grantDrainLedgerObservedMark, hReqPost, hGrantPost,
      hFollowerPost, hLockPost]
  have hCoalesce :
      grantDrainLedgerCoalesceMark ring s p (some g) (some g) =
        .unmarked := by
    simp [grantDrainLedgerCoalesceMark, hNeY]
  have hMarkPost :
      (grantDrainLedgerStep ring freshRequest updateScratch s p label).mark =
        .strong := by
    change grantDrainLedgerMarkNext
      ring freshRequest updateScratch s p label = .strong
    unfold grantDrainLedgerMarkNext
    rw [hMark, hHost, hHostSome, hObservedOld,
      hCoalesce, hObservedPost]
    rfl
  have hNoHit :
      grantDrainLedgerNominatedHit ring s p label.host = false := by
    rw [hHost]
    have hYNeG : ring.rightNeighbor p ≠ g := Ne.symm hNeY
    simp [grantDrainLedgerNominatedHit, hRequest, hYNeG]
  have hQuota :
      (grantDrainLedgerStep ring freshRequest updateScratch s p label).remaining ≤
        label.remaining :=
    grantDrainLedgerStep_remaining_nonincrease
      ring freshRequest updateScratch s p label (by simp [hMark])
  have hPhysicalPost :
      GrantDrainStrongPhysical ring
        (grantDrainStep ring freshRequest updateScratch s p)
        (grantDrainLedgerStep ring freshRequest updateScratch s p label) :=
    ⟨g, hHostPost, hMarkPost, hGrantPost, hReqPost,
      hFollowerPost, hLockPost⟩
  refine ⟨hPhysicalPost, hHostPost, hMarkPost, hNoHit, hQuota, ?_⟩
  rcases hSelect with hNone | hRight
  · refine Or.inl ⟨hNone, ?_⟩
    intro k hk
    have hBit :=
      (grantDrainMarksProtectedSourceEFrame
        hn ring s p (PPL.shiftRight ring p k)
        hNearest.2.1 hShield hPS hYL hYS).1
    change (grantDrainNativeNext ring s p
      (PPL.shiftRight ring p k)).l = _
    simpa [grantDrainNativeNext, hNone] using hBit
  · have hArc := grantDrainMarksProtectedSourceFiresSuffix
      hn ring s p g hNearest hZero hShield hLong hRight
    exact Or.inr ⟨hRight, hArc.1⟩

/-- The outgoing protected-source long-arc case supplies precisely
the stable-host or closer-birth disjunction required by
GrantDrainMarksStrongArcCoverage, plus the physical closure. -/
theorem grantDrainMarksProtectedSourceLongCoverage
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hLong : 1 < PPL.cyclicOffset ring p g)
    (hHost : label.host = some g)
    (hMark : label.mark = .strong)
    (hGrant : s.grant g = true)
    (hRequest : s.request g = false)
    (hFollower : (s.native g).l = false) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s p)
      (grantDrainLedgerStep ring freshRequest updateScratch s p label) ∧
    ∃ (q h : Fin n),
      label.host = some h ∧
      GrantDrainMarksNearestArc ring s.native q h ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s p label).host =
            some h ∧
          grantDrainLedgerNominatedHit ring s p label.host = false ∧
          (∀ k : Nat, k < PPL.cyclicOffset ring q h →
            ((grantDrainStep ring freshRequest updateScratch s p).native
              (PPL.shiftRight ring q k)).l =
            (s.native (PPL.shiftRight ring q k)).l)) ∨
        (∃ d : Nat,
          PPL.cyclicOffset ring q h = d ∧ 2 ≤ d ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s p label).host =
            some (PPL.shiftLeft ring h 1) ∧
          (∀ k : Nat, k < d - 1 →
            ((grantDrainStep ring freshRequest updateScratch s p).native
              (PPL.shiftRight ring q k)).l =
            (s.native (PPL.shiftRight ring q k)).l)) ∨
        (∃ j : Nat, 0 < j ∧
          j < PPL.cyclicOffset ring q h ∧
          grantDrainLedgerNominatedHit ring s p label.host = false ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s p label).host =
            some h ∧
          GrantDrainMarksNearestArc ring
            (grantDrainStep ring freshRequest updateScratch s p).native
            (PPL.shiftRight ring q j) h)) := by
  obtain ⟨hPhysicalPost, hHostPost, hMarkPost, hNoHit,
      hQuota, hCases⟩ :=
    grantDrainMarksProtectedSourceLongStrong hn ring
      freshRequest updateScratch s p g label hNearest hZero
      hShield hLong hHost hMark hGrant hRequest hFollower
  refine ⟨hPhysicalPost, p, g, hHost, hNearest, ?_⟩
  rcases hCases with ⟨hNone, hFrame⟩ | ⟨hRight, hArc⟩
  · exact Or.inl ⟨hHostPost, hNoHit, hFrame⟩
  · have hY : ring.rightNeighbor p = PPL.shiftRight ring p 1 := by
      apply Fin.ext
      rfl
    have hArcOne :
        GrantDrainMarksNearestArc ring
          (grantDrainStep ring freshRequest updateScratch s p).native
          (PPL.shiftRight ring p 1) g := by
      rw [← hY]
      exact hArc
    exact Or.inr (Or.inr
      ⟨1, by omega, hLong, hNoHit, hHostPost, hArcOne⟩)

/-- Next *unproved* edge class. At the selected edge x -> y=g,
both OLD endpoints are followers, X lies immediately before the
strong unheld grant host, and Y owns the tracked old grant.
The label can move Y->X, coalesce with X, or retire according
to the exact token row. Its moving strong corridor must be
rebuilt at X when the label remains strong. This is a Prop,
NOT a theorem, axiom, or implicit prerequisite of the case
already proved above. -/
def GrantDrainMarksIncomingFollowerHostLeaf
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    Prop :=
  ∀ (s : GrantDrainState n Scratch) (x : Fin n)
    (label : GrantDrainLedgerLabel n),
    PPlus ring s.native →
    (s.native x).l = false →
    (s.native (ring.rightNeighbor x)).l = false →
    label.host = some (ring.rightNeighbor x) →
    GrantDrainStrongPhysical ring s label →
    (grantDrainLedgerStep ring freshRequest updateScratch s x label).host ≠ none →
    (grantDrainLedgerStep ring freshRequest updateScratch s x label).mark =
      .strong →
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s x)
      (grantDrainLedgerStep ring freshRequest updateScratch s x label)

/-!
Scope audit:

Proved:
* grantDrainMarksProtectedSourceEFrame: E leader/zero frame at
  protected p and its follower y, globally including untouched sites;
* grantDrainMarksProtectedSourceNoFireArc: no-FIRE whole lock;
* grantDrainMarksProtectedSourceFiresSuffix: F1 y..g suffix,
  protected newborn leader, exact distance d-1, restricted zero word;
* grantDrainMarksProtectedSourceLongStrong: physical strong mark,
  unchanged proof-only host, no nominated hit, remaining quota
  nonincrease, and FIRE disjunction;
* grantDrainMarksProtectedSourceLongCoverage: both required local
  outputs of global StrongArcCoverage and StrongPhysicalClosure.

NOT PROVED HERE: universal GrantDrainMarksStrongArcCoverage or
GrantDrainMarksStrongPhysicalClosure. WholeRingBoundaryStrong
covers the e=g -> p seam; strict-interior zero-arc preservation
and incoming-to-p native geometry exist, but the other edge
locations still require their token/label/mark assembly, in
particular GrantDrainMarksIncomingFollowerHostLeaf (x -> g).
The two global Props are therefore not asserted under a
misleading 3<=n hypothesis.
-/

end L3



/-!
Incoming edge x -> y=g for an OLD unheld strong grant.

The OLD responder grant has request=false, grant=true. Its token
cannot stutter at Y. If its identity survives, YSource is some false
and the proof-only host is X. This forces no FIRE and both final
endpoint leader bits false. A pre-existing X grant may coalesce; it
does not make a second identity, and a post-step HOLD is excluded by
the hypothesis that the persistent mark remains .strong.

The new protected corridor is [p,x), a STRICT PREFIX of the OLD
[p,g), because x is the immediate predecessor of g. The signal
at g is NOT required to be zero and is NEVER inserted into the
new corridor. The selected edge changes only x and g; every
old prefix site through x's predecessor is framed. Existing
offset-arc-to-strong-lock and quota monotonicity then finish
the native, label, and numerical requirements.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- On a ring of at least three sites, going one step right
and then one step left returns to the same site. -/
private theorem grantDrainMarksIncomingLeftRight
    {n : Nat} (hn : 3 ≤ n)
    (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftLeft ring (ring.rightNeighbor x) 1 = x := by
  have hr : ring.rightNeighbor x = PPL.shiftRight ring x 1 := by
    apply Fin.ext
    rfl
  rw [hr]
  have hInverse :=
    grantDrainMarksArcShiftLeftRight ring x 1 1
      (by omega) (by omega)
  simpa only [Nat.sub_self, grantDrainMarksArcShiftRightZero]
    using hInverse

/-- A surviving OLD unheld responder label can only MOVE to X.
The row cannot leave an OLD unheld Y identity at Y. Apart from
the no-FIRE, two-final-followers case it is retired. This proof
only splits the FIRE selector and the two final native leader
bits, not all token-state Booleans. -/
private theorem grantDrainMarksIncomingYSurvivorRow
    (rx gx lx ly fresh : Bool) (fire : GrantDrainFire)
    (hLive :
      grantDrainLedgerYSource false true lx ly fire
        (grantDrainTokenRow rx gx false true lx ly fresh fire) ≠
          none) :
    fire = .none ∧ lx = false ∧ ly = false ∧
    grantDrainLedgerYSource false true lx ly fire
      (grantDrainTokenRow rx gx false true lx ly fresh fire) =
        some false := by
  have hNoY :=
    grantDrainMarksUnheldResponderNoStutter
      rx gx lx ly fresh fire
  cases fire with
  | none =>
      cases lx with
      | true =>
          simp [grantDrainLedgerYSource, hNoY] at hLive
      | false =>
          cases ly with
          | true =>
              simp [grantDrainLedgerYSource, hNoY] at hLive
          | false =>
              exact ⟨rfl, rfl, rfl,
                grantDrainMarksUnheldResponderLabelMoves
                  rx gx fresh⟩
  | leftLocal =>
      simp [grantDrainLedgerYSource, hNoY] at hLive
      exact absurd hLive.1 (by decide)
  | rightLocal =>
      simp [grantDrainLedgerYSource, hNoY] at hLive
      exact absurd hLive.1 (by decide)
  | cross =>
      simp [grantDrainLedgerYSource, hNoY] at hLive
      exact absurd hLive.1 (by decide)

/-- Source-level OLD unheld Y survivor: only no FIRE,
Y-to-X transport, and physical X grant. The proof does not
assume X's OLD request/grant or Y's OLD signal/bullet. A
coalescence with an OLD X grant is permitted. -/
theorem grantDrainMarksIncomingFollowerSurvivorMoves
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (x : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hOldHost : label.host = some (ring.rightNeighbor x))
    (hOldRequest : s.request (ring.rightNeighbor x) = false)
    (hOldGrant : s.grant (ring.rightNeighbor x) = true)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s x label).host ≠
        none) :
    grantDrainSelect ring s x = .none ∧
    (grantDrainNativeNext ring s x x).l = false ∧
    (grantDrainNativeNext ring s x (ring.rightNeighbor x)).l =
      false ∧
    (grantDrainLedgerStep ring freshRequest updateScratch s x label).host =
      some x ∧
    (grantDrainStep ring freshRequest updateScratch s x).grant x =
      true := by
  have hNe : ring.rightNeighbor x ≠ x :=
    grantDrainMarksNeighborDistinct hn ring x
  have hHostEq :
      grantDrainLedgerHost ring freshRequest s x label.host =
        (match grantDrainLedgerYSource
          (s.request (ring.rightNeighbor x))
          (s.grant (ring.rightNeighbor x))
          (grantDrainNativeNext ring s x x).l
          (grantDrainNativeNext ring s x (ring.rightNeighbor x)).l
          (grantDrainSelect ring s x)
          (grantDrainLedgerRow ring freshRequest s x) with
        | some true => some (ring.rightNeighbor x)
        | some false => some x
        | none => none) := by
    rw [hOldHost]
    simp only [grantDrainLedgerHost, if_neg hNe, if_pos rfl,
      ↓reduceIte]
  have hRowEq :
      grantDrainLedgerRow ring freshRequest s x =
        grantDrainTokenRow
          (s.request x) (s.grant x) false true
          (grantDrainNativeNext ring s x x).l
          (grantDrainNativeNext ring s x (ring.rightNeighbor x)).l
          (freshRequest s x) (grantDrainSelect ring s x) := by
    unfold grantDrainLedgerRow
    rw [hOldRequest, hOldGrant]
  have hYLive :
      grantDrainLedgerYSource false true
        (grantDrainNativeNext ring s x x).l
        (grantDrainNativeNext ring s x (ring.rightNeighbor x)).l
        (grantDrainSelect ring s x)
        (grantDrainTokenRow
          (s.request x) (s.grant x) false true
          (grantDrainNativeNext ring s x x).l
          (grantDrainNativeNext ring s x (ring.rightNeighbor x)).l
          (freshRequest s x) (grantDrainSelect ring s x)) ≠ none := by
    have hRaw := hLive
    change
      grantDrainLedgerHost ring freshRequest s x label.host ≠ none
        at hRaw
    rw [hHostEq, hOldRequest, hOldGrant, hRowEq] at hRaw
    intro hNone
    apply hRaw
    rw [hNone]
  obtain ⟨hFire, hSourceFollower, hResponderFollower, hYMove⟩ :=
    grantDrainMarksIncomingYSurvivorRow
      (s.request x) (s.grant x)
      (grantDrainNativeNext ring s x x).l
      (grantDrainNativeNext ring s x (ring.rightNeighbor x)).l
      (freshRequest s x) (grantDrainSelect ring s x) hYLive
  have hNewHost :
      (grantDrainLedgerStep ring freshRequest updateScratch s x label).host =
        some x := by
    change
      grantDrainLedgerHost ring freshRequest s x label.host = some x
    rw [hHostEq, hOldRequest, hOldGrant, hRowEq, hYMove]
  have hXGrantRow :
      (grantDrainLedgerRow ring freshRequest s x).1.grant =
        true := by
    rw [hRowEq, hSourceFollower, hResponderFollower, hFire]
    exact
      (grantDrainMarksUnheldResponderMoves
        (s.request x) (s.grant x) (freshRequest s x)).1
  have hNewGrant :
      (grantDrainStep ring freshRequest updateScratch s x).grant x =
        true := by
    change
      (if x = x then
        (grantDrainLedgerRow ring freshRequest s x).1.grant
      else if x = ring.rightNeighbor x then
        (grantDrainLedgerRow ring freshRequest s x).2.grant
      else s.grant x) = true
    simp only [if_pos rfl, ↓reduceIte]
    exact hXGrantRow
  exact ⟨hFire, hSourceFollower, hResponderFollower,
    hNewHost, hNewGrant⟩

/-- If x is the OLD follower immediately preceding the
strong host g, the old p..g nearest-leader arc has length
at least two. All native records in [p,x) are framed under
ANY selector at x->g; this is the entire new corridor
needed for a surviving label moved to x. -/
theorem grantDrainMarksIncomingFollowerPrefixFrame
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g x : Fin n) (d : Nat)
    (hDistance : PPL.cyclicOffset ring p g = d)
    (hNeighbor : ring.rightNeighbor x = g)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hX : (s.native x).l = false) :
    2 ≤ d ∧
    x = PPL.shiftRight ring p (d - 1) ∧
    PPL.cyclicOffset ring p x = d - 1 ∧
    (∀ k : Nat, k < d - 1 →
      grantDrainNativeNext ring s x (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k)) := by
  have hLeft := grantDrainMarksIncomingLeftRight hn ring x
  have hXLeft : PPL.shiftLeft ring g 1 = x := by
    rw [← hNeighbor]
    exact hLeft
  have hdpos : 1 ≤ d := by
    rw [← hDistance]
    exact hNearest.1
  have hdlt : d < n := by
    rw [← hDistance]
    exact grantDrainMarksArcOffsetLt ring p g
  have hXSite : x = PPL.shiftRight ring p (d - 1) := by
    have hs :=
      grantDrainMarksArcLeftHostSite ring p g d hDistance hdpos
    rw [hXLeft] at hs
    exact hs
  have hdTwo : 2 ≤ d := by
    by_cases hOne : d = 1
    · have hAtP : x = p := by
        rw [hOne] at hXSite
        simpa [grantDrainMarksArcShiftRightZero] using hXSite
      have hBad : (s.native x).l = true := by
        rw [hAtP]
        exact hNearest.2.1
      rw [hX] at hBad
      cases hBad
    · omega
  have hXOff : PPL.cyclicOffset ring p x = d - 1 := by
    rw [hXSite]
    exact grantDrainMarksArcOffsetShiftRight
      ring p (d - 1) (by omega)
  have hFrame :
      ∀ k : Nat, k < d - 1 →
        grantDrainNativeNext ring s x (PPL.shiftRight ring p k) =
          s.native (PPL.shiftRight ring p k) := by
    intro k hk
    have hklt : k < n := by omega
    have hNotX : PPL.shiftRight ring p k ≠ x := by
      intro heq
      have hoff := congrArg (PPL.cyclicOffset ring p) heq
      rw [grantDrainMarksArcOffsetShiftRight ring p k hklt,
        hXOff] at hoff
      omega
    have hNotG : PPL.shiftRight ring p k ≠ g := by
      intro heq
      have hoff := congrArg (PPL.cyclicOffset ring p) heq
      rw [grantDrainMarksArcOffsetShiftRight ring p k hklt,
        hDistance] at hoff
      omega
    exact grantDrainMarksNativeOutsidePairFrame ring s x
      (PPL.shiftRight ring p k) hNotX
      (by rw [hNeighbor]; exact hNotG)
  exact ⟨hdTwo, hXSite, hXOff, hFrame⟩

/-- The new shortest prefix p..x is a genuine protected,
zero-signal arc. The old host g's signal is NEVER needed:
the new corridor excludes x and g, so the E-induced signal
at X does not break strong locking. -/
theorem grantDrainMarksIncomingFollowerProtectedArc
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g x : Fin n)
    (hNeighbor : ring.rightNeighbor x = g)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hX : (s.native x).l = false) :
    GrantDrainMarksNearestArc ring
      (grantDrainNativeNext ring s x) p x ∧
    GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s x) p x ∧
    (grantDrainNativeNext ring s x p).sh = true ∧
    2 ≤ PPL.cyclicOffset ring p g ∧
    (∀ k : Nat, k < PPL.cyclicOffset ring p g - 1 →
      grantDrainNativeNext ring s x (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k)) := by
  obtain ⟨hdTwo, hXSite, hXOff, hFrame⟩ :=
    grantDrainMarksIncomingFollowerPrefixFrame hn ring
      s p g x (PPL.cyclicOffset ring p g) rfl
      hNeighbor hNearest hX
  have hPFrame :
      grantDrainNativeNext ring s x p = s.native p := by
    have h := hFrame 0 (by omega)
    rw [grantDrainMarksArcShiftRightZero] at h
    exact h
  have hNewNearest :
      GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s x) p x := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hXOff]
      omega
    · rw [hPFrame]
      exact hNearest.2.1
    · intro k hk hklt
      rw [hXOff] at hklt
      rw [hFrame k hklt]
      exact hNearest.2.2 k hk (by omega)
  have hNewZero :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s x) p x := by
    intro k hk
    rw [hXOff] at hk
    rw [hFrame k hk]
    exact hZero k (by omega)
  have hNewShield :
      (grantDrainNativeNext ring s x p).sh = true := by
    rw [hPFrame]
    exact hShield
  exact ⟨hNewNearest, hNewZero, hNewShield, hdTwo, hFrame⟩

/-- Exact previously named incoming-Y-host class, now discharged.
A surviving strong label moves to X (coalescence allowed).
The strong mark excludes post-HOLD and its prefix is the
shorter protected arc just proved. -/
theorem grantDrainMarksIncomingFollowerHostLeaf_proved
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainMarksIncomingFollowerHostLeaf
      ring freshRequest updateScratch := by
  intro s x label hP hOldX hOldY hLabelHost hOldPhysical
    hLive hStrong
  rcases hOldPhysical with
    ⟨g, hOldHost, hOldMark, hOldGrant, hOldRequest,
      hOldFollower, hOldLock⟩
  have hg : g = ring.rightNeighbor x :=
    Option.some.inj (hOldHost.symm.trans hLabelHost)
  subst g
  obtain ⟨p, hNearest, hZero, hShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s (ring.rightNeighbor x) hP hOldFollower hOldLock
  obtain ⟨hFire, hLX, hLY, hNewHost, hNewGrant⟩ :=
    grantDrainMarksIncomingFollowerSurvivorMoves
      hn ring freshRequest updateScratch s x label
      hLabelHost hOldRequest hOldGrant hLive
  have hNewFollower :
      ((grantDrainStep ring freshRequest updateScratch s x).native x).l =
        false := by
    change (grantDrainNativeNext ring s x x).l = false
    exact hLX
  obtain ⟨hNewNearest, hNewZero, hNewShield, hDistance, hFrame⟩ :=
    grantDrainMarksIncomingFollowerProtectedArc
      hn ring s p (ring.rightNeighbor x) x rfl
      hNearest hZero hShield hOldX
  have hNewLock :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring freshRequest updateScratch s x)
        x = true :=
    grantDrainMarksOffsetArcStrongLock ring
      (grantDrainStep ring freshRequest updateScratch s x)
      p x hNewNearest hNewZero hNewShield
  have hNewReq :
      (grantDrainStep ring freshRequest updateScratch s x).request x =
        false := by
    cases hReq :
        (grantDrainStep ring freshRequest updateScratch s x).request x with
    | false =>
        rfl
    | true =>
        have hTerminal :=
          grantDrainLedgerMarkNext_of_post_held
            ring freshRequest updateScratch s x x label
            (by change grantDrainLedgerHost ring freshRequest s x label.host = some x; exact hNewHost)
            hReq hNewGrant
        have hMarkEq :
            grantDrainLedgerMarkNext
              ring freshRequest updateScratch s x label = .strong := by
          exact hStrong
        rw [hTerminal] at hMarkEq
        cases hMarkEq
  exact ⟨x, hNewHost, hStrong, hNewGrant, hNewReq,
    hNewFollower, hNewLock⟩

/-- The same incoming X->Y=g class yields the MOVE disjunct
in the original ArcCoverage target: old distance d>=2,
new host=g-1, and the entire leader prefix before g-1 is
unchanged. The lemma also states physical closure directly. -/
theorem grantDrainMarksIncomingFollowerHostCoverage
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (x : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hOldX : (s.native x).l = false)
    (hOldY : (s.native (ring.rightNeighbor x)).l = false)
    (hLabelHost : label.host = some (ring.rightNeighbor x))
    (hOldPhysical : GrantDrainStrongPhysical ring s label)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s x label).host ≠
        none)
    (hStrong :
      (grantDrainLedgerStep ring freshRequest updateScratch s x label).mark =
        .strong) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s x)
      (grantDrainLedgerStep ring freshRequest updateScratch s x label) ∧
    ∃ (p g : Fin n),
      label.host = some g ∧
      GrantDrainMarksNearestArc ring s.native p g ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s x label).host =
            some g ∧
          grantDrainLedgerNominatedHit ring s x label.host = false ∧
          (∀ k : Nat, k < PPL.cyclicOffset ring p g →
            ((grantDrainStep ring freshRequest updateScratch s x).native
              (PPL.shiftRight ring p k)).l =
            (s.native (PPL.shiftRight ring p k)).l)) ∨
        (∃ d : Nat,
          PPL.cyclicOffset ring p g = d ∧ 2 ≤ d ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s x label).host =
            some (PPL.shiftLeft ring g 1) ∧
          (∀ k : Nat, k < d - 1 →
            ((grantDrainStep ring freshRequest updateScratch s x).native
              (PPL.shiftRight ring p k)).l =
            (s.native (PPL.shiftRight ring p k)).l)) ∨
        (∃ j : Nat, 0 < j ∧
          j < PPL.cyclicOffset ring p g ∧
          grantDrainLedgerNominatedHit ring s x label.host = false ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s x label).host =
            some g ∧
          GrantDrainMarksNearestArc ring
            (grantDrainStep ring freshRequest updateScratch s x).native
            (PPL.shiftRight ring p j) g)) := by
  have hPhysicalNext :=
    grantDrainMarksIncomingFollowerHostLeaf_proved
      hn ring freshRequest updateScratch
      s x label hP hOldX hOldY hLabelHost
      hOldPhysical hLive hStrong
  rcases hOldPhysical with
    ⟨g, hOldHost, hOldMark, hOldGrant, hOldRequest,
      hOldFollower, hOldLock⟩
  have hg : g = ring.rightNeighbor x :=
    Option.some.inj (hOldHost.symm.trans hLabelHost)
  subst g
  obtain ⟨p, hNearest, hZero, hShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s (ring.rightNeighbor x) hP hOldFollower hOldLock
  obtain ⟨hFire, hLX, hLY, hNewHost, hNewGrant⟩ :=
    grantDrainMarksIncomingFollowerSurvivorMoves
      hn ring freshRequest updateScratch s x label
      hLabelHost hOldRequest hOldGrant hLive
  obtain ⟨hNewNearest, hNewZero, hNewShield, hdTwo, hFrame⟩ :=
    grantDrainMarksIncomingFollowerProtectedArc
      hn ring s p (ring.rightNeighbor x) x rfl
      hNearest hZero hShield hOldX
  have hNeighborLeft :=
    grantDrainMarksIncomingLeftRight hn ring x
  have hHostLeft :
      (grantDrainLedgerStep ring freshRequest updateScratch s x label).host =
        some (PPL.shiftLeft ring (ring.rightNeighbor x) 1) := by
    rw [hNeighborLeft]
    exact hNewHost
  refine ⟨hPhysicalNext, p, ring.rightNeighbor x,
    hLabelHost, hNearest, Or.inr (Or.inl ?_)⟩
  refine ⟨PPL.cyclicOffset ring p (ring.rightNeighbor x),
    rfl, hdTwo, hHostLeft, ?_⟩
  intro k hk
  have hEq := hFrame k hk
  change (grantDrainNativeNext ring s x
    (PPL.shiftRight ring p k)).l =
      (s.native (PPL.shiftRight ring p k)).l
  rw [hEq]

/-- STILL OPEN: strict-interior selected follower pair X->Y
with both OLD signals zero, both sites strictly inside [p,g),
and the old strong label hosted elsewhere at the right end g.
The native zero arc is covered by StrictInteriorZeroArcStep.
The remaining work is the complete token-host/mark/leader
classification after a possible F0/F1/F2, followed by the
three alternative ArcCoverage branches. This is intentionally
a named Prop, not an asserted theorem. -/
def GrantDrainMarksStrictInteriorFollowerPairLeaf
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    Prop :=
  ∀ (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainLedgerLabel n),
    PPlus ring s.native →
    GrantDrainStrongPhysical ring s label →
    (∃ p g : Fin n,
      label.host = some g ∧
      GrantDrainMarksNearestArc ring s.native p g ∧
      GrantDrainMarksStrictInteriorEdge ring p g e ∧
      (s.native e).l = false ∧
      (s.native (ring.rightNeighbor e)).l = false ∧
      (s.native e).sg = false ∧
      (s.native (ring.rightNeighbor e)).sg = false) →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠
      none →
    (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
      .strong →
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label)

/-!
Status: The declared IncomingFollowerHostLeaf is supplied
by grantDrainMarksIncomingFollowerHostLeaf_proved; its ArcCoverage
MOVE branch is supplied by grantDrainMarksIncomingFollowerHostCoverage.

An old unheld responder grant cannot remain at Y, so there is no
separate Y-stays/strong case; the two physical alternatives are
move/coalescence to X or retirement. An OLD X HOLD would force
a terminal post-mark, contradicting the .strong premise.

The global ArcCoverage and StrongPhysicalClosure definitions are
NOT established here, even after adding 3<=n: strict-interior
follower pairs and other non-boundary edge classes still require
their complete token/mark case assembly. The next precise class
is GrantDrainMarksStrictInteriorFollowerPairLeaf.
-/

end L3

/-!
Strict-interior follower pair, with a genuine selected
native E and F0/F1/F2 classification.

No new protocol field or alternate physical successor is introduced.

All statements below stay in the original source L3 namespace.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A nearest source is uniquely determined by the finite
first-left-leader scan at g. The proof makes the full cyclic inverse
explicit, so no arbitrary name choice is hidden. -/
theorem grantDrainMarksNearestArcUnique
    {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p q g : Fin n)
    (hp : GrantDrainMarksNearestArc ring N p g)
    (hq : GrantDrainMarksNearestArc ring N q g) :
    p = q := by
  have hd :
      PPL.cyclicOffset ring p g =
        PPL.cyclicOffset ring q g :=
    (grantDrainMarksScanOfNearestArc ring N p g hp).symm.trans
      (grantDrainMarksScanOfNearestArc ring N q g hq)
  have hleftP :
      PPL.shiftLeft ring g (PPL.cyclicOffset ring p g) = p := by
    have h := grantDrainMarksArcShiftLeftRight ring p
      (PPL.cyclicOffset ring p g) (PPL.cyclicOffset ring p g)
      (Nat.le_refl _) (grantDrainMarksArcOffsetLt ring p g)
    rw [grantDrainMarksArcShiftRightOffset ring p g] at h
    simpa [Nat.sub_self, grantDrainMarksArcShiftRightZero] using h
  have hleftQ :
      PPL.shiftLeft ring g (PPL.cyclicOffset ring q g) = q := by
    have h := grantDrainMarksArcShiftLeftRight ring q
      (PPL.cyclicOffset ring q g) (PPL.cyclicOffset ring q g)
      (Nat.le_refl _) (grantDrainMarksArcOffsetLt ring q g)
    rw [grantDrainMarksArcShiftRightOffset ring q g] at h
    simpa [Nat.sub_self, grantDrainMarksArcShiftRightZero] using h
  calc
    p = PPL.shiftLeft ring g (PPL.cyclicOffset ring p g) :=
      hleftP.symm
    _ = PPL.shiftLeft ring g (PPL.cyclicOffset ring q g) := by
      rw [hd]
    _ = q := hleftQ

/-- Generic strict-interior FIRE: a canonical birth at the old
clockwise offset j produces a closer shielded first leader, and
the new zero corridor is exactly a suffix of the old zero corridor.
This lemma uses the full old selected two-follower E row. -/
theorem grantDrainMarksStrictInteriorFireSuffix
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (p g e b : Fin n) (j : Nat)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZeroPost : GrantDrainMarksZeroOffsetArc ring
      (grantDrainNativeNext ring s e) p g)
    (hLX : (s.native e).l = false)
    (hLY : (s.native (ring.rightNeighbor e)).l = false)
    (hSX : (s.native e).sg = false)
    (hSY : (s.native (ring.rightNeighbor e)).sg = false)
    (hSite : b = PPL.shiftRight ring p j)
    (hJPos : 0 < j)
    (hJLt : j < PPL.cyclicOffset ring p g)
    (hBirth :
      grantDrainNativeNext ring s e =
        canonicalBirth (nativeE ring s.native e) b) :
    GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s e) b g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) b g ∧
      (grantDrainNativeNext ring s e b).sh = true := by
  have hOffset :
      PPL.cyclicOffset ring b g =
        PPL.cyclicOffset ring p g - j := by
    rw [hSite]
    exact grantDrainMarksArcOffsetSubtract ring p g j
      (Nat.le_of_lt hJLt)
  have hRootLeader :
      (grantDrainNativeNext ring s e b).l = true := by
    rw [hBirth]
    exact (grantDrainMarksBirthIsProtected
      (nativeE ring s.native e) b).1
  have hRootShield :
      (grantDrainNativeNext ring s e b).sh = true := by
    rw [hBirth]
    exact (grantDrainMarksBirthIsProtected
      (nativeE ring s.native e) b).2.2.1
  have hNearNew :
      GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s e) b g := by
    refine ⟨?_, hRootLeader, ?_⟩
    · rw [hOffset]
      omega
    · intro k hk hklt
      have hWithin : j + k < PPL.cyclicOffset ring p g := by
        rw [hOffset] at hklt
        omega
      have hJBound : j < n :=
        Nat.lt_trans hJLt (grantDrainMarksArcOffsetLt ring p g)
      have hSumBound : j + k < n :=
        Nat.lt_trans hWithin (grantDrainMarksArcOffsetLt ring p g)
      have hShift :
          PPL.shiftRight ring b k =
            PPL.shiftRight ring p (j + k) := by
        rw [hSite]
        exact grantDrainMarksArcShiftRightAdd ring p j k
      have hDifferent :
          PPL.shiftRight ring p (j + k) ≠ b := by
        intro he
        rw [hSite] at he
        have ho := congrArg (PPL.cyclicOffset ring p) he
        rw [grantDrainMarksArcOffsetShiftRight ring p
            (j + k) hSumBound,
          grantDrainMarksArcOffsetShiftRight ring p j hJBound]
          at ho
        omega
      have hFrame := grantDrainMarksBirthOtherSite
        (nativeE ring s.native e) b
        (PPL.shiftRight ring p (j + k)) hDifferent
      have hE := grantDrainMarksInteriorNativeELeaderAt
        ring s e (PPL.shiftRight ring p (j + k))
          hLX hLY hSX hSY
      calc
        (grantDrainNativeNext ring s e
            (PPL.shiftRight ring b k)).l =
          (canonicalBirth (nativeE ring s.native e) b
            (PPL.shiftRight ring p (j + k))).l := by
              rw [hBirth, hShift]
        _ = (nativeE ring s.native e
            (PPL.shiftRight ring p (j + k))).l :=
              congrArg CertNative.l hFrame
        _ = (s.native
            (PPL.shiftRight ring p (j + k))).l := hE
        _ = false :=
          hNearest.2.2 (j + k) (by omega) hWithin
  have hZeroSuffix :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) b g := by
    intro k hk
    have hWithin : j + k < PPL.cyclicOffset ring p g := by
      rw [hOffset] at hk
      omega
    have hShift :
        PPL.shiftRight ring b k =
          PPL.shiftRight ring p (j + k) := by
      rw [hSite]
      exact grantDrainMarksArcShiftRightAdd ring p j k
    rw [hShift]
    exact hZeroPost (j + k) hWithin
  exact ⟨hNearNew, hZeroSuffix, hRootShield⟩

/-- Exact strict-interior follower-pair analysis, including the
physical strong lock AND the precise arc-coverage disjunction.
The strong label's host is not one of the selected two endpoints.
No old-token or grant assumptions at those endpoints are omitted:
all four actual FIRE selector outcomes are covered. -/
theorem grantDrainMarksStrictInteriorFollowerPairCoverage
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (p g : Fin n)
    (hHost : label.host = some g)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hInside : GrantDrainMarksStrictInteriorEdge ring p g e)
    (hLX : (s.native e).l = false)
    (hLY : (s.native (ring.rightNeighbor e)).l = false)
    (hSX : (s.native e).sg = false)
    (hSY : (s.native (ring.rightNeighbor e)).sg = false)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠
        none)
    (hStrong :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
        .strong) :
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
    ∃ (q h : Fin n),
      label.host = some h ∧
      GrantDrainMarksNearestArc ring s.native q h ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some h ∧
          grantDrainLedgerNominatedHit ring s e label.host = false ∧
          (∀ k : Nat, k < PPL.cyclicOffset ring q h →
            ((grantDrainStep ring freshRequest updateScratch s e).native
              (PPL.shiftRight ring q k)).l =
            (s.native (PPL.shiftRight ring q k)).l)) ∨
        (∃ d : Nat,
          PPL.cyclicOffset ring q h = d ∧ 2 ≤ d ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some (PPL.shiftLeft ring h 1) ∧
          (∀ k : Nat, k < d - 1 →
            ((grantDrainStep ring freshRequest updateScratch s e).native
              (PPL.shiftRight ring q k)).l =
            (s.native (PPL.shiftRight ring q k)).l)) ∨
        (∃ j : Nat, 0 < j ∧
          j < PPL.cyclicOffset ring q h ∧
          grantDrainLedgerNominatedHit ring s e label.host = false ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some h ∧
          GrantDrainMarksNearestArc ring
            (grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring q j) h)) := by
  rcases hPhysical with
    ⟨oldG, hOldHost, hOldMark, hOldGrant, hOldRequest,
      hOldFollower, hOldLock⟩
  have hG : oldG = g :=
    Option.some.inj (hOldHost.symm.trans hHost)
  subst oldG
  obtain ⟨oldP, hOldNearest, hZero, hShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s g hP hOldFollower hOldLock
  have hPSource : oldP = p :=
    grantDrainMarksNearestArcUnique
      ring s.native oldP p g hOldNearest hNearest
  subst oldP
  have hAvoid :=
    grantDrainMarksStrictInteriorAvoidEndpoints ring p g e hInside
  have hOutsideX : g ≠ e := Ne.symm hAvoid.2.2.1
  have hOutsideY : g ≠ ring.rightNeighbor e :=
    Ne.symm hAvoid.2.2.2
  have hRootX : p ≠ e := Ne.symm hAvoid.1
  have hRootY : p ≠ ring.rightNeighbor e :=
    Ne.symm hAvoid.2.1
  have hNewHost :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
        some g := by
    change grantDrainLedgerHost ring freshRequest s e label.host =
      some g
    exact grantDrainMarksInteriorHostFrame
      ring freshRequest s e g label hHost hOutsideX hOutsideY
  have hTokenFrame := grantDrainMarksInteriorTokenFrame
    ring freshRequest updateScratch s e g hOutsideX hOutsideY
  have hNewGrant :
      (grantDrainStep ring freshRequest updateScratch s e).grant g =
        true := by
    rw [hTokenFrame.2]
    exact hOldGrant
  have hNewRequest :
      (grantDrainStep ring freshRequest updateScratch s e).request g =
        false := by
    rw [hTokenFrame.1]
    exact hOldRequest
  have hNativeAtG :=
    grantDrainMarksNativeOutsidePairFrame
      ring s e g hOutsideX hOutsideY
  have hNewFollower :
      ((grantDrainStep ring freshRequest updateScratch s e).native g).l =
        false := by
    change (grantDrainNativeNext ring s e g).l = false
    rw [hNativeAtG]
    exact hOldFollower
  have hNewZero := grantDrainMarksStrictInteriorZeroArcStep
    ring s p g e hNearest hZero hInside
  have hNoHit :
      grantDrainLedgerNominatedHit ring s e label.host = false := by
    rw [hHost]
    simp [grantDrainLedgerNominatedHit, hOldRequest, hAvoid.2.2.2]
  have hPostPhysical :
      ∀ q : Fin n,
        GrantDrainMarksNearestArc ring
          (grantDrainNativeNext ring s e) q g →
        GrantDrainMarksZeroOffsetArc ring
          (grantDrainNativeNext ring s e) q g →
        (grantDrainNativeNext ring s e q).sh = true →
        GrantDrainStrongPhysical ring
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerStep ring freshRequest updateScratch s e label) := by
    intro q hNearestNext hZeroNext hShieldNext
    have hNewLock :
        grantDrainLedgerStrongLock ring
          (grantDrainStep ring freshRequest updateScratch s e) g =
            true := by
      exact grantDrainMarksOffsetArcStrongLock
        ring (grantDrainStep ring freshRequest updateScratch s e)
          q g hNearestNext hZeroNext hShieldNext
    exact ⟨g, hNewHost, hStrong, hNewGrant,
      hNewRequest, hNewFollower, hNewLock⟩
  have hFireOutcome :
      ∀ (b : Fin n) (j : Nat),
        b = PPL.shiftRight ring p j →
        0 < j →
        j < PPL.cyclicOffset ring p g →
        grantDrainNativeNext ring s e =
          canonicalBirth (nativeE ring s.native e) b →
        GrantDrainStrongPhysical ring
          (grantDrainStep ring freshRequest updateScratch s e)
          (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
        (∃ j : Nat, 0 < j ∧
          j < PPL.cyclicOffset ring p g ∧
          grantDrainLedgerNominatedHit ring s e label.host = false ∧
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some g ∧
          GrantDrainMarksNearestArc ring
            (grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring p j) g) := by
    intro b j hSite hjpos hjlt hBirth
    obtain ⟨hNearestB, hZeroB, hShieldB⟩ :=
      grantDrainMarksStrictInteriorFireSuffix
        ring s p g e b j hNearest hNewZero
          hLX hLY hSX hSY hSite hjpos hjlt hBirth
    have hPhysicalB :=
      hPostPhysical b hNearestB hZeroB hShieldB
    refine ⟨hPhysicalB, j, hjpos, hjlt,
      hNoHit, hNewHost, ?_⟩
    rw [← hSite]
    exact hNearestB
  cases hf : grantDrainSelect ring s e with
  | none =>
      have hLeaderFrame :
          ∀ i : Fin n,
            (grantDrainNativeNext ring s e i).l = (s.native i).l :=
        fun i => grantDrainMarksInteriorNoFireLeaderFrame
          ring s e i hLX hLY hSX hSY hf
      have hNearestNext :
          GrantDrainMarksNearestArc ring
            (grantDrainNativeNext ring s e) p g := by
        refine ⟨hNearest.1, ?_, ?_⟩
        · rw [hLeaderFrame p]
          exact hNearest.2.1
        · intro k hk hklt
          rw [hLeaderFrame (PPL.shiftRight ring p k)]
          exact hNearest.2.2 k hk hklt
      have hShieldNext :
          (grantDrainNativeNext ring s e p).sh = true := by
        rw [grantDrainMarksNativeOutsidePairFrame
          ring s e p hRootX hRootY]
        exact hShield
      have hPhysicalNext :=
        hPostPhysical p hNearestNext hNewZero hShieldNext
      refine ⟨hPhysicalNext, p, g, hHost,
        hNearest, Or.inl ?_⟩
      exact ⟨hNewHost, hNoHit, fun k hk =>
        hLeaderFrame (PPL.shiftRight ring p k)⟩
  | leftLocal =>
      have hBirth :
          grantDrainNativeNext ring s e =
            canonicalBirth (nativeE ring s.native e) e := by
        simp [grantDrainNativeNext, hf]
      obtain ⟨hPhysicalNext, hArcNext⟩ :=
        hFireOutcome e (PPL.cyclicOffset ring p e)
          (grantDrainMarksArcShiftRightOffset ring p e).symm
          hInside.1 hInside.2.1 hBirth
      exact ⟨hPhysicalNext, p, g, hHost,
        hNearest, Or.inr (Or.inr hArcNext)⟩
  | rightLocal =>
      have hBirth :
          grantDrainNativeNext ring s e =
            canonicalBirth (nativeE ring s.native e)
              (ring.rightNeighbor e) := by
        simp [grantDrainNativeNext, hf]
      obtain ⟨hPhysicalNext, hArcNext⟩ :=
        hFireOutcome (ring.rightNeighbor e)
          (PPL.cyclicOffset ring p (ring.rightNeighbor e))
          (grantDrainMarksArcShiftRightOffset ring p
            (ring.rightNeighbor e)).symm
          hInside.2.2.1 hInside.2.2.2 hBirth
      exact ⟨hPhysicalNext, p, g, hHost,
        hNearest, Or.inr (Or.inr hArcNext)⟩
  | cross =>
      have hBirth :
          grantDrainNativeNext ring s e =
            canonicalBirth (nativeE ring s.native e) e := by
        simp [grantDrainNativeNext, hf]
      obtain ⟨hPhysicalNext, hArcNext⟩ :=
        hFireOutcome e (PPL.cyclicOffset ring p e)
          (grantDrainMarksArcShiftRightOffset ring p e).symm
          hInside.1 hInside.2.1 hBirth
      exact ⟨hPhysicalNext, p, g, hHost,
        hNearest, Or.inr (Or.inr hArcNext)⟩

/-- The previously named strict-interior physical leaf, discharged
by the same F0/F1/F2 case split and source-scope suffix geometry. -/
theorem grantDrainMarksStrictInteriorFollowerPairLeaf_proved
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainMarksStrictInteriorFollowerPairLeaf
      ring freshRequest updateScratch := by
  intro s e label hP hPhysical hGeometry hLive hStrong
  obtain ⟨p, g, hHost, hNearest, hInside,
    hLX, hLY, hSX, hSY⟩ := hGeometry
  exact (grantDrainMarksStrictInteriorFollowerPairCoverage
    hn ring freshRequest updateScratch s e label
    hP hPhysical p g hHost hNearest hInside
    hLX hLY hSX hSY hLive hStrong).1

end L3


/-!
The three exterior/boundary leaf classes and a disjoint
cyclic edge partition.
No original declarations above are altered.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The two original global conclusions packaged at one OLD edge.
This is definitionally the pair of source-scope StrongPhysicalClosure
and StrongArcCoverage conclusions, not a strengthened class. -/
def GrantDrainMarksEdgeCoverAt
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainLedgerLabel n) : Prop :=
  GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
    ∃ (p g : Fin n),
      label.host = some g ∧
      GrantDrainMarksNearestArc ring s.native p g ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some g ∧
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        (∀ k : Nat, k < PPL.cyclicOffset ring p g →
          ((grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l)) ∨
      (∃ d : Nat,
        PPL.cyclicOffset ring p g = d ∧ 2 ≤ d ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some (PPL.shiftLeft ring g 1) ∧
        (∀ k : Nat, k < d - 1 →
          ((grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l)) ∨
      (∃ j : Nat, 0 < j ∧
        j < PPL.cyclicOffset ring p g ∧
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some g ∧
        GrantDrainMarksNearestArc ring
          (grantDrainStep ring freshRequest updateScratch s e).native
          (PPL.shiftRight ring p j) g))

/-- Any shielded, zero-signal protected leader p remains the
same nearest source of g under an arbitrary incoming e -> p.
The selected initiator is genuinely unrestricted and may FIRE.
This is the source geometry without token assumptions. -/
theorem grantDrainMarksIncomingProtectedFrame
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e p g : Fin n)
    (hIncoming : ring.rightNeighbor e = p)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true) :
    GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s e) p g ∧
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) p g ∧
      (grantDrainNativeNext ring s e p).sh = true := by
  have hSignal : (s.native p).sg = false := by
    have hz := hZero 0 hNearest.1
    simpa [grantDrainMarksArcShiftRightZero] using hz
  have hNear := grantDrainMarksIncomingSourceNearestArc
    hn ring s p g e hIncoming hNearest hShield hSignal
  have hZeroNew := grantDrainMarksIncomingSourceZeroArc
    hn ring s p g e hIncoming hNearest.2.1 hShield hSignal hZero
  have hRoot := grantDrainMarksIncomingProtectedNativeNext
    hn ring s e
    (by rw [hIncoming]; exact hNearest.2.1)
    (by rw [hIncoming]; exact hShield)
    (by rw [hIncoming]; exact hSignal)
  refine ⟨hNear, hZeroNew, ?_⟩
  rw [← hIncoming]
  exact hRoot.2.1

/-- Every incoming service to protected p with host g away from
the initiator preserves the complete physical strong record.
The source X may have arbitrary bullet, shield, signal,
request, and grant. The protected Y has l=sh=1 and sg=0.
The old label at g is untouched by both selected endpoints. -/
theorem grantDrainMarksIncomingExteriorProtectedCoverage
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hHost : label.host = some g)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hIncoming : ring.rightNeighbor e = p)
    (hNotHost : e ≠ g)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠ none)
    (hStrong :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
        .strong) :
    GrantDrainMarksEdgeCoverAt ring freshRequest updateScratch
      s e label := by
  rcases hPhysical with
    ⟨oldG, hOldHost, hOldMark, hOldGrant, hOldRequest,
      hOldFollower, hOldLock⟩
  have hSame : oldG = g :=
    Option.some.inj (hOldHost.symm.trans hHost)
  subst oldG
  have hGp : g ≠ p := by
    intro heq
    have hp := hNearest.1
    rw [heq, grantDrainMarksArcOffsetZero ring p] at hp
    omega
  have hYNotHost : g ≠ ring.rightNeighbor e := by
    rw [hIncoming]
    exact hGp
  have hXNotHost : g ≠ e := Ne.symm hNotHost
  have hNewHost :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
        some g := by
    change grantDrainLedgerHost ring freshRequest s e label.host = some g
    exact grantDrainMarksInteriorHostFrame
      ring freshRequest s e g label hHost hXNotHost hYNotHost
  have hTokens := grantDrainMarksInteriorTokenFrame
    ring freshRequest updateScratch s e g hXNotHost hYNotHost
  have hGrant :
      (grantDrainStep ring freshRequest updateScratch s e).grant g = true := by
    rw [hTokens.2]
    exact hOldGrant
  have hRequest :
      (grantDrainStep ring freshRequest updateScratch s e).request g = false := by
    rw [hTokens.1]
    exact hOldRequest
  have hNativeAtG :=
    grantDrainMarksNativeOutsidePairFrame
      ring s e g hXNotHost hYNotHost
  have hFollower :
      ((grantDrainStep ring freshRequest updateScratch s e).native g).l =
        false := by
    change (grantDrainNativeNext ring s e g).l = false
    rw [hNativeAtG]
    exact hOldFollower
  have hGeometry := grantDrainMarksIncomingProtectedFrame
    hn ring s e p g hIncoming hNearest hZero hShield
  have hLock :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring freshRequest updateScratch s e) g = true :=
    grantDrainMarksOffsetArcStrongLock
      ring (grantDrainStep ring freshRequest updateScratch s e)
      p g hGeometry.1 hGeometry.2.1 hGeometry.2.2
  have hNoHit :
      grantDrainLedgerNominatedHit ring s e label.host = false := by
    rw [hHost]
    simp [grantDrainLedgerNominatedHit, hOldRequest,
      hIncoming, Ne.symm hGp]
  have hFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p g →
        ((grantDrainStep ring freshRequest updateScratch s e).native
          (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l := by
    intro k hk
    exact grantDrainMarksLeaderFrameOfNearest
      ring s.native (grantDrainNativeNext ring s e)
      p g hNearest hGeometry.1 k hk
  change
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
    ∃ (q h : Fin n), label.host = some h ∧
      GrantDrainMarksNearestArc ring s.native q h ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some h ∧
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        (∀ k : Nat, k < PPL.cyclicOffset ring q h →
          ((grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring q k)).l =
          (s.native (PPL.shiftRight ring q k)).l)) ∨
      (∃ d : Nat,
        PPL.cyclicOffset ring q h = d ∧ 2 ≤ d ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some (PPL.shiftLeft ring h 1) ∧
        (∀ k : Nat, k < d - 1 →
          ((grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring q k)).l =
          (s.native (PPL.shiftRight ring q k)).l)) ∨
      (∃ j : Nat, 0 < j ∧ j < PPL.cyclicOffset ring q h ∧
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some h ∧
        GrantDrainMarksNearestArc ring
          (grantDrainStep ring freshRequest updateScratch s e).native
          (PPL.shiftRight ring q j) h))
  refine ⟨⟨g, hNewHost, hStrong, hGrant, hRequest,
    hFollower, hLock⟩, p, g, hHost, hNearest, Or.inl ?_⟩
  exact ⟨hNewHost, hNoHit, hFrame⟩


/-- In the adjacent protected-source edge p -> g the final
initiator is an OLD leader. The OLD responder grant is physically
sunk, and its label cannot survive at X: the Y-source mover requires
post-X to be a follower. Thus the ArcCoverage/PhysicalClosure
antecedent is vacuous on this edge, for arbitrary OLD token flags
and arbitrary fresh responder requests. -/
theorem grantDrainMarksProtectedAdjacentHostRetired
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hNeighbor : ring.rightNeighbor p = g)
    (hHost : label.host = some g)
    (hLeader : (s.native p).l = true)
    (hFollower : (s.native g).l = false)
    (hGrant : s.grant g = true) :
    (grantDrainLedgerStep ring freshRequest updateScratch s p label).host =
      none := by
  have hDistinct : g ≠ p := by
    intro hg
    rw [hg, hLeader] at hFollower
    cases hFollower
  have hFinalX :
      (grantDrainNativeNext ring s p p).l = true :=
    grantDrainMarksOutgoingLeaderNext ring s p hLeader
  have hSink :=
    grantDrainMarksOutgoingLeaderAdjacentGrantSunk
      ring freshRequest updateScratch s p g hNeighbor
      hLeader hFollower hGrant
  have hRowY :
      (grantDrainLedgerRow ring freshRequest s p).2.grant =
        false := by
    change (if g = p then
        (grantDrainLedgerRow ring freshRequest s p).1.grant
      else if g = ring.rightNeighbor p then
        (grantDrainLedgerRow ring freshRequest s p).2.grant
      else s.grant g) = false at hSink
    simpa only [if_neg hDistinct, if_pos hNeighbor.symm]
      using hSink
  have hYSource :
      grantDrainLedgerYSource
        (s.request g) (s.grant g)
        (grantDrainNativeNext ring s p p).l
        (grantDrainNativeNext ring s p g).l
        (grantDrainSelect ring s p)
        (grantDrainLedgerRow ring freshRequest s p) = none := by
    simp [grantDrainLedgerYSource, hGrant, hFinalX, hRowY]
  change grantDrainLedgerHost ring freshRequest s p label.host =
    none
  rw [hHost]
  simp [grantDrainLedgerHost, hNeighbor, hDistinct,
    hYSource]

/-- The exact source row at an arbitrary exterior pair frames
the entire clockwise protected prefix, even when it performs a
canonical FIRE at one of the two outside endpoints. The host g
may itself be the initiator, in which case the already-proved
OutgoingHostStrongGeometry supplies its token and mark behavior. -/
theorem grantDrainMarksExteriorPairCoverage
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e p g : Fin n)
    (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hHost : label.host = some g)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hAway : ∀ k : Nat,
      k < PPL.cyclicOffset ring p g →
        PPL.shiftRight ring p k ≠ e ∧
          PPL.shiftRight ring p k ≠ ring.rightNeighbor e)
    (hResponderNotHost : ring.rightNeighbor e ≠ g)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠ none)
    (hStrong :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
        .strong) :
    GrantDrainMarksEdgeCoverAt ring freshRequest updateScratch
      s e label := by
  rcases hPhysical with
    ⟨oldG, hOldHost, hOldMark, hOldGrant, hOldRequest,
      hOldFollower, hOldLock⟩
  have hSame : oldG = g :=
    Option.some.inj (hOldHost.symm.trans hHost)
  subst oldG
  have hPoint :
      ∀ k : Nat, k < PPL.cyclicOffset ring p g →
        grantDrainNativeNext ring s e
          (PPL.shiftRight ring p k) =
        s.native (PPL.shiftRight ring p k) := by
    intro k hk
    have hh := hAway k hk
    exact grantDrainMarksNativeOutsidePairFrame
      ring s e (PPL.shiftRight ring p k) hh.1 hh.2
  have hNearestNext :
      GrantDrainMarksNearestArc ring
        (grantDrainNativeNext ring s e) p g := by
    refine ⟨hNearest.1, ?_, ?_⟩
    · have hp := hPoint 0 hNearest.1
      rw [grantDrainMarksArcShiftRightZero] at hp
      rw [hp]
      exact hNearest.2.1
    · intro k hk hklt
      rw [hPoint k hklt]
      exact hNearest.2.2 k hk hklt
  have hZeroNext :
      GrantDrainMarksZeroOffsetArc ring
        (grantDrainNativeNext ring s e) p g := by
    intro k hk
    rw [hPoint k hk]
    exact hZero k hk
  have hShieldNext :
      (grantDrainNativeNext ring s e p).sh = true := by
    have hp := hPoint 0 hNearest.1
    rw [grantDrainMarksArcShiftRightZero] at hp
    rw [hp]
    exact hShield
  have hLockNext :
      grantDrainLedgerStrongLock ring
        (grantDrainStep ring freshRequest updateScratch s e) g = true :=
    grantDrainMarksOffsetArcStrongLock
      ring (grantDrainStep ring freshRequest updateScratch s e)
      p g hNearestNext hZeroNext hShieldNext
  have hFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p g →
        ((grantDrainStep ring freshRequest updateScratch s e).native
          (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l := by
    intro k hk
    exact congrArg CertNative.l (hPoint k hk)
  have hPost :
      GrantDrainStrongPhysical ring
        (grantDrainStep ring freshRequest updateScratch s e)
        (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
        some g ∧
      grantDrainLedgerNominatedHit ring s e label.host = false := by
    by_cases hAt : e = g
    · have hGeo := grantDrainMarksOutgoingHostStrongGeometry
        hn ring freshRequest updateScratch s e label hP
        ⟨g, hHost, hOldMark, hOldGrant, hOldRequest,
          hOldFollower, hOldLock⟩
        (by simpa [hAt] using hHost)
      refine ⟨hGeo.1, ?_, hGeo.2.2.2.1⟩
      simpa [hAt] using hGeo.2.1
    · have hNotX : g ≠ e := Ne.symm hAt
      have hNotY : g ≠ ring.rightNeighbor e :=
        Ne.symm hResponderNotHost
      have hHostNext :
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            some g := by
        change grantDrainLedgerHost ring freshRequest s e label.host =
          some g
        exact grantDrainMarksInteriorHostFrame
          ring freshRequest s e g label hHost hNotX hNotY
      have hTokens := grantDrainMarksInteriorTokenFrame
        ring freshRequest updateScratch s e g hNotX hNotY
      have hNativeG := grantDrainMarksNativeOutsidePairFrame
        ring s e g hNotX hNotY
      have hGrantNext :
          (grantDrainStep ring freshRequest updateScratch s e).grant g =
            true := by
        rw [hTokens.2]
        exact hOldGrant
      have hRequestNext :
          (grantDrainStep ring freshRequest updateScratch s e).request g =
            false := by
        rw [hTokens.1]
        exact hOldRequest
      have hFollowerNext :
          ((grantDrainStep ring freshRequest updateScratch s e).native g).l =
            false := by
        change (grantDrainNativeNext ring s e g).l = false
        rw [hNativeG]
        exact hOldFollower
      have hNoHit :
          grantDrainLedgerNominatedHit ring s e label.host = false := by
        rw [hHost]
        simp [grantDrainLedgerNominatedHit, hOldRequest,
          hResponderNotHost]
      refine ⟨?_, hHostNext, hNoHit⟩
      exact ⟨g, hHostNext, hStrong, hGrantNext,
        hRequestNext, hFollowerNext, hLockNext⟩
  change
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s e)
      (grantDrainLedgerStep ring freshRequest updateScratch s e label) ∧
    ∃ (q h : Fin n), label.host = some h ∧
      GrantDrainMarksNearestArc ring s.native q h ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some h ∧
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        (∀ k : Nat, k < PPL.cyclicOffset ring q h →
          ((grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring q k)).l =
          (s.native (PPL.shiftRight ring q k)).l)) ∨
      (∃ d : Nat,
        PPL.cyclicOffset ring q h = d ∧ 2 ≤ d ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some (PPL.shiftLeft ring h 1) ∧
        (∀ k : Nat, k < d - 1 →
          ((grantDrainStep ring freshRequest updateScratch s e).native
            (PPL.shiftRight ring q k)).l =
          (s.native (PPL.shiftRight ring q k)).l)) ∨
      (∃ j : Nat, 0 < j ∧ j < PPL.cyclicOffset ring q h ∧
        grantDrainLedgerNominatedHit ring s e label.host = false ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
          some h ∧
        GrantDrainMarksNearestArc ring
          (grantDrainStep ring freshRequest updateScratch s e).native
          (PPL.shiftRight ring q j) h))
  exact ⟨hPost.1, p, g, hHost, hNearest,
    Or.inl ⟨hPost.2.1, hPost.2.2, hFrame⟩⟩


/-- The directed edge has one of seven disjoint numerical
positions relative to the half-open protected corridor [p,g):
protected source adjacent/long, whole-ring host boundary,
incoming host, strict interior, incoming protected source,
or exterior. Exterior INCLUDES outgoing g -> g+1 when g+1 != p. -/
inductive GrantDrainMarksEdgeClass where
  | protectedAdjacent
  | protectedLong
  | wholeBoundary
  | incomingHost
  | strictInterior
  | incomingProtected
  | exterior
  deriving DecidableEq, Repr

def GrantDrainMarksEdgeClassAt
    {n : Nat} (ring : DirectedRing n)
    (p g e : Fin n)
    (kind : GrantDrainMarksEdgeClass) : Prop :=
  match kind with
  | .protectedAdjacent =>
      PPL.cyclicOffset ring p e = 0 ∧
        PPL.cyclicOffset ring p g = 1
  | .protectedLong =>
      PPL.cyclicOffset ring p e = 0 ∧
        1 < PPL.cyclicOffset ring p g
  | .wholeBoundary =>
      PPL.cyclicOffset ring p e = n - 1 ∧
        PPL.cyclicOffset ring p g = n - 1
  | .incomingHost =>
      0 < PPL.cyclicOffset ring p e ∧
        PPL.cyclicOffset ring p e + 1 =
          PPL.cyclicOffset ring p g
  | .strictInterior =>
      0 < PPL.cyclicOffset ring p e ∧
        PPL.cyclicOffset ring p e + 1 <
          PPL.cyclicOffset ring p g
  | .incomingProtected =>
      PPL.cyclicOffset ring p e = n - 1 ∧
        PPL.cyclicOffset ring p g < n - 1
  | .exterior =>
      PPL.cyclicOffset ring p g ≤
        PPL.cyclicOffset ring p e ∧
        PPL.cyclicOffset ring p e + 1 < n

/-- Exact cyclic-position exclusivity. -/
theorem grantDrainMarksCyclicClassesExclusive
    {n : Nat} (ring : DirectedRing n)
    (p g e : Fin n)
    (one two : GrantDrainMarksEdgeClass)
    (hOne : GrantDrainMarksEdgeClassAt ring p g e one)
    (hTwo : GrantDrainMarksEdgeClassAt ring p g e two) :
    one = two := by
  cases one <;> cases two <;>
    dsimp [GrantDrainMarksEdgeClassAt] at hOne hTwo <;>
    first | rfl | omega

/-- Every edge falls in EXACTLY ONE position under a genuine
positive nearest-source offset. The proof is purely Nat arithmetic
after cyclic offset ranges; no extra physical invariant is assumed. -/
theorem grantDrainMarksCyclicEdgePartitionOfThree
    {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (p g e : Fin n)
    (hPos : 0 < PPL.cyclicOffset ring p g) :
    ∃ kind : GrantDrainMarksEdgeClass,
      GrantDrainMarksEdgeClassAt ring p g e kind ∧
        ∀ other : GrantDrainMarksEdgeClass,
          GrantDrainMarksEdgeClassAt ring p g e other → other = kind := by
  have hdlt : PPL.cyclicOffset ring p g < n :=
    grantDrainMarksArcOffsetLt ring p g
  have hklt : PPL.cyclicOffset ring p e < n :=
    grantDrainMarksArcOffsetLt ring p e
  have hCases :
      (PPL.cyclicOffset ring p e = 0 ∧
        PPL.cyclicOffset ring p g = 1) ∨
      (PPL.cyclicOffset ring p e = 0 ∧
        1 < PPL.cyclicOffset ring p g) ∨
      (PPL.cyclicOffset ring p e = n - 1 ∧
        PPL.cyclicOffset ring p g = n - 1) ∨
      (0 < PPL.cyclicOffset ring p e ∧
        PPL.cyclicOffset ring p e + 1 =
          PPL.cyclicOffset ring p g) ∨
      (0 < PPL.cyclicOffset ring p e ∧
        PPL.cyclicOffset ring p e + 1 <
          PPL.cyclicOffset ring p g) ∨
      (PPL.cyclicOffset ring p e = n - 1 ∧
        PPL.cyclicOffset ring p g < n - 1) ∨
      (PPL.cyclicOffset ring p g ≤
        PPL.cyclicOffset ring p e ∧
        PPL.cyclicOffset ring p e + 1 < n) := by
    omega
  have hExists :
      ∃ kind : GrantDrainMarksEdgeClass,
        GrantDrainMarksEdgeClassAt ring p g e kind := by
    rcases hCases with ha | hb | hc | hd | he | hf | hg
    · exact ⟨.protectedAdjacent, ha⟩
    · exact ⟨.protectedLong, hb⟩
    · exact ⟨.wholeBoundary, hc⟩
    · exact ⟨.incomingHost, hd⟩
    · exact ⟨.strictInterior, he⟩
    · exact ⟨.incomingProtected, hf⟩
    · exact ⟨.exterior, hg⟩
  obtain ⟨kind, hKind⟩ := hExists
  exact ⟨kind, hKind, fun other hOther =>
    grantDrainMarksCyclicClassesExclusive ring p g e
      other kind hOther hKind⟩

/-- Immediate physical-state specialization of the pure offset
partition to an actual old nearest protected leader. -/
theorem grantDrainMarksCyclicEdgePartition
    {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (p g e : Fin n)
    (hNearest : GrantDrainMarksNearestArc ring N p g) :
    ∃ kind : GrantDrainMarksEdgeClass,
      GrantDrainMarksEdgeClassAt ring p g e kind ∧
        ∀ other : GrantDrainMarksEdgeClass,
          GrantDrainMarksEdgeClassAt ring p g e other → other = kind :=
  grantDrainMarksCyclicEdgePartitionOfThree
    hn ring p g e hNearest.1

/-- A physical right-neighbor edge is one clockwise shift
after its selected source's canonical offset from p. -/
theorem grantDrainMarksNeighborOfOffset
    {n : Nat} (ring : DirectedRing n)
    (p e : Fin n) :
    ring.rightNeighbor e =
      PPL.shiftRight ring p (PPL.cyclicOffset ring p e + 1) := by
  calc
    ring.rightNeighbor e = PPL.shiftRight ring e 1 := by
      apply Fin.ext
      rfl
    _ = PPL.shiftRight ring
          (PPL.shiftRight ring p (PPL.cyclicOffset ring p e))
          1 := by rw [grantDrainMarksArcShiftRightOffset ring p e]
    _ = PPL.shiftRight ring p
          (PPL.cyclicOffset ring p e + 1) :=
          grantDrainMarksArcShiftRightAdd ring p
            (PPL.cyclicOffset ring p e) 1

theorem grantDrainMarksFullRotation
    {n : Nat} (ring : DirectedRing n) (p : Fin n) :
    PPL.shiftRight ring p n = p := by
  apply Fin.ext
  change (p.val + n) % n = p.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]


/-- A whole-ring boundary service g -> p (host g is the last
clockwise follower before protected p) is covered by the existing
physical outgoing-host result and the incoming-protected native
frame. The selected token remains strong at g, while the entire
old leader prefix is unchanged. -/
theorem grantDrainMarksWholeRingBoundaryCoverage
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (p g : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hHost : label.host = some g)
    (hIncoming : ring.rightNeighbor g = p)
    (hNearest : GrantDrainMarksNearestArc ring s.native p g)
    (hZero : GrantDrainMarksZeroOffsetArc ring s.native p g)
    (hShield : (s.native p).sh = true)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s g label).host ≠
        none)
    (hStrong :
      (grantDrainLedgerStep ring freshRequest updateScratch s g label).mark =
        .strong) :
    GrantDrainMarksEdgeCoverAt ring freshRequest updateScratch
      s g label := by
  have hWhole := grantDrainMarksWholeRingBoundaryStrong
    hn ring freshRequest updateScratch s p g label
    hP hPhysical hHost hIncoming hNearest hZero hShield
  have hNativeFrame := grantDrainMarksIncomingProtectedFrame
    hn ring s g p g hIncoming hNearest hZero hShield
  have hFrame :
      ∀ k : Nat, k < PPL.cyclicOffset ring p g →
        ((grantDrainStep ring freshRequest updateScratch s g).native
          (PPL.shiftRight ring p k)).l =
          (s.native (PPL.shiftRight ring p k)).l := by
    intro k hk
    exact grantDrainMarksLeaderFrameOfNearest
      ring s.native (grantDrainNativeNext ring s g)
      p g hNearest hNativeFrame.1 k hk
  change
    GrantDrainStrongPhysical ring
      (grantDrainStep ring freshRequest updateScratch s g)
      (grantDrainLedgerStep ring freshRequest updateScratch s g label) ∧
    ∃ (q h : Fin n), label.host = some h ∧
      GrantDrainMarksNearestArc ring s.native q h ∧
      (((grantDrainLedgerStep ring freshRequest updateScratch s g label).host =
          some h ∧
        grantDrainLedgerNominatedHit ring s g label.host = false ∧
        (∀ k : Nat, k < PPL.cyclicOffset ring q h →
          ((grantDrainStep ring freshRequest updateScratch s g).native
            (PPL.shiftRight ring q k)).l =
          (s.native (PPL.shiftRight ring q k)).l)) ∨
      (∃ d : Nat,
        PPL.cyclicOffset ring q h = d ∧ 2 ≤ d ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s g label).host =
          some (PPL.shiftLeft ring h 1) ∧
        (∀ k : Nat, k < d - 1 →
          ((grantDrainStep ring freshRequest updateScratch s g).native
            (PPL.shiftRight ring q k)).l =
          (s.native (PPL.shiftRight ring q k)).l)) ∨
      (∃ j : Nat, 0 < j ∧ j < PPL.cyclicOffset ring q h ∧
        grantDrainLedgerNominatedHit ring s g label.host = false ∧
        (grantDrainLedgerStep ring freshRequest updateScratch s g label).host =
          some h ∧
        GrantDrainMarksNearestArc ring
          (grantDrainStep ring freshRequest updateScratch s g).native
          (PPL.shiftRight ring q j) h))
  exact ⟨hWhole.2.1, p, g, hHost, hNearest,
    Or.inl ⟨hWhole.2.2.1, hWhole.2.2.2.2.1, hFrame⟩⟩

/-- The source is p exactly when its clockwise offset is zero. -/
theorem grantDrainMarksSourceAtOffsetZero
    {n : Nat} (ring : DirectedRing n)
    (p e : Fin n)
    (hZero : PPL.cyclicOffset ring p e = 0) :
    e = p := by
  have hSite := grantDrainMarksArcShiftRightOffset ring p e
  rw [hZero, grantDrainMarksArcShiftRightZero] at hSite
  exact hSite.symm

/-- Equality of clockwise offsets from the same p uniquely
determines a physical site, including wraparound. -/
theorem grantDrainMarksEqualOffsetSite
    {n : Nat} (ring : DirectedRing n)
    (p e g : Fin n)
    (hEq : PPL.cyclicOffset ring p e =
      PPL.cyclicOffset ring p g) :
    e = g := by
  calc
    e = PPL.shiftRight ring p (PPL.cyclicOffset ring p e) :=
      (grantDrainMarksArcShiftRightOffset ring p e).symm
    _ = PPL.shiftRight ring p (PPL.cyclicOffset ring p g) := by
      rw [hEq]
    _ = g := grantDrainMarksArcShiftRightOffset ring p g

/-- At offset one the destination is the immediate ring
right-neighbor of p. -/
theorem grantDrainMarksHostAtOffsetOne
    {n : Nat} (ring : DirectedRing n)
    (p g : Fin n)
    (hOne : PPL.cyclicOffset ring p g = 1) :
    ring.rightNeighbor p = g := by
  have hg := grantDrainMarksArcShiftRightOffset ring p g
  rw [hOne] at hg
  have hStep : PPL.shiftRight ring p 1 = ring.rightNeighbor p := by
    apply Fin.ext
    rfl
  rw [hStep] at hg
  exact hg

/-- The successor site is the old host g exactly when the
successor clockwise offset agrees with that of g. -/
theorem grantDrainMarksNeighborIsHost
    {n : Nat} (ring : DirectedRing n)
    (p g e : Fin n)
    (hEq : PPL.cyclicOffset ring p e + 1 =
      PPL.cyclicOffset ring p g) :
    ring.rightNeighbor e = g := by
  rw [grantDrainMarksNeighborOfOffset ring p e, hEq]
  exact grantDrainMarksArcShiftRightOffset ring p g

/-- An edge at last offset n-1 has responder exactly p. -/
theorem grantDrainMarksNeighborWrapsToProtected
    {n : Nat} (ring : DirectedRing n)
    (p e : Fin n)
    (hLast : PPL.cyclicOffset ring p e = n - 1)
    (hn : 1 ≤ n) :
    ring.rightNeighbor e = p := by
  have hNext : PPL.cyclicOffset ring p e + 1 = n := by omega
  rw [grantDrainMarksNeighborOfOffset ring p e, hNext]
  exact grantDrainMarksFullRotation ring p

/-- Before wrapping, the successor's cyclic offset is exactly
one larger than the source's. -/
theorem grantDrainMarksNeighborOffsetAdvance
    {n : Nat} (ring : DirectedRing n)
    (p e : Fin n)
    (hBound : PPL.cyclicOffset ring p e + 1 < n) :
    PPL.cyclicOffset ring p (ring.rightNeighbor e) =
      PPL.cyclicOffset ring p e + 1 := by
  rw [grantDrainMarksNeighborOfOffset ring p e]
  exact grantDrainMarksArcOffsetShiftRight ring p
    (PPL.cyclicOffset ring p e + 1) hBound


/-- The seven exclusive cyclic positions are ALL the selected
source edge classes for a physical strong label, under n >= 3.
Every case is discharged by its own literal source-row/arc lemma.
In particular, the adjacent protected source consumes and retires
the OLD responder label, so a still-live strong continuation is
impossible there, rather than being silently omitted. -/
theorem grantDrainMarksAllEdgeCoverageOfThree
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (label : GrantDrainLedgerLabel n)
    (hP : PPlus ring s.native)
    (hPhysical : GrantDrainStrongPhysical ring s label)
    (hLive :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).host ≠
        none)
    (hStrong :
      (grantDrainLedgerStep ring freshRequest updateScratch s e label).mark =
        .strong) :
    GrantDrainMarksEdgeCoverAt ring freshRequest updateScratch
      s e label := by
  obtain ⟨g, hHost, hMark, hGrant, hRequest,
      hFollower, hLock⟩ := hPhysical
  have hOld : GrantDrainStrongPhysical ring s label :=
    ⟨g, hHost, hMark, hGrant, hRequest, hFollower, hLock⟩
  obtain ⟨p, hNearest, hZero, hShield⟩ :=
    grantDrainMarksStrongLockToOffsetArc_proved
      ring s g hP hFollower hLock
  obtain ⟨kind, hKind, _hUnique⟩ :=
    grantDrainMarksCyclicEdgePartition
      hn ring s.native p g e hNearest
  cases kind with
  | protectedAdjacent =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have he : e = p :=
        grantDrainMarksSourceAtOffsetZero ring p e hKind.1
      have hy : ring.rightNeighbor p = g :=
        grantDrainMarksHostAtOffsetOne ring p g hKind.2
      have hSunk := grantDrainMarksProtectedAdjacentHostRetired
        ring freshRequest updateScratch s p g label
        hy hHost hNearest.2.1 hFollower hGrant
      have hSunkAtE :
          (grantDrainLedgerStep ring freshRequest updateScratch s e label).host =
            none := by
        simpa [he] using hSunk
      exact False.elim (hLive hSunkAtE)
  | protectedLong =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have he : e = p :=
        grantDrainMarksSourceAtOffsetZero ring p e hKind.1
      have hResult :=
        grantDrainMarksProtectedSourceLongCoverage
          hn ring freshRequest updateScratch s p g label
          hNearest hZero hShield hKind.2
          hHost hMark hGrant hRequest hFollower
      rw [he]
      exact hResult
  | wholeBoundary =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hOffsetEq :
          PPL.cyclicOffset ring p e =
            PPL.cyclicOffset ring p g :=
        hKind.1.trans hKind.2.symm
      have he : e = g :=
        grantDrainMarksEqualOffsetSite ring p e g hOffsetEq
      have hIncomingOld :
          ring.rightNeighbor e = p :=
        grantDrainMarksNeighborWrapsToProtected
          ring p e hKind.1 (by omega)
      have hIncoming : ring.rightNeighbor g = p := by
        simpa [he] using hIncomingOld
      have hLiveG :
          (grantDrainLedgerStep ring freshRequest updateScratch s g label).host ≠
            none := by
        simpa [he] using hLive
      have hStrongG :
          (grantDrainLedgerStep ring freshRequest updateScratch s g label).mark =
            .strong := by
        simpa [he] using hStrong
      have hResult :=
        grantDrainMarksWholeRingBoundaryCoverage
          hn ring freshRequest updateScratch s
          p g label hP hOld hHost hIncoming
          hNearest hZero hShield hLiveG hStrongG
      simpa [he] using hResult
  | incomingHost =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hY : ring.rightNeighbor e = g :=
        grantDrainMarksNeighborIsHost
          ring p g e hKind.2
      have hOffsetBefore :
          PPL.cyclicOffset ring p e <
            PPL.cyclicOffset ring p g := by
        omega
      have hXFollow :
          (s.native e).l = false := by
        have hh := hNearest.2.2
          (PPL.cyclicOffset ring p e)
          hKind.1 hOffsetBefore
        rw [grantDrainMarksArcShiftRightOffset ring p e] at hh
        exact hh
      have hYFollow :
          (s.native (ring.rightNeighbor e)).l = false := by
        rw [hY]
        exact hFollower
      have hYHost :
          label.host = some (ring.rightNeighbor e) := by
        rw [hY]
        exact hHost
      exact grantDrainMarksIncomingFollowerHostCoverage
        hn ring freshRequest updateScratch s e label
        hP hXFollow hYFollow hYHost
        hOld hLive hStrong
  | strictInterior =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hYBound :
          PPL.cyclicOffset ring p e + 1 < n := by
        have hd := grantDrainMarksArcOffsetLt ring p g
        omega
      have hYOff :=
        grantDrainMarksNeighborOffsetAdvance ring p e hYBound
      have hInside :
          GrantDrainMarksStrictInteriorEdge ring p g e := by
        refine ⟨hKind.1, ?_, ?_, ?_⟩
        · omega
        · rw [hYOff]
          omega
        · rw [hYOff]
          exact hKind.2
      have hXFollow :
          (s.native e).l = false := by
        have hh := hNearest.2.2
          (PPL.cyclicOffset ring p e)
          hKind.1 hInside.2.1
        rw [grantDrainMarksArcShiftRightOffset ring p e] at hh
        exact hh
      have hYFollow :
          (s.native (ring.rightNeighbor e)).l = false := by
        have hh := hNearest.2.2
          (PPL.cyclicOffset ring p (ring.rightNeighbor e))
          hInside.2.2.1 hInside.2.2.2
        rw [grantDrainMarksArcShiftRightOffset
          ring p (ring.rightNeighbor e)] at hh
        exact hh
      have hXZero :
          (s.native e).sg = false := by
        have hh := hZero
          (PPL.cyclicOffset ring p e) hInside.2.1
        rw [grantDrainMarksArcShiftRightOffset ring p e] at hh
        exact hh
      have hYZero :
          (s.native (ring.rightNeighbor e)).sg = false := by
        have hh := hZero
          (PPL.cyclicOffset ring p (ring.rightNeighbor e))
          hInside.2.2.2
        rw [grantDrainMarksArcShiftRightOffset
          ring p (ring.rightNeighbor e)] at hh
        exact hh
      exact grantDrainMarksStrictInteriorFollowerPairCoverage
        hn ring freshRequest updateScratch s e label
        hP hOld p g hHost hNearest hInside
        hXFollow hYFollow hXZero hYZero hLive hStrong
  | incomingProtected =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hIncoming :
          ring.rightNeighbor e = p :=
        grantDrainMarksNeighborWrapsToProtected
          ring p e hKind.1 (by omega)
      have hNotHost : e ≠ g := by
        intro he
        have ho := congrArg (PPL.cyclicOffset ring p) he
        omega
      exact grantDrainMarksIncomingExteriorProtectedCoverage
        hn ring freshRequest updateScratch s e p g label
        hP hOld hHost hNearest hZero hShield
        hIncoming hNotHost hLive hStrong
  | exterior =>
      dsimp [GrantDrainMarksEdgeClassAt] at hKind
      have hYOff := grantDrainMarksNeighborOffsetAdvance
        ring p e hKind.2
      have hAway :
          ∀ k : Nat, k < PPL.cyclicOffset ring p g →
            PPL.shiftRight ring p k ≠ e ∧
              PPL.shiftRight ring p k ≠ ring.rightNeighbor e := by
        intro k hk
        have hklt : k < n :=
          Nat.lt_trans hk (grantDrainMarksArcOffsetLt ring p g)
        constructor
        · intro he
          have ho := congrArg (PPL.cyclicOffset ring p) he
          rw [grantDrainMarksArcOffsetShiftRight ring p k hklt] at ho
          omega
        · intro hy
          have ho := congrArg (PPL.cyclicOffset ring p) hy
          rw [grantDrainMarksArcOffsetShiftRight ring p k hklt,
            hYOff] at ho
          omega
      have hResponderNotHost : ring.rightNeighbor e ≠ g := by
        intro he
        have ho := congrArg (PPL.cyclicOffset ring p) he
        rw [hYOff] at ho
        omega
      exact grantDrainMarksExteriorPairCoverage
        hn ring freshRequest updateScratch
        s e p g label hP hOld hHost hNearest hZero hShield
        hAway hResponderNotHost hLive hStrong

/-- Global D.1 ArcCoverage for the exact source semantics on
rings with 3 <= n. The proof is the seven-class cyclic partition,
not a falsely general no-FIRE projection assertion. -/
theorem grantDrainMarksStrongArcCoverageOfThree
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainMarksStrongArcCoverage
      ring freshRequest updateScratch := by
  intro s e label hP hPhysical hLive hStrong
  exact (grantDrainMarksAllEdgeCoverageOfThree
    hn ring freshRequest updateScratch
    s e label hP hPhysical hLive hStrong).2

/-- Global D.1 StrongPhysicalClosure on the original grantDrainStep
for every surviving strong identity and any FIRE selector. -/
theorem grantDrainMarksStrongPhysicalClosureOfThree
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainMarksStrongPhysicalClosure
      ring freshRequest updateScratch := by
  intro s e label hP hPhysical hLive hStrong
  exact (grantDrainMarksAllEdgeCoverageOfThree
    hn ring freshRequest updateScratch
    s e label hP hPhysical hLive hStrong).1

end L3
