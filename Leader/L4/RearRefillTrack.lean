import Leader.L4.RearRefill
import Leader.L4.RearFrontStock
import Leader.L4.RearPhaseBudget

/-! # Refills on the actual rear observer -/

namespace L4.RearTrace

open TaggedTrace

private theorem native_payer {p c : Nat} (u v : Site p c) :
    payer (native (materialize u v) v).1 = payer u := by
  have hm : payer (materialize u v) = payer u := by unfold materialize; split <;> rfl
  have hf (a : Site p c) : payer (fireInitiator a) = payer a := by
    unfold fireInitiator
    split <;> rfl
  have hi (a b : Site p c) : payer (impact a b).1 = payer a := by
    unfold impact
    split
    · split <;> rfl
    · rfl
  have hb (g : Bool) (a b : Site p c) : payer (followerBullet g a b).1 = payer a := by
    unfold followerBullet
    split <;> (try split) <;> rfl
  unfold native
  have h₂ := hi (fireInitiator (materialize u v)) (fireResponder v)
  generalize hh : impact (fireInitiator (materialize u v)) (fireResponder v) = xy at h₂ ⊢
  rcases xy with ⟨x,y⟩
  dsimp only
  have h₃ := hb (pinned x y) x y
  generalize hh' : followerBullet (pinned x y) x y = ab at h₃ ⊢
  rcases ab with ⟨a,b⟩
  change payer a = payer u
  exact h₃.trans (h₂.trans ((hf _).trans hm))

theorem geometricPay_ready {p c : Nat} (u v : Site p c)
    (h : geometricPay u v = true) : payer u = true := by
  simp only [geometricPay, Bool.and_eq_true] at h
  exact (native_payer u v).symm.trans h.2

private theorem successor_ne_self {n : Nat} (hn : 4 ≤ n) (e : Fin n) :
    rightNeighbor e ≠ e := by
  intro he
  have h := congrArg Fin.val he
  change (e.val+1)%n = e.val at h
  by_cases hh : e.val+1<n
  · rw [Nat.mod_eq_of_lt hh] at h; omega
  · have ht := e.isLt
    have hs : e.val+1=n := by omega
    rw [hs,Nat.mod_self] at h
    omega

/-- A real rear shift uses the nominated ready bond. -/
theorem rearShift_ready_nomination {p c n : Nat} (i e r : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hg : s.phase = .ghost) (hr : s.rear = some r) (hs : rearShifts s e r = true) :
    payer (s.tag.config (predecessor r)) = true ∧ e = rearBond i s := by
  obtain ⟨he,hp⟩ := (paid_moves_rear_iff hm i e r s rfl).1 hs
  have hp' := geometricPay_ready _ _ hp
  rw [he] at hp'
  have hh : (Phase.ghost == Phase.ghost) = true := rfl
  exact ⟨hp', by rw [he]; simp [rearBond,hg,hr,hp',hh]⟩

/-- The old empty rear site becomes an actually unready new donor on a
paid shift, including if it was killed before the payment. -/
theorem empty_shift_leaves_unready {p c n : Nat} (hn : 4 ≤ n)
    (i e r : Fin n) (s : Observer p c n) (hm : MCOV s.tag.config)
    (hs : rearShifts s e r = true) (hEmpty : (s.tag.config r).stock = false) :
    payer ((rearAdvance i s e).tag.config r) = false := by
  let x := s.tag.config
  obtain ⟨he,hp⟩ := (paid_moves_rear_iff hm i e r s rfl).1 hs
  have hright : rightNeighbor e = r := by rw [he,right_predecessor]
  have hne : r ≠ e := hright ▸ successor_ne_self hn e
  have hm' := paid_was_marked hm e hp
  have hstock := RearFrontStock.marked_right_stock (x e) (x (rightNeighbor e)) hm'
  have hlead := (pair_geometric_fields (x e) (x (rightNeighbor e))).2.2
  have hp' : geometricPay (x e) (x (rightNeighbor e)) = true := hp
  simp only [hp',if_true] at hlead
  rw [rearAdvance_tag,projection_step]
  have hstate : step x e r = (pairStep (x e) (x (rightNeighbor e))).2 := by
    simp [step,hne,hright]
  change payer (step x e r) = false
  rw [hstate]
  unfold payer
  rw [hstock, hlead.2, hright]
  change ((s.tag.config r).stock || false) = false
  rw [hEmpty]
  decide

/-- Exact proof-side clock event, with all increments classified by
the pre-mark physical state and with the pin advance omitted. -/
def clockEvent {p c n : Nat} (i : Fin n) (s : Observer p c n) (e : Fin n) : ClockEvent :=
  if s.phase = .ghost then
    match s.rear with
    | none => .idle
    | some r =>
      if rearShifts s e r = true ∧ (rearAdvance i s e).phase ≠ .pinned then
        if (s.tag.config r).stock then .filledAdvance else .emptyAdvance
      else if e = rearBond i s then
        if payer (s.tag.config (predecessor r)) then .hit else .refill
      else .idle
  else .idle

/-- Phase and actual rear-site projection on a marked ghost transition. -/
theorem ghost_step_rear {p c n : Nat} (i e r : Fin n)
    (s : Observer p c n) (hg : s.phase = .ghost) (hr : s.rear = some r) :
    let m := rearShifts s e r
    (rearAdvance i s e).rear = some (if m then rightNeighbor r else r) ∧
    (rearAdvance i s e).rearMoves = s.rearMoves + m.toNat := by
  have hb : (Phase.ghost == Phase.pinned) = false := rfl
  simp [rearAdvance,hg,hr,hb]

/-- A filled or empty counted advance has exactly one hit, and a
nonadvance hits only when the pre-mark nomination is selected. -/
def eventAdvances : ClockEvent → Nat
  | .filledAdvance | .emptyAdvance => 1
  | _ => 0

def eventFilled : ClockEvent → Nat
  | .filledAdvance => 1
  | _ => 0

def eventHits : ClockEvent → Nat
  | .idle => 0
  | _ => 1

/-- Pending payments only occur once the moving phase has begun; in that
phase a retained pending obligation witnesses a physically unready donor. -/
def PendingInvariant {p c n : Nat} (s : Observer p c n) (a : ClockAccount) : Prop :=
  a.pending = true → (s.phase ≠ .initial ∧ s.phase ≠ .initialLeader) ∧
    ∀ r, s.phase = .ghost → s.rear = some r → payer (s.tag.config (predecessor r)) = false

private theorem mature_phase_step {p c n : Nat} (s : Observer p c n) (i e : Fin n)
    (ht : s.phase ≠ .initial ∧ s.phase ≠ .initialLeader) :
    let t := (rearAdvance i s e).phase
    (t ≠ .initial ∧ t ≠ .initialLeader) ∧ (t = .ghost → s.phase = .ghost) := by
  cases hr : s.rear with
  | none => simp [rearAdvance,hr,ht]
  | some r =>
    unfold rearAdvance
    simp only [hr]
    unfold phaseAfter
    split
    · simp
    · cases h : s.phase
      · exact (ht.1 h).elim
      · exact (ht.2 h).elim
      · dsimp only
        split <;> split <;> simp
      · simp
      · simp

private theorem event_nocount {p c n : Nat} (i e r : Fin n) (s : Observer p c n)
    (hg : s.phase = .ghost) (hr : s.rear = some r)
    (hn : ¬ (rearShifts s e r = true ∧ (rearAdvance i s e).phase ≠ .pinned)) :
    clockEvent i s e =
      if e = rearBond i s then
        if payer (s.tag.config (predecessor r)) then .hit else .refill
      else .idle := by
  simp [clockEvent,hg,hr,hn]

private theorem event_count {p c n : Nat} (i e r : Fin n) (s : Observer p c n)
    (hg : s.phase = .ghost) (hr : s.rear = some r)
    (h : rearShifts s e r = true ∧ (rearAdvance i s e).phase ≠ .pinned) :
    clockEvent i s e = if (s.tag.config r).stock then .filledAdvance else .emptyAdvance := by
  simp [clockEvent,hg,hr,h]

/-- Each realized event is enabled by its account; the pending invariant
is preserved. No unready donor can make a counted advance, and the first
possible refill from an empty departure hits the nominated bond. -/
theorem clockEvent_valid_step {p c n : Nat} (hn : 4 ≤ n)
    (i e : Fin n) (s : Observer p c n) (a : ClockAccount)
    (hm : MCOV s.tag.config) (ha : PendingInvariant s a) :
    let ev := clockEvent i s e
    a.Allowed ev ∧ PendingInvariant (rearAdvance i s e) (a.update ev) := by
  dsimp only
  by_cases hg : s.phase = .ghost
  · cases hr : s.rear with
    | none =>
      simp only [clockEvent,hg,if_pos,hr,ClockAccount.Allowed,ClockAccount.update,true_and]
      intro h
      refine ⟨(mature_phase_step s i e (ha h).1).1, ?_⟩
      intro r _ hh
      simp [rearAdvance,hr] at hh
    | some r =>
      by_cases hs : rearShifts s e r = true ∧ (rearAdvance i s e).phase ≠ .pinned
      · have hready := (rearShift_ready_nomination i e r s hm hg hr hs.1).1
        have hp : a.pending = false := by
          by_cases hh : a.pending = true
          · have hf := (ha hh).2 r hg hr
            rw [hready] at hf
            contradiction
          · exact Bool.eq_false_iff.mpr hh
        rw [event_count i e r s hg hr hs]
        have hph := (mature_phase_step s i e (by rw [hg]; decide)).1
        cases hst : (s.tag.config r).stock
        · simp only [Bool.false_eq_true, if_false, ClockAccount.Allowed, hp,
            true_and, ClockAccount.update]
          intro _
          refine ⟨hph, ?_⟩
          intro q _ hq
          have hh := (ghost_step_rear i e r s hg hr).1
          rw [if_pos hs.1] at hh
          have heq : rightNeighbor r = q := Option.some.inj (hh.symm.trans hq)
          rw [← heq,predecessor_right]
          exact empty_shift_leaves_unready hn i e r s hm hs.1 hst
        · simp [ClockAccount.Allowed,hp, ClockAccount.update,PendingInvariant]
      · rw [event_nocount i e r s hg hr hs]
        have hph := (mature_phase_step s i e (by rw [hg]; decide)).1
        by_cases he : e = rearBond i s
        · cases hp : payer (s.tag.config (predecessor r))
          · simp [he,ClockAccount.Allowed,ClockAccount.update,PendingInvariant]
          · simp only [he,if_true,ClockAccount.Allowed,ClockAccount.update,true_and]
            intro h
            have hf := (ha h).2 r hg hr
            rw [hp] at hf
            contradiction
        · simp only [he,if_false,ClockAccount.Allowed,ClockAccount.update,true_and]
          intro h
          refine ⟨hph, ?_⟩
          intro q hq hrear
          have hun := (ha h).2 r hg hr
          have hsh : rearShifts s e r = false := by
            apply Bool.eq_false_iff.mpr
            intro htrue
            exact hs ⟨htrue, by rw [hq]; decide⟩
          have hpos := (ghost_step_rear i e r s hg hr).1
          rw [hsh] at hpos
          simp only [Bool.false_eq_true,if_false] at hpos
          have heq := Option.some.inj (hpos.symm.trans hrear)
          subst q
          rw [rearAdvance_tag,projection_step]
          apply unready_off_incoming _ _ _ _ hun
          intro hR
          have hh := congrArg predecessor hR
          rw [predecessor_right] at hh
          apply he
          have hb : (Phase.ghost == Phase.ghost) = true := rfl
          simpa [rearBond,hg,hr,hb,hun] using hh.symm
  · simp only [clockEvent,hg,if_false,ClockAccount.Allowed,ClockAccount.update,true_and]
    intro h
    have hh := mature_phase_step s i e (ha h).1
    exact ⟨hh.1, fun _ hz _ => (hg (hh.2 hz)).elim⟩

/-- The clock event counts precisely the same ghost advances as the
deterministic phase-budget ledger. -/
theorem clockEvent_advances_eq {p c n : Nat} (i e : Fin n) (s : Observer p c n) :
    eventAdvances (clockEvent i s e) = ghostAdvanceCount s (rearAdvance i s e) := by
  by_cases hg : s.phase = .ghost
  · cases hr : s.rear with
    | none => simp [clockEvent,ghostAdvanceCount,rearAdvance,eventAdvances,hg,hr]
    | some r =>
      have h := (ghost_step_rear i e r s hg hr).2
      by_cases hc : rearShifts s e r = true ∧ (rearAdvance i s e).phase ≠ .pinned
      · rw [event_count i e r s hg hr hc]
        cases hh : (s.tag.config r).stock <;>
          simp [eventAdvances,ghostAdvanceCount,hg,hc.2,h,hc.1]
      · rw [event_nocount i e r s hg hr hc]
        have hz : ghostAdvanceCount s (rearAdvance i s e) = 0 := by
          by_cases hp : (rearAdvance i s e).phase = .pinned
          · simp [ghostAdvanceCount,hg,hp]
          · have hf : rearShifts s e r = false :=
              Bool.eq_false_iff.mpr (fun hh => hc ⟨hh,hp⟩)
            simp [ghostAdvanceCount,hg,hp,h,hf]
        rw [hz]
        split
        · split <;> rfl
        · rfl
  · simp [clockEvent,ghostAdvanceCount,eventAdvances,hg]

/-- Every charged ghost event hits the exact pre-mark rear nomination. -/
theorem clockEvent_hits_le {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (hm : MCOV s.tag.config) :
    eventHits (clockEvent i s e) ≤ (e == rearBond i s).toNat := by
  by_cases hg : s.phase = .ghost
  · cases hr : s.rear with
    | none => simp [clockEvent,hg,hr,eventHits]
    | some r =>
      by_cases hc : rearShifts s e r = true ∧ (rearAdvance i s e).phase ≠ .pinned
      · have he := (rearShift_ready_nomination i e r s hm hg hr hc.1).2
        rw [event_count i e r s hg hr hc]
        cases hs : (s.tag.config r).stock <;> simp [eventHits,he]
      · rw [event_nocount i e r s hg hr hc]
        by_cases he : e = rearBond i s
        · cases hd : payer (s.tag.config (predecessor r)) <;> simp [eventHits,he]
        · simp [eventHits,he]
  · simp [clockEvent,hg,eventHits]

/-- Chronological events from the actual observer. No lookahead needed
except the deterministic bit saying whether this one selected mark pins. -/
def clockEvents {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → List ClockEvent
  | [] => []
  | e::w => clockEvent i s e :: clockEvents i (rearAdvance i s e) w

/-- Apply the verified refill account to the actual chronological trace. -/
def clockFold {p c n : Nat} (i : Fin n) (s : Observer p c n) (a : ClockAccount) :
    List (Fin n) → ClockAccount
  | [] => a
  | e::w => clockFold i (rearAdvance i s e) (a.update (clockEvent i s e)) w

/-- The original chronological refill matching is valid for the actual
observer on every covered finite word. Each successful refill clears at
most one pending advance, and a new counted advance requires no pending
one; this rule realizes the injective assignment of earlier obligations
to distinct selected marks. -/
theorem clockTrace_of_marks {p c n : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (a : ClockAccount) (w : List (Fin n))
    (hm : MCOV s.tag.config) (ha : PendingInvariant s a) :
    ClockTrace a (clockEvents i s w) (clockFold i s a w) := by
  induction w generalizing s a with
  | nil => exact .nil a
  | cons e w ih =>
    have ⟨hallow,hinv⟩ := clockEvent_valid_step hn i e s a hm ha
    have hcov : MCOV (rearAdvance i s e).tag.config := by
      rw [rearAdvance_tag,projection_step]
      exact mcov_step hn s.tag.config hm e
    exact .cons hallow (ih _ _ hcov hinv)

theorem clockFold_metrics {p c n : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (a : ClockAccount) (w : List (Fin n))
    (hm : MCOV s.tag.config) :
    let b := clockFold i s a w
    b.advances = a.advances + ghostAdvances i s w ∧
    b.filled = a.filled + ((clockEvents i s w).map eventFilled).sum ∧
    b.hits+s.rearHits ≤ a.hits+(rearFold i s w).rearHits := by
  induction w generalizing s a with
  | nil => simp [clockFold,clockEvents,ghostAdvances,rearFold]
  | cons e w ih =>
    let ev := clockEvent i s e
    let t := rearAdvance i s e
    have hcov : MCOV t.tag.config := by
      dsimp [t]; rw [rearAdvance_tag,projection_step]
      exact mcov_step hn s.tag.config hm e
    have ⟨hnA,hnF,hnH⟩ := ih t (a.update ev) hcov
    have h₁ : (a.update ev).advances = a.advances + eventAdvances ev := by
      cases ev <;> simp [ClockAccount.update,eventAdvances]
    have h₂ : (a.update ev).filled = a.filled + eventFilled ev := by
      cases ev <;> simp [ClockAccount.update,eventFilled]
    have h₃ : (a.update ev).hits = a.hits + eventHits ev := by
      cases ev <;> simp [ClockAccount.update,eventHits]
    have hA : eventAdvances ev = ghostAdvanceCount s t := clockEvent_advances_eq i e s
    have hH : eventHits ev ≤ (e == rearBond i s).toNat := clockEvent_hits_le i e s hm
    have hR : t.rearHits = s.rearHits+(e == rearBond i s).toNat := rearAdvance_hits i s e
    change (clockFold i t (a.update ev) w).advances =
       a.advances + (ghostAdvanceCount s t+ghostAdvances i t w) ∧
      (clockFold i t (a.update ev) w).filled =
       a.filled + (eventFilled ev+((clockEvents i t w).map eventFilled).sum) ∧
      (clockFold i t (a.update ev) w).hits+s.rearHits ≤ a.hits+(rearFold i t w).rearHits
    constructor
    · omega
    constructor <;> omega

/-- Refill inequality on a concrete trace, ready for the filled-
departure and occupied-landing budget. -/
theorem concrete_refill_bound {p c n : Nat} (hn : 4 ≤ n)
    (i : Fin n) (s : Observer p c n) (w : List (Fin n))
    (hm : MCOV s.tag.config) :
    2*ghostAdvances i s w ≤ (rearFold i s w).rearHits +
      ((clockEvents i s w).map eventFilled).sum + 1 := by
  have hPend : PendingInvariant s ClockAccount.zero := by
    intro h
    change false = true at h
    contradiction
  have h := count_refills (clockTrace_of_marks hn i s ClockAccount.zero w hm hPend)
  have ⟨ha,hf,hh⟩ := clockFold_metrics hn i s ClockAccount.zero w hm
  let bb := clockFold i s ClockAccount.zero w
  change 2*bb.advances ≤ bb.hits+bb.filled+1 at h
  change bb.advances = 0+ghostAdvances i s w at ha
  change bb.filled = 0+((clockEvents i s w).map eventFilled).sum at hf
  change bb.hits+s.rearHits ≤ 0+(rearFold i s w).rearHits at hh
  omega

end L4.RearTrace

