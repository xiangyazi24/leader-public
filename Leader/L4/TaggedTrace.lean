import Leader.L4.TaggedFront
import Leader.L4.TaggedRows

namespace L4.TaggedTrace

/-- The observer follows the actual resident/transport claims of the
literal row. Ending a tag never creates another. -/
def carrierStep {p c1 n : Nat} (x : Config p c1 n) (e : Fin n) :
    Option (Fin n) → Option (Fin n)
  | none => none
  | some i =>
    let j := rightNeighbor e
    if i = e then
      if tagTransfer (x e) (x j) then some j else none
    else if i = j then
      if tagResident (x e) (x j) then some i else none
    else some i

theorem carrierStep_selected_survives {p c1 n : Nat} (x : Config p c1 n)
    (e i : Fin n) (h : carrierStep x e (some e) = some i) :
    i = rightNeighbor e ∧ tagTransfer (x e) (x (rightNeighbor e)) = true := by
  by_cases ht : tagTransfer (x e) (x (rightNeighbor e)) = true
  · have hi : rightNeighbor e = i := by simpa [carrierStep, ht] using h
    exact ⟨hi.symm,ht⟩
  · simp [carrierStep, ht] at h

theorem carrierStep_not_selected_stays {p c1 n : Nat} (x : Config p c1 n)
    (e i j : Fin n) (hne : i ≠ e) (h : carrierStep x e (some i) = some j) :
    j = i := by
  simp only [carrierStep, if_neg hne] at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · contradiction
  · exact (Option.some.inj h).symm

/-- A proof-side tracked state. No metadata is stored in the physical
agents. Queue current and selected outgoing hits use scaled units of five. -/
structure Obs (p c1 n : Nat) where
  config : Config p c1 n
  carrier : Option (Fin n)
  priorLeader : Option (Fin n)
  priorQueue : Option (Fin n × OpenQueue.StockPair)
  moveCount : Nat
  outHits : Nat
  paidCount : Nat
  tenureCount : Nat
  episodes : Nat
  idealIngresses : Nat
  current5 : Int

def init {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) : Obs p c1 n :=
  ⟨x, if (x i).bullet == .live then some i else none, none, none, 0, 0, 0, 0, 0, 0, 0⟩

def ended {p c1 n : Nat} (s : Obs p c1 n) : Prop := s.carrier = none

def leaderNow {p c1 n : Nat} (s : Obs p c1 n) : Option (Fin n) :=
  s.carrier.bind (TaggedFront.firstLeader s.config)

def activeQueue {p c1 n : Nat} (s : Obs p c1 n) :
    Option (Fin n × OpenQueue.StockPair) :=
  ((leaderNow s).filter (TaggedFront.isLong s.config)).map fun z =>
    (z, if (s.priorQueue.map Prod.fst) = some z then
      (s.priorQueue.map Prod.snd).getD OpenQueue.empty else OpenQueue.empty)

/-- The event of a forward paid shift of the active first incoming mark.
No other mark-change row clears an old incoming marker. -/
def paidFirst {p c1 n : Nat} (x : Config p c1 n) (i e : Fin n) : Bool :=
  (TaggedFront.firstMarkedEdge x i == some e) &&
    (x e).mark && !(pairStep (x e) (x (rightNeighbor e))).1.mark

def advance {p c1 n : Nat} (s : Obs p c1 n) (e : Fin n) : Obs p c1 n :=
  let y := step s.config e
  match s.carrier with
  | none => { s with config := y }
  | some i =>
    let c := carrierStep s.config e (some i)
    let b := leaderNow s
    let aq := activeQueue s
    let m := aq.map fun (z,q) => (z, OpenQueue.idealStep q (barrierBond z e))
    let ingress := (aq.map fun (z,q) => OpenQueue.ingress q (barrierBond z e)).getD false
    let current := (aq.map fun (z,q) => OpenQueue.scaledIncrement q (barrierBond z e)).getD 0
    { config := y
      carrier := c
      priorLeader := b
      priorQueue := m
      moveCount := s.moveCount + ((i == e) && c.isSome).toNat
      outHits := s.outHits + (i == e).toNat
      paidCount := s.paidCount + (paidFirst s.config i e).toNat
      tenureCount := s.tenureCount + (b.isSome && b != s.priorLeader).toNat
      episodes := s.episodes + (aq.isSome && aq.map Prod.fst != s.priorQueue.map Prod.fst).toNat
      idealIngresses := s.idealIngresses + ingress.toNat
      current5 := s.current5 + current }

def track {p c1 n : Nat} (s : Obs p c1 n) : List (Fin n) → Obs p c1 n
  | [] => s
  | e :: w => track (advance s e) w

theorem projection_step {p c1 n : Nat} (s : Obs p c1 n) (e : Fin n) :
    (advance s e).config = step s.config e := by
  unfold advance
  split <;> rfl

theorem projection_run {p c1 n : Nat} (s : Obs p c1 n) (w : List (Fin n)) :
    (track s w).config = run s.config w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => simp only [track, run, ih, projection_step]

theorem ended_step {p c1 n : Nat} {s : Obs p c1 n} (h : ended s) (e : Fin n) :
    ended (advance s e) := by
  simp [ended, advance, show s.carrier = none from h]

theorem ended_run {p c1 n : Nat} (s : Obs p c1 n) (w : List (Fin n))
    (h : ended s) : ended (track s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih => exact ih (advance s e) (ended_step h e)

theorem hits_eq_moves_on_survival {p c1 n : Nat} (s : Obs p c1 n)
    (w : List (Fin n)) (h0 : s.outHits = s.moveCount)
    (h : ¬ ended (track s w)) : (track s w).outHits = (track s w).moveCount := by
  induction w generalizing s with
  | nil => exact h0
  | cons e w ih =>
    have hsurv : ¬ ended (advance s e) := fun ht => h (ended_run (advance s e) w ht)
    apply ih (advance s e) _ h
    cases he : s.carrier with
    | none => exact False.elim (hsurv (ended_step he e))
    | some i =>
      have hc : (carrierStep s.config e (some i)).isSome = true := by
        cases hh : carrierStep s.config e (some i)
        · exact False.elim (hsurv (by simp [ended, advance, he, hh]))
        · rfl
      simp [advance, he, h0, hc]

/-- Queue/tenure bookkeeping totals for the actual deterministic observer. -/
def totals {p c1 n : Nat} (s : Obs p c1 n) : BarrierLedger.Totals :=
  ⟨s.moveCount, s.paidCount, s.tenureCount, s.idealIngresses, s.current5⟩

def scaledDebt {p c1 n : Nat} (s : Obs p c1 n) : Int :=
  5 * (s.outHits : Int) - s.current5

/-- The final numerical claim for the literal surviving tagged trace.
This proposition is intentionally not a theorem until the trace budgets
have been closed. -/
def ConcreteBarrierDebt : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (w : List (Fin n)),
    2 ≤ p → 12 ≤ c1 → 4 ≤ n → ¬ p ∣ n → MCOV x → COV x →
      ¬ ended (track (init x i) w) →
      scaledDebt (track (init x i) w) < 120 * (n : Int)

/-- All choices are made from the pre-mark tracked state. The fallback
outgoing edge is irrelevant after extinction because the process stops. -/
def nominatedOut {p c1 n : Nat} (fallback : Fin n) (s : Obs p c1 n) : Fin n :=
  s.carrier.getD fallback

def nominatedQueue {p c1 n : Nat} (hn : 4 ≤ n) (s : Obs p c1 n) :
    Option (BarrierIID.QueueBonds n × OpenQueue.StockPair) :=
  (activeQueue s).map fun (z,q) => (barrierQueueBonds hn z,q)

theorem scaledDebt_step {p c1 n : Nat} (hn : 4 ≤ n) (fallback e : Fin n)
    (s : Obs p c1 n) (h : ¬ ended s) :
    scaledDebt (advance s e) =
      scaledDebt s + BarrierIID.driftMark (nominatedOut fallback s) (nominatedQueue hn s) e := by
  cases hc : s.carrier with
  | none => exact False.elim (h hc)
  | some i =>
    have hinc :
        ((activeQueue s).map (fun (z,q) =>
          OpenQueue.scaledIncrement q (barrierBond z e))).getD 0 =
        BarrierIID.queueMark (nominatedQueue hn s) e := by
      unfold nominatedQueue
      cases hq : activeQueue s with
      | none => rfl
      | some v => rcases v with ⟨z,q⟩; rfl
    simp only [scaledDebt, advance, hc, nominatedOut, Option.getD_some,
      BarrierIID.driftMark, hinc]
    by_cases he : e = i
    · subst e
      simp
      omega
    · have hb : (i == e) = false := by simpa using Ne.symm he
      simp only [if_neg he, hb, Bool.toNat_false, Nat.add_zero]
      omega

theorem track_append {p c1 n : Nat} (s : Obs p c1 n) (u v : List (Fin n)) :
    track s (u ++ v) = track (track s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (advance s e)

/-- Once the live debt proposition is discharged, the existing stopped-IID
bridge applies to the concrete trace, including the terminal mark. This is
a single-tag bound, not the all-tag maximum. -/
theorem concreteSingleTag_mean (hdebt : ConcreteBarrierDebt)
    {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (B : Nat)
    (hp : 2 ≤ p) (hc1 : 12 ≤ c1) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hm : MCOV x) (hc : COV x)
    (hB : (n : Int) * (120 * (n : Int) + 5) ≤ 3 * (B : Int)) :
    IIDExpectedHittingTimeAtMost advance ended (init x i) B := by
  let reached := fun s : Obs p c1 n => ∃ w : List (Fin n), track (init x i) w = s
  apply BarrierIID.singleTag_expected_of_live_debt (n := n) (by omega)
    advance ended (nominatedOut i) (nominatedQueue hn) reached scaledDebt (120 * (n : Int))
  · intro s e hs _
    obtain ⟨w, rfl⟩ := hs
    exact ⟨w ++ [e], by rw [track_append]; rfl⟩
  · intro s hs hl
    obtain ⟨w, rfl⟩ := hs
    exact Int.le_of_lt (hdebt x i w hp hc1 hn hnd hm hc hl)
  · intro s e _ hs
    exact scaledDebt_step hn i e s hs
  · exact ⟨[], rfl⟩
  · simpa [scaledDebt, init] using hB

end L4.TaggedTrace

