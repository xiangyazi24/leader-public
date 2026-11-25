import Leader.L4.TaggedTrace

namespace L4.TaggedTrace

open OpenQueue

private def priorWeight {n : Nat} (q : Option (Fin n × StockPair)) : Int :=
  (q.map (fun v => weight v.2)).getD 0

private def priorPenalty {n : Nat} (q : Option (Fin n × StockPair)) : Int :=
  if q.isSome then 5 else 0

/-- Account for a still-open episode with its actual current potential, so
closing it costs at most 5 and starting the next at 00 adds no current. -/
def QueueAccount {p c1 n : Nat} (s : Obs p c1 n) : Prop :=
  5 * (s.idealIngresses : Int) - s.current5 + priorWeight s.priorQueue ≤
    5 * (s.episodes : Int) - priorPenalty s.priorQueue

private theorem penaltyWeight_nonneg {n : Nat}
    (q : Option (Fin n × StockPair)) : 0 ≤ priorPenalty q + priorWeight q := by
  cases q with
  | none => change (0 : Int) ≤ 0; decide
  | some v =>
    change 0 ≤ 5 + weight v.2
    have := weight_ge_neg_five v.2
    omega

theorem QueueAccount.unweighted {p c1 n : Nat} {s : Obs p c1 n}
    (h : QueueAccount s) :
    5 * (s.idealIngresses : Int) ≤ s.current5 + 5 * (s.episodes : Int) := by
  have := penaltyWeight_nonneg s.priorQueue
  unfold QueueAccount at h
  omega

private theorem activeQueue_some_weight {p c1 n : Nat} (s : Obs p c1 n)
    (z : Fin n) (q : StockPair) (h : activeQueue s = some (z,q)) :
    weight q =
      if s.priorQueue.map Prod.fst = some z then priorWeight s.priorQueue else 0 := by
  unfold activeQueue at h
  cases hh : (leaderNow s).filter (TaggedFront.isLong s.config) with
  | none => simp [hh] at h
  | some v =>
    simp only [hh, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hq⟩ := h
    subst q
    cases hp : s.priorQueue with
    | none => rfl
    | some a =>
      rcases a with ⟨j,b⟩
      simp only [Option.map_some, Option.some.injEq, Option.getD_some, priorWeight]
      by_cases hj : j = v
      · rw [if_pos hj, if_pos hj]
      · rw [if_neg hj, if_neg hj]; rfl

theorem queueAccount_step {p c1 n : Nat} (s : Obs p c1 n) (e : Fin n)
    (h : QueueAccount s) : QueueAccount (advance s e) := by
  have hun := QueueAccount.unweighted h
  cases hc : s.carrier with
  | none => simpa [QueueAccount, advance, hc] using h
  | some i =>
    cases ha : activeQueue s with
    | none =>
      change QueueAccount (advance s e)
      simp [QueueAccount, advance, hc, ha, priorWeight, priorPenalty]
      omega
    | some v =>
      rcases v with ⟨z,q⟩
      have hw := activeQueue_some_weight s z q ha
      let b := barrierBond z e
      have hc' : scaledIncrement q b =
          5 * ((ingress q b).toNat : Int) + weight (idealStep q b) - weight q := by
        change 5 * ((ingress q b).toNat : Int) + (weight (idealStep q b) - weight q) = _
        omega
      have hrev : ((some z : Option (Fin n)) == s.priorQueue.map Prod.fst) = true ↔
          s.priorQueue.map Prod.fst = some z := by rw [beq_iff_eq, eq_comm]
      unfold QueueAccount at h ⊢
      simp only [advance, hc, ha, Option.map_some, Option.getD_some, Option.isSome_some,
        Bool.true_and, priorWeight, priorPenalty, if_true, Int.natCast_add]
      change 5 * ((s.idealIngresses : Int) + ↑(ingress q b).toNat) -
          (s.current5 + scaledIncrement q b) + weight (idealStep q b) ≤
        5 * ((s.episodes : Int) +
          ↑(!(some z == s.priorQueue.map Prod.fst)).toNat) - 5
      rw [hc']
      by_cases hh : s.priorQueue.map Prod.fst = some z
      · have hb : (some z == s.priorQueue.map Prod.fst) = true := hrev.mpr hh
        have hpen : priorPenalty s.priorQueue = 5 := by
          cases hp : s.priorQueue with
          | none => simp [hp] at hh
          | some a => rfl
        rw [if_pos hh] at hw
        simp only [hb, Bool.not_true, Bool.toNat_false, Int.natCast_zero, Int.add_zero]
        rw [hpen] at h
        omega
      · have hb : (some z == s.priorQueue.map Prod.fst) = false := by
          cases hbool : (some z == s.priorQueue.map Prod.fst)
          · rfl
          · exact False.elim (hh (hrev.mp hbool))
        rw [if_neg hh] at hw
        simp only [hb, Bool.not_false, Bool.toNat_true, Int.natCast_one]
        omega

theorem queueAccount_run {p c1 n : Nat} (s : Obs p c1 n) (w : List (Fin n))
    (h : QueueAccount s) : QueueAccount (track s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih => exact ih (advance s e) (queueAccount_step s e h)

/-- For the actual counted queue episodes, the raw-current debit bound is
unconditional. The separate paper obligation is episodes ≤ tenures. -/
theorem trace_queueCompensation {p c1 n : Nat} (x : Config p c1 n)
    (i : Fin n) (w : List (Fin n)) :
    let s := track (init x i) w
    5 * (s.idealIngresses : Int) ≤ s.current5 + 5 * (s.episodes : Int) := by
  have hinit : QueueAccount (init x i) := by
    change (0 : Int) ≤ 0
    decide
  exact QueueAccount.unweighted (queueAccount_run (init x i) w hinit)

end L4.TaggedTrace

#print axioms L4.TaggedTrace.trace_queueCompensation
