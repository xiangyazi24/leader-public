import Leader.L4.Height.LeaderBridge

namespace L4.Height

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- One fixed site outputs leader along every finite continuation,
including the empty scheduler word. -/
def permanentSiteOutput {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (out : α → Fin n → Bool) (x : α) : Prop :=
  ∃ winner : Fin n, ∀ (u : List (Fin n)) (j : Fin n),
    out (runWord next x u) j = decide (j = winner)

/-- A total decoder that commutes on single raw labels also commutes
along every finite scheduler word, from every raw starting state. -/
private theorem decoder_runWord
    {α β : Type} {n : Nat}
    (raw : α → Fin n → α)
    (ordinary : β → Fin n → β)
    (decode : α → β)
    (hStep : ∀ x e, decode (raw x e) =
      ordinary (decode x) e) :
    ∀ (x : α) (u : List (Fin n)),
      decode (runWord raw x u) =
        runWord ordinary (decode x) u := by
  intro x u
  induction u generalizing x with
  | nil =>
      rfl
  | cons e u ih =>
      change decode (runWord raw (raw x e) u) =
        runWord ordinary (ordinary (decode x) e) u
      rw [ih (raw x e), hStep x e]

/-- A fixed permanent winner in the decoded system is the same
permanent winner in the raw system. The witness is fixed before
quantifying over raw continuation words. -/
private theorem decoder_permanent_witness
    {α β : Type} {n : Nat}
    (raw : α → Fin n → α)
    (ordinary : β → Fin n → β)
    (decode : α → β)
    (rawOut : α → Fin n → Bool)
    (ordinaryOut : β → Fin n → Bool)
    (hStep : ∀ x e, decode (raw x e) =
      ordinary (decode x) e)
    (hRead : ∀ x j, rawOut x j =
      ordinaryOut (decode x) j)
    (x : α)
    (hx : permanentSiteOutput ordinary ordinaryOut (decode x)) :
    permanentSiteOutput raw rawOut x := by
  obtain ⟨winner, hwinner⟩ := hx
  refine ⟨winner, ?_⟩
  intro u j
  calc
    rawOut (runWord raw x u) j =
        ordinaryOut (decode (runWord raw x u)) j :=
      hRead (runWord raw x u) j
    _ = ordinaryOut (runWord ordinary (decode x) u) j := by
      rw [decoder_runWord raw ordinary decode hStep x u]
    _ = decide (j = winner) := hwinner u j

/-- Hitting the inverse image of an ordinary target has exactly the
same truncated IID numerator as hitting that target after decoding.
No injectivity or nonempty-alphabet premise is needed. -/
private theorem decoder_cost_commutes
    {α β : Type} {n : Nat}
    (raw : α → Fin n → α)
    (ordinary : β → Fin n → β)
    (decode : α → β)
    (hStep : ∀ x e, decode (raw x e) =
      ordinary (decode x) e)
    (E : β → Prop) :
    ∀ (t : Nat) (x : α),
      iidHitCost raw (fun z => E (decode z)) t x =
        iidHitCost ordinary E t (decode x) := by
  intro t
  induction t with
  | zero =>
      intro x
      rfl
  | succ t ih =>
      intro x
      by_cases hx : E (decode x)
      · simp [iidHitCost, hx]
      · have hsum :
            (List.ofFn (fun e : Fin n =>
              iidHitCost raw (fun z => E (decode z)) t (raw x e))).sum =
            (List.ofFn (fun e : Fin n =>
              iidHitCost ordinary E t
                (ordinary (decode x) e))).sum := by
          apply sum_ofFn_eq
          intro e
          rw [ih (raw x e), hStep x e]
        simp only [iidHitCost, hx, if_false]
        exact congrArg (fun v : Nat => n ^ (t + 1) + v) hsum

/-- Every total padded raw record inherits the bounded provider's
quadratic truncated hitting-cost estimate once both the raw transition
and the output commute with the ordinary decoder. -/
theorem bounded_decoder_permanent_cost
    {α β : Type} {n : Nat}
    (raw : α → Fin n → α)
    (ordinary : β → Fin n → β)
    (decode : α → β)
    (rawOut : α → Fin n → Bool)
    (ordinaryOut : β → Fin n → Bool)
    (hStep : ∀ x e, decode (raw x e) =
      ordinary (decode x) e)
    (hRead : ∀ x j, rawOut x j =
      ordinaryOut (decode x) j)
    (E : β → Prop)
    (hPermanent : ∀ y, E y →
      permanentSiteOutput ordinary ordinaryOut y)
    (C : Nat)
    (hExpected : ∀ y,
      IIDExpectedHittingTimeAtMost ordinary E y (C * n ^ 2)) :
    ∀ x, IIDExpectedHittingTimeAtMost raw
      (permanentSiteOutput raw rawOut) x (C * n ^ 2) := by
  have hTarget :
      ∀ z : α, E (decode z) →
        permanentSiteOutput raw rawOut z := by
    intro z hz
    exact decoder_permanent_witness
      raw ordinary decode rawOut ordinaryOut
      hStep hRead z (hPermanent (decode z) hz)
  intro x t
  calc
    iidHitCost raw (permanentSiteOutput raw rawOut) t x =
        costNumerator raw (permanentSiteOutput raw rawOut) x t :=
      iidHitCost_eq_costNumerator raw _ t x
    _ ≤ costNumerator raw (fun z => E (decode z)) x t :=
      L3.Prob.costNumerator_target_mono raw
        (fun z => E (decode z))
        (permanentSiteOutput raw rawOut) hTarget x t
    _ = iidHitCost raw (fun z => E (decode z)) t x :=
      (iidHitCost_eq_costNumerator raw _ t x).symm
    _ = iidHitCost ordinary E t (decode x) :=
      decoder_cost_commutes raw ordinary decode hStep E t x
    _ ≤ (C * n ^ 2) * n ^ t :=
      hExpected (decode x) t

end L4.Height

